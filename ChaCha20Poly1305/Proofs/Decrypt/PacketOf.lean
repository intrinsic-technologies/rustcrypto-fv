import ChaCha20Poly1305.Proofs.Decrypt.DetachBase
import ChaCha20Poly1305.Proofs.Decrypt.PrefixInitial
import ChaCha20Poly1305.Proofs.Decrypt.Output

namespace ChaCha20Poly1305.Proofs.Decrypt.Wrapper
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program
open ChaCha20Poly1305.Spec ChaCha20Poly1305.Spec.Program
open Hash Detached Poly1305 Standards.RFC.ChaCha20Poly1305

set_option maxHeartbeats 800000
set_option maxRecDepth 7500
attribute [local irreducible] poly1305Mac chacha20Encrypt poly1305KeyGen

def trimmed (msg : ByteArray) := msg.extract 0 (msg.size-16)
theorem trimmedSize (msg : ByteArray) : (trimmed msg).size=msg.size-16 := by simp [trimmed,ByteArray.size_extract]
def lastTag (msg : ByteArray) (h : 16≤msg.size) : Vector UInt8 16 :=
  Vector.ofFn fun i => msg[msg.size-16+i.val]'(by omega)

def packet (key : Vector UInt8 32) (nonce : Vector UInt8 12) (aad msg : ByteArray) (pa heap : BitVec 64)
    (h : 16≤msg.size) (small : msg.size<2^32) : Packet where
  key := key
  nonce := nonce
  aad := aad
  ct := trimmed msg
  tag := tagBits (lastTag msg h)
  pa := if aad.size=0 then 0 else pa
  buf := heap
  n := BitVec.ofNat 64 (msg.size-16)
  length := by rw [trimmedSize,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  small := by rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]; omega

theorem decryptPacket {key nonce aad msg pa heap h small}
:
    AEAD.decryptWithTag aad key nonce msg = if (packet key nonce aad msg pa heap h small).good then some (packet key nonce aad msg pa heap h small).plain else none := by
  rw [AEAD.decryptWithTag,dite_eq_left h]
  unfold chacha20AeadDecrypt
  change (if poly1305Mac (aeadMacData aad (trimmed msg)) (poly1305KeyGen key nonce)=lastTag msg h then _ else _) = _
  simp only [Packet.good,Packet.computed,Packet.one,packet,tagInj,decide_eq_true_eq,Packet.plain]
  rfl

private theorem vecDecode {n} (v : Vector UInt8 n) : toArray? (v : ByteArray) n=some v := by
  cases v with | mk a h => simp [toArray?,h]

theorem needsPacket {key : Vector UInt8 32} {nonce : Vector UInt8 12} {aad msg pa heap h small} :
    decrypt.needsOutput [key,nonce,aad,msg] = (packet key nonce aad msg pa heap h small).good := by
  change (tagAccepted [key,nonce,aad,msg] || false)=_
  rw [Bool.or_false,tagAccepted,vecDecode,vecDecode]
  change (AEAD.decryptWithTag aad key nonce msg).isSome=_
  rw [decryptPacket (pa:=pa) (heap:=heap) (h:=h) (small:=small)]
  split <;> simp_all

theorem keyMatch {s : RamState} {key : Vector UInt8 32} (h : ValidInput s (registerRegion s .rdi 32) (key : ByteArray)) :
    Prefix.initialKey s=keyQuads key := by
  apply Vector.ext
  intro i hi
  simp only [Prefix.initialKey,keyQuads,Vector.getElem_ofFn]
  exact pairAt (bytesOfRegion h.2) i (by omega)

theorem lastBytes (msg : ByteArray) (h : 16≤msg.size) : (lastTag msg h : ByteArray)=msg.extract (msg.size-16) msg.size := by
  apply ByteArray.ext
  apply Array.ext
  · change (lastTag msg h).toArray.size=(msg.extract _ _).size
    rw [Vector.size_toArray,ByteArray.size_extract]; omega
  · intro i hi hj
    change (lastTag msg h).toArray[i]=(msg.extract (msg.size-16) msg.size)[i]'(hj)
    simp only [lastTag,Vector.toArray_ofFn,Array.getElem_ofFn,ByteArray.getElem_extract]

theorem splitData (msg : ByteArray) (h : 16≤msg.size) (m : Ram) (buf n : BitVec 64)
    (len : n.toNat=msg.size-16) (raw : memLoad m buf (8*msg.size)=Bytes.packed msg) :
    let t := tagBits (lastTag msg h)
    memLoad m buf (8*n.toNat)=Stream.encode (trimmed msg) n.toNat ∧
    memLoad m (buf+n) 64=t.extractLsb' 0 64 ∧ memLoad m (buf+n+8) 64=t.extractLsb' 64 64 := by
  let k := msg.size-16
  have sum : k+16=msg.size := by dsimp [k]; omega
  have nv : BitVec.ofNat 64 k=n := by rw [show k=n.toNat from len.symm,BitVec.ofNat_toNat,BitVec.setWidth_eq]
  have part := loadPart (m:=m) (p:=buf) (w:=8*msg.size) k 16 (by omega)
  rw [raw,nv] at part
  have eq : memLoad m (buf+n) 128=tagBits (lastTag msg h) := by
    apply BitVec.eq_of_toNat_eq
    rw [←part,Bytes.slice msg k 16 (by omega),sum,tagBits,lastBytes,BitVec.toNat_ofNat,Nat.mod_eq_of_lt]
    have bound := le_bound (msg.extract k msg.size)
    rw [ByteArray.size_extract,Nat.min_self,show msg.size-k=16 by omega] at bound
    exact bound
  have l := loadPart (m:=m) (p:=buf+n) (w:=128) 0 8 (by decide)
  have r := loadPart (m:=m) (p:=buf+n) (w:=128) 8 8 (by decide)
  rw [eq,show buf+n+BitVec.ofNat 64 0=buf+n from BitVec.add_zero _] at l
  rw [eq] at r
  refine ⟨?_,l.symm,r.symm⟩
  have v := loadPart (m:=m) (p:=buf) (w:=8*msg.size) 0 k (by omega)
  rw [raw,show buf+BitVec.ofNat 64 0=buf from BitVec.add_zero _] at v
  apply BitVec.eq_of_toNat_eq
  simp only [Stream.encode,BitVec.toNat_setWidth,Bytes.packedNat]
  have b := le_bound (trimmed msg)
  rw [trimmedSize,←Bytes.pow_bytes] at b
  rw [len,←v,Bytes.slice msg 0 k (by omega),Nat.zero_add,Nat.mod_eq_of_lt b]
  rfl

theorem bytesFromPacked {m : Ram} {p : BitVec 64} {s : ByteArray} (rd : Readable m p s.size)
    (eq : memLoad m p (8*s.size)=Bytes.packed s) : (MemoryRegion.mk p.toNat s.size).HasBytes m s := by
  refine ⟨rfl,?_⟩
  intro i
  have read := rd.present i.val i.isLt
  obtain ⟨v,hv⟩ := Option.isSome_iff_exists.mp read
  change m[BitVec.ofNat 64 (p.toNat+i.val)]?=some _
  rw [BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq,hv]
  have load := loadPart (m:=m) (p:=p) (w:=8*s.size) i.val 1 (by have := i.isLt; omega)
  rw [eq,Bytes.byte s i.isLt] at load
  change _=memLoad m (p+BitVec.ofNat 64 i.val) 8 at load
  rw [memLoad_8] at load
  change _=(m[p+BitVec.ofNat 64 i.val]?.getD 0).toBitVec at load
  rw [hv] at load
  exact congrArg some (UInt8.toBitVec_inj.mp load.symm)

end ChaCha20Poly1305.Proofs.Decrypt.Wrapper
