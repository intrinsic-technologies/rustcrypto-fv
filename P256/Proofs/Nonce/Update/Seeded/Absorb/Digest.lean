import P256.Proofs.Nonce.Update.Seeded.Absorb.Compress
import P256.Proofs.Nonce.Update.Absorb.HmacAppend

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Seeded.Absorb

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open Update.Absorb

structure Digest [Bindings] (initial s : RamState) (state : State) (input secret : ByteArray) : Prop extends
    Context initial s state where
  current : s.regValue .rbp = initial.regValue .rsi
  hashPointer : s.regValue .r14 = scratch initial + 384
  copyPointer : s.regValue .r13 = 0x11c930
  outer : (MemoryRegion.mk (scratch initial + 256).toNat 64).HasBytes s.external (HMAC.keyPad state.key 0x5c)
  hash : SHA256.HashStateAt s (scratch initial + 384)
    (P256.Proofs.SHA256.Reference.compress
      (SHA256.compressBlocks P256.Proofs.SHA256.initialHash (HMAC.keyPad state.key 0x36 ++ input))
      (Standards.NIST.SHA2.bytesToBits (input ++ secret.extract 0 31)))
  count : loadBytes s.external (scratch initial + 416) 8 = .ok (2 : BitVec 64)

structure RemainderReady [Bindings] (initial s : RamState) (state : State) (input secret : ByteArray)
    (address : BitVec 64) : Prop extends Digest initial s state input secret where
  rip : s.RIP = 0x10a827
  source : s.regValue .rsi = address + 31
  destination : s.regValue .rdi = scratch initial + 320
  countRegister : s.regValue .rdx = 1
  position : s.external[scratch initial + 383]? = some 1

theorem Compressed.toDigest [Bindings] {initial s : RamState} {state : State}
    {input secret : ByteArray} {address : BitVec 64} (compressed : Compressed initial s state input secret address) :
    Digest initial s state input secret :=
  ⟨compressed.toContext,compressed.current,compressed.hashPointer,compressed.copyPointer,compressed.outer,compressed.hash,compressed.count⟩

theorem Digest.after [Bindings] {initial s t : RamState} {state : State} {input secret : ByteArray}
    (digest : Digest initial s state input secret) (ctx : Context initial t state)
    (current : t.regValue .rbp = s.regValue .rbp)
    (hashPointer : t.regValue .r14 = s.regValue .r14)
    (copyPointer : t.regValue .r13 = s.regValue .r13)
    (outer : ∀ i < 64, t.external[scratch initial + 256 + BitVec.ofNat 64 i]? =
      s.external[scratch initial + 256 + BitVec.ofNat 64 i]?)
    (hashCount : ∀ i < 40, t.external[scratch initial + 384 + BitVec.ofNat 64 i]? =
      s.external[scratch initial + 384 + BitVec.ofNat 64 i]?) : Digest initial t state input secret := by
  refine ⟨ctx,current.trans digest.current,hashPointer.trans digest.hashPointer,copyPointer.trans digest.copyPointer,P256.Proofs.Program.hasBytes_copy digest.outer outer,
    SHA256.HashStateAt.copy digest.hash (fun i hi => hashCount i (by omega)),?_⟩
  apply P256.Proofs.Program.loadBytes_ok_copy _ digest.count
  intro i hi
  have h := hashCount (32+i) (by omega)
  rw [show scratch initial + 384 + BitVec.ofNat 64 (32+i) = scratch initial + 416 + BitVec.ofNat 64 i by bv_omega] at h
  exact h

theorem Digest.after_position [Bindings] {initial s t : RamState} {state : State}
    {input secret : ByteArray} {components : List Component}
    (digest : Digest initial s state input secret) (ctx : Context initial t state)
    (agrees : AgreesExcept components s t) (current : .reg 5 ∉ components)
    (hashPointer : .reg 14 ∉ components) (copyPointer : .reg 13 ∉ components)
    (writes : ∀ c ∈ components, ∀ a, c.Covers a →
      (.mem (scratch initial + 383) 1 : Component).Covers a) : Digest initial t state input secret := by
  apply digest.after ctx (agrees.read (n:=64) (r:=5) current)
    (agrees.read (n:=64) (r:=14) hashPointer) (agrees.read (n:=64) (r:=13) copyPointer)
  · intro i hi
    apply agrees.byte
    intro c hc cover
    obtain ⟨j,hj,eq⟩ := writes c hc _ cover
    bv_omega
  · intro i hi
    apply agrees.byte
    intro c hc cover
    obtain ⟨j,hj,eq⟩ := writes c hc _ cover
    bv_omega

theorem Digest.step_position [Bindings] {initial s t : RamState} {original state : State}
    {input secret : ByteArray} {boundary : ReturnBoundary} {components : List Component}
    (pre : DrbgCalleePre initial boundary 0x109f30 1856 original)
    (digest : Digest initial s state input secret) (ready : ReadyToStep t)
    (agrees : AgreesExcept components s t) (rsp : .reg 4 ∉ components)
    (buffer : .reg 12 ∉ components) (current : .reg 5 ∉ components)
    (hashPointer : .reg 14 ∉ components) (copyPointer : .reg 13 ∉ components)
    (writes : ∀ c ∈ components, ∀ a, c.Covers a →
      (.mem (scratch initial + 383) 1 : Component).Covers a)
    (hdf : Component.df ∉ components := by component_not_mem)
    (hmxcsr : Component.mxcsr ∉ components := by component_not_mem)
    (hfcw : Component.fcw ∉ components := by component_not_mem) : Digest initial t state input secret := by
  apply digest.after_position _ agrees current hashPointer copyPointer writes
  apply digest.toContext.after_inner pre ready agrees rsp buffer
  intro c hc a cover
  obtain ⟨i,hi,rfl⟩ := writes c hc a cover
  refine ⟨63+i,by omega,?_⟩
  bv_omega

theorem Digest.hmac [Bindings] {initial s : RamState} {state : State} {input secret : ByteArray}
    (digest : Digest initial s state input secret)
    (inputSize : input.size = 33) (secretSize : secret.size = 32)
    (buffer : (MemoryRegion.mk (scratch initial + 320).toNat 1).HasBytes s.external (secret.extract 31 32))
    (position : s.external[scratch initial + 383]? = some 1) :
    HMAC.HmacStateAt s (scratch initial + 256) state.key (input ++ secret) := by
  refine ⟨digest.outer,?_⟩
  apply HMAC.sha256StateAt_keyPad_append
  · rw [remainderBytes_append_crossing input secret (by omega) (by omega) (by omega)]
    simpa only [ByteArray.size_append,inputSize,secretSize,Nat.reduceAdd,Nat.reduceSub,Nat.reduceMod,show UInt8.ofNat 1 = (1 : UInt8) from rfl,
      BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd] using buffer
  · simpa only [ByteArray.size_append,inputSize,secretSize,Nat.reduceAdd,Nat.reduceMod,show UInt8.ofNat 1 = (1 : UInt8) from rfl,
      BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd] using position
  · rw [compressBlocks_append_crossing _ input secret (by omega) (by omega) (by omega)]
    have h := digest.hash
    rw [HMAC.compressBlocks_keyPad_append,HMAC.compressBlocks_short _ input (by omega)] at h
    simpa only [inputSize,secretSize,Nat.reduceSub,BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd] using h
  · simpa only [ByteArray.size_append,inputSize,secretSize,Nat.reduceAdd,Nat.reduceDiv,
      BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd] using digest.count

end P256.Proofs.Nonce.Update.Seeded.Absorb
