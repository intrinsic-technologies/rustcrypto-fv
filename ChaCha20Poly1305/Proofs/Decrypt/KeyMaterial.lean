import ChaCha20Poly1305.Proofs.Decrypt.HashBytes
import ChaCha20Poly1305.Proofs.Decrypt.RFCStream

namespace ChaCha20Poly1305.Proofs.Decrypt.Detached
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.Refine
open Standards.RFC.ChaCha20Poly1305

def word {n : Nat} (v : Vector UInt8 n) (i : Nat) :=
  littleEndianWord v[4*i]! v[4*i+1]! v[4*i+2]! v[4*i+3]!

def pair {n : Nat} (v : Vector UInt8 n) (i : Nat) : BitVec 64 :=
  (word v (2*i+1)).toBitVec ++ (word v (2*i)).toBitVec

def keyQuads (key : Vector UInt8 32) : Vector (BitVec 64) 4 := Vector.ofFn (fun i => pair key i)

private theorem reorder (a b c d : BitVec 32) : a ||| b ||| c ||| d = d ||| c ||| b ||| a := by
  apply BitVec.eq_of_getLsbD_eq; intro i _
  simp only [BitVec.getLsbD_or,Bool.or_left_comm,Bool.or_comm]

theorem le4 (a b c d : UInt8) : (littleEndianWord a b c d).toBitVec =
    d.toBitVec ++ c.toBitVec ++ b.toBitVec ++ a.toBitVec := by
  have e := BitVec.setWidth_append_append_append_eq_shiftLeft_setWidth_or (w'''' := 32)
    (b:=d.toBitVec) (b':=c.toBitVec) (b'':=b.toBitVec) (b''':=a.toBitVec)
  rw [BitVec.setWidth_eq] at e
  rw [e]
  change (((a.toBitVec.setWidth 32 ||| b.toBitVec.setWidth 32 <<< 8) ||| c.toBitVec.setWidth 32 <<< 16) |||
    d.toBitVec.setWidth 32 <<< 24) = _
  exact reorder _ _ _ _

def BytesAtVec {n : Nat} (m : Ram) (p : BitVec 64) (v : Vector UInt8 n) :=
  ∀ i (hi : i<n), memLoad m (p+BitVec.ofNat 64 i) 8=v[i].toBitVec

theorem bytesOfRegion {n : Nat} {m : Ram} {p : BitVec 64} {v : Vector UInt8 n}
    (h : (MemoryRegion.mk p.toNat n).HasBytes m (v : ByteArray)) : BytesAtVec m p v := by
  intro i hi
  have hi' : i < (v : ByteArray).size := by rw [show (v : ByteArray).size=n from v.size_toArray]; exact hi
  have hb := h.2 ⟨i,hi'⟩
  change m[BitVec.ofNat 64 (p.toNat+i)]? = some _ at hb
  rw [BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq] at hb
  rw [memLoad_8]
  change (m[p+BitVec.ofNat 64 i]?.getD 0).toBitVec = _
  rw [hb]; rfl

theorem wordAt {n : Nat} {m : Ram} {p : BitVec 64} {v : Vector UInt8 n} (h : BytesAtVec m p v) (i : Nat)
    (hi : 4*i+4≤n) : memLoad m (p+BitVec.ofNat 64 (4*i)) 32 = (word v i).toBitVec := by
  let a := p+BitVec.ofNat 64 (4*i)
  have get (j : Nat) (hj : j<4) : memLoad m (a+BitVec.ofNat 64 j) 8 = (v[4*i+j]!).toBitVec := by
    rw [getElem!_pos v _ (by omega),←h]
    simp only [a,BitVec.add_assoc,BitVec.ofNat_add]
  have read (q : BitVec 64) : memLoad m q 32 =
      memLoad m (q+3) 8 ++ memLoad m (q+2) 8 ++ memLoad m (q+1) 8 ++ memLoad m q 8 := by
    rw [Hash.loadJoin 1 3,Hash.loadJoin 1 2,Hash.loadJoin 1 1]
    simp +decide [BitVec.add_assoc]
  change memLoad m a 32 = _
  rw [word,le4,read]
  have e3 : memLoad m (a+3) 8=(v[4*i+3]!).toBitVec := get 3 (by decide)
  have e2 : memLoad m (a+2) 8=(v[4*i+2]!).toBitVec := get 2 (by decide)
  have e1 : memLoad m (a+1) 8=(v[4*i+1]!).toBitVec := get 1 (by decide)
  rw [e3,e2,e1]
  congr 1
  simpa only [BitVec.add_zero,Nat.add_zero] using get 0 (by decide)

theorem pairAt {n : Nat} {m : Ram} {p : BitVec 64} {v : Vector UInt8 n} (h : BytesAtVec m p v) (i : Nat)
    (hi : 8*i+8≤n) : memLoad m (p+BitVec.ofNat 64 (8*i)) 64 = pair v i := by
  rw [Hash.loadJoin 4 4,pair,←wordAt h (2*i+1) (by omega),←wordAt h (2*i) (by omega)]
  simp only [BitVec.add_assoc,←BitVec.ofNat_add]
  rw [show 4*(2*i+1)=8*i+4 by omega,show 4*(2*i)=8*i by omega]

end ChaCha20Poly1305.Proofs.Decrypt.Detached
