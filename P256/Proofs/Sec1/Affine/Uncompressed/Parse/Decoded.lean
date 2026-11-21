import P256.Proofs.Sec1.Affine.Uncompressed.Parse.Execution
import P256.Proofs.SecretKeyFromBytes.Scalar.Representation

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Uncompressed.Parse

open P256.Spec P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Standards.SECG.ECC.Encoding
open P256.Proofs.Common.Instructions (bswap64)

theorem load_value (y : Bool) {s t u : RamState} {bytes : ByteArray}
    (size : bytes.size = 65) (input : EncodedPointAt t (s.regValue .rsi) bytes)
    (source : (if y then t.regValue .rsi else t.regValue .rbp) = s.regValue .rsi)
    (effect : (loadEffect y t).Holds t u) :
    let value := octetsToNat (bytes.extract (if y then 33 else 1) (if y then 65 else 33))
    u.regValue .rax = BitVec.ofNat 64 (value / 2^192) ∧
    u.regValue .rcx = BitVec.ofNat 64 (value / 2^128) ∧
    (Operand.reg (if y then 7 else 6) : Operand 64).read u =
      BitVec.ofNat 64 (value / 2^64) ∧
    u.regValue .rdx = BitVec.ofNat 64 value := by
  let off : Nat := if y then 33 else 1
  have decoded (j : Nat) (hj : j < 4) := coordinate_limb size input off
    (by cases y <;> decide) j hj
  have h0 : u.regValue .rax = bswap64 (memLoad t.external
      ((if y then t.regValue .rsi else t.regValue .rbp) + BitVec.ofNat 64 off) 64) := by
    cases y <;> exact effect.writes.1
  have h1 : u.regValue .rcx = bswap64 (memLoad t.external
      ((if y then t.regValue .rsi else t.regValue .rbp) + BitVec.ofNat 64 (off+8)) 64) := by
    cases y <;> exact effect.writes.2.1
  have h2 : (Operand.reg (if y then 7 else 6) : Operand 64).read u =
      bswap64 (memLoad t.external
        ((if y then t.regValue .rsi else t.regValue .rbp) + BitVec.ofNat 64 (off+16)) 64) := by
    cases y <;> exact effect.writes.2.2.1
  have h3 : u.regValue .rdx = bswap64 (memLoad t.external
      ((if y then t.regValue .rsi else t.regValue .rbp) + BitVec.ofNat 64 (off+24)) 64) := by
    cases y <;> exact effect.writes.2.2.2
  rw [source] at h0 h1 h2 h3
  refine ⟨h0.trans ?_, h1.trans ?_, h2.trans ?_, h3.trans ?_⟩
  · cases y <;> simpa [off] using decoded 0 (by decide)
  · cases y <;> simpa [off] using decoded 1 (by decide)
  · cases y <;> simpa [off] using decoded 2 (by decide)
  · cases y <;> simpa [off] using decoded 3 (by decide)

def decodeComponents (y : Bool) (t : RamState) : List Component :=
  [.reg 0, .reg 1, .reg (if y then 7 else 6), .reg 2, .rip] ++ storeComponents t

theorem decode_correct [Bindings] (y : Bool) {s t : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} (pre : AffineDecodePre s boundary bytes) (state : Frame s t)
    (size : bytes.size = 65) (rip : t.RIP = if y then 0x110635 else 0x110820)
    (source : (if y then t.regValue .rsi else t.regValue .rbp) = s.regValue .rsi) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧
      u.RIP = (if y then 0x110671 else 0x11085c) ∧
      SecretKeyFromBytes.Scalar.Nat256At u (stackPtr s - 592)
        (octetsToNat (bytes.extract (if y then 33 else 1) (if y then 65 else 33))) ∧
      (SecretKeyFromBytes.Scalar.Limbs.mk (u.regValue .rdx)
        ((Operand.reg (if y then 7 else 6) : Operand 64).read u)
        (u.regValue .rcx) (u.regValue .rax)).toNat =
          octetsToNat (bytes.extract (if y then 33 else 1) (if y then 65 else 33)) ∧
      AgreesExcept (decodeComponents y t) t u := by
  obtain ⟨n, a, runA, frameA, load⟩ := load_correct y pre state rip source
  have loadRip : a.RIP = if y then 0x110651 else 0x11083c := by
    cases y <;> exact load.rip
  obtain ⟨m, u, runU, frameU, store⟩ := store_correct y pre frameA loadRip
  have loadAgrees := load.agrees
  rw [load_components] at loadAgrees
  have storeAgrees := store.agrees
  rw [store_components] at storeAgrees
  have spA : stackPtr a = stackPtr t :=
    loadAgrees.read (n := 64) (r := 4) (by cases y <;> simp)
  have addr : stackPtr a + 168 = stackPtr s - 592 := by
    rw [frameA.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have values := load_value y size (input_of_frame pre state.frame) source load
  let chunk := bytes.extract (if y then 33 else 1) (if y then 65 else 33)
  have chunkSize : chunk.size = 32 := by cases y <;> simp [chunk, size]
  refine ⟨n+m, u, runA.trans runU, frameU, ?_, ?_, ?_, ?_⟩
  · cases y <;> exact store.rip
  · apply SecretKeyFromBytes.Scalar.nat256At_of_memLoad_limbs
    · have bound := SecretKeyFromBytes.Encoding.octetsToNat_lt chunk
      rw [chunkSize] at bound
      exact bound
    · intro i hi
      exact frameU.allocated _ ((stack_sub_readable pre.stack (offset := 592) (len := 32)
        (by decide) (by decide)).mem i hi)
    · intro j hj
      have h0 : memLoad u.external (stackPtr a + 168) 64 = a.regValue .rdx := by
        cases y <;> exact store.writes.1
      have h1 : memLoad u.external (stackPtr a + 176) 64 =
          (Operand.reg (if y then 7 else 6) : Operand 64).read a := by
        cases y <;> exact store.writes.2.1
      have h2 : memLoad u.external (stackPtr a + 184) 64 = a.regValue .rcx := by
        cases y <;> exact store.writes.2.2.1
      have h3 : memLoad u.external (stackPtr a + 192) 64 = a.regValue .rax := by
        cases y <;> exact store.writes.2.2.2
      rw [← addr]
      have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
      rcases cases with rfl | rfl | rfl | rfl
      · simpa using h0.trans values.2.2.2
      · simpa [BitVec.add_assoc] using h1.trans values.2.2.1
      · simpa [BitVec.add_assoc] using h2.trans values.2.1
      · simpa [BitVec.add_assoc] using h3.trans values.1
  · have reg (r : BitVec 5) : (Operand.reg r : Operand 64).read u =
        (Operand.reg r : Operand 64).read a :=
      storeAgrees.read (by simp [storeComponents])
    change (SecretKeyFromBytes.Scalar.Limbs.mk ((Operand.reg 2 : Operand 64).read u)
      ((Operand.reg (if y then 7 else 6) : Operand 64).read u)
      ((Operand.reg 1 : Operand 64).read u) ((Operand.reg 0 : Operand 64).read u)).toNat = _
    rw [reg 2, reg (if y then 7 else 6), reg 1, reg 0]
    change (SecretKeyFromBytes.Scalar.Limbs.mk (a.regValue .rdx)
      ((Operand.reg (if y then 7 else 6) : Operand 64).read a)
      (a.regValue .rcx) (a.regValue .rax)).toNat = _
    rw [values.1, values.2.1, values.2.2.1, values.2.2.2]
    apply SecretKeyFromBytes.Scalar.limbs_ofNat_toNat
    have bound := SecretKeyFromBytes.Encoding.octetsToNat_lt chunk
    rw [chunkSize] at bound
    exact bound
  · have h := loadAgrees.trans storeAgrees
    simpa only [decodeComponents, storeComponents, spA] using h

end P256.Proofs.Sec1.Affine.Uncompressed.Parse
