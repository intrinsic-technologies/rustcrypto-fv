import P256.Proofs.Nonce.Initialize.Conversions.Bsr.Parity

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Conversions.Bsr

open X86 X86.Helpers X86Proofs

def bsrValue64 (x : BitVec 64) : BitVec 64 :=
  BitVec.ofInt 64 (63 - leadingZeroCount64 x)

def bsrFlags64 (x : BitVec 64) : StatusFlags :=
  ⟨false, !oddParity64 x, false, x == 0, false, false⟩

def bsrOracleUsed (x : BitVec 64) : Nat := if x = 0 then 64 else 0

theorem bsr_flags_store (r : BitVec 64) (zf pf : Bool) :
    (⟨false, pf, false, zf, false, false⟩ : StatusFlags).store r =
      Runtime.setSlice (Runtime.setSlice (Runtime.setSlice (Runtime.setSlice
        (Runtime.setSlice (Runtime.setSlice r 6 1 (BitVec.ofBool zf)) 11 1 0#1)
          7 1 0#1) 4 1 0#1) 2 1 (BitVec.ofBool pf)) 0 1 0#1 := by
  rflags_ext

theorem bsr64_operation {σ : Type} (s : X86.State σ) (x : BitVec 64) :
    (X86.Instructions.Operations.BSR 64 x).run s =
      (.ok ((if x = 0 then (s.oracle.take 64).1 else bsrValue64 x), x != 0),
        setFlags {s with oracle := oracleSkip s.oracle (bsrOracleUsed x)} (bsrFlags64 x)) := by
  unfold X86.Instructions.Operations.BSR
  simp only [isParityOdd64_run, countLeadingZeroBits64_run]
  by_cases hx : x = (0 : BitVec 64)
  · subst x
    repeat spec_bind_rfl
    apply Prod.ext
    · rfl
    · symm
      apply setFlags_eq_of_store
      have hp : oddParity64 (0 : BitVec 64) = false := by decide +kernel
      rw [bsrFlags64, hp]
      exact bsr_flags_store s.RFLAGS true true
  · have hz : Std.Bits.Is_Zero (size := 64) x = .ok false := by
      have hx' : x ≠ 0#64 := hx
      simp [Std.Bits.Is_Zero, x86_runtime, hx', bind, pure, Except.bind, Except.pure]
    rw [hz]
    repeat spec_bind_rfl
    simp only [Int.reduceSub, Int.reduceToNat, Int.reducePow, Int.ediv_one]
    change (Except.ok (bsrValue64 x, true), {s with RFLAGS := (
      Runtime.setSlice (Runtime.setSlice (Runtime.setSlice (Runtime.setSlice
        (Runtime.setSlice (Runtime.setSlice s.RFLAGS 6 1 0#1) 11 1 0#1)
          7 1 0#1) 4 1 0#1) 2 1 (if oddParity64 x then 0#1 else 1#1)) 0 1 0#1)}) = _
    apply Prod.ext
    · simp only [hx, ↓reduceIte, bne_iff_ne.mpr hx]
    · symm
      simp only [bsrOracleUsed, hx, ↓reduceIte, oracleSkip_zero]
      apply setFlags_eq_of_store
      rw [bsrFlags64, bsr_flags_store]
      have hx' : x ≠ 0#64 := hx
      cases oddParity64 x <;> simp [hx', BitVec.ofBool]

end P256.Proofs.Nonce.Initialize.Conversions.Bsr
