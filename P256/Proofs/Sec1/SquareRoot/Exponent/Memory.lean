import P256.Proofs.Sec1.SquareRoot.Exponent.Frame
import P256.Proofs.Sec1.SquareRoot.Exponent.Preservation
import P256.Proofs.Field.Preserve

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot

open P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem ExponentFrame.input_residue [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {x : Nat} (ctx : ExponentPre s boundary x) (frame : ExponentFrame s t) :
    ResidueAt t (s.regValue .rsi) x := by
  have bytes {i : Nat} (hi : i < 144) :
      t.external[s.regValue .rsi + BitVec.ofNat 64 i]? =
        s.external[s.regValue .rsi + BitVec.ofNat 64 i]? := by
    apply frame_read frame.frame _
      (memoryRegion_contains_add ctx.inputBounded (Nat.le_refl _) (Nat.le_refl _) hi)
    intro region hr
    have cases : region = registerRegion s .rdi 32 ∨ region = Stack.region s 1584 := by simpa using hr
    rcases cases with rfl | rfl
    · exact ctx.separation (0 : Fin 3) (1 : Fin 3) (by decide)
    · exact ctx.separation (0 : Fin 3) (2 : Fin 3) (by decide)
  constructor
  · exact ctx.residue.1.of_bytes_eq (fun i hi => bytes (by omega))
  · intro i hi
    have he : s.regValue .rsi + 32 + BitVec.ofNat 64 i =
        s.regValue .rsi + BitVec.ofNat 64 (32+i) := by
      rw [BitVec.ofNat_add, ← BitVec.add_assoc]
      rfl
    change t.external[s.regValue .rsi + 32 + BitVec.ofNat 64 i]? = _
    rw [he, bytes (by omega), ← he]
    exact ctx.residue.2 i hi

theorem exponent_word_of_bytes {s t : RamState} {a : BitVec 64} {n : Nat}
    (bytes : ∀ i < n / 8, t.external[a + BitVec.ofNat 64 i]? = s.external[a + BitVec.ofNat 64 i]?) :
    (Operand.mem a : Operand n).read t = (Operand.mem a : Operand n).read s := by
  apply memLoad_congr
  intro i hi
  exact congrArg (fun a : Option UInt8 => a.getD 0) (bytes i hi)

theorem ExponentConstants.of_upper_bytes [Bindings] {s t u : RamState}
    {boundary : ReturnBoundary} {x cutoff : Nat} (ctx : ExponentPre s boundary x)
    (h : ExponentConstants s t x) (frame : ExponentFrame s u) (lower : cutoff ≤ 120)
    (bytes : ∀ offset len : Nat, cutoff ≤ offset → offset + len ≤ 1368 →
      ∀ i < len, u.external[exponentFrameBase s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
        t.external[exponentFrameBase s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?) :
    ExponentConstants s u x := by
  have word {offset : Nat} {value : BitVec 64} (lo : cutoff ≤ offset) (hi : offset + 8 ≤ 1368)
      (hv : exponentWordAt t (exponentFrameBase s + BitVec.ofNat 64 offset) value) :
      exponentWordAt u (exponentFrameBase s + BitVec.ofNat 64 offset) value :=
    (exponent_word_of_bytes (bytes offset 8 lo hi)).trans hv
  refine ⟨frame.input_residue ctx, ?_, ?_, ?_,
    word (by change cutoff ≤ 136; omega) (by decide) h.modulus0,
    word (by change cutoff ≤ 128; omega) (by decide) h.modulus1,
    word (by change cutoff ≤ 152; omega) (by decide) h.modulus2,
    word (by change cutoff ≤ 144; omega) (by decide) h.modulus3,
    word (by change cutoff ≤ 680; omega) (by decide) h.firstWindow,
    word (by change cutoff ≤ 696; omega) (by decide) h.parameterPointer,
    word (by change cutoff ≤ 688; omega) (by decide) h.firstWord,
    word (by change cutoff ≤ 736; omega) (by decide) h.inverse,
    word (by change cutoff ≤ 728; omega) (by decide) h.initialMask,
    word (by change cutoff ≤ 712; omega) (by decide) h.negativeInverse⟩
  · intro i hi
    apply (h.table i hi).of_bytes_eq
    intro j hj
    have he := bytes (0x338+32*i) 32 (by omega) (by omega) j hj
    simpa only [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using he
  · refine ⟨h.exponent.1, ?_⟩
    intro i hi
    exact (bytes 0x538 32 (by omega) (by decide) i hi).trans (h.exponent.2 i hi)
  · exact (exponent_word_of_bytes (bytes 0x78 4 (by omega) (by decide))).trans h.initialWindow

end P256.Proofs.Sec1.SquareRoot
