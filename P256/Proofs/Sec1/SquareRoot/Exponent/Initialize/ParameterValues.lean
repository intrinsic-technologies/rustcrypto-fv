import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.ParameterMemory
import P256.Proofs.Sec1.SquareRoot.Parameters
import P256.Proofs.Field.Representation

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.ExponentInitialize

open P256.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

set_option maxRecDepth 4096 in
theorem initialParameterCopies_targets :
    ∀ pair ∈ initialParameterCopies, pair.2 ≤ 1360 ∧ pair.2 % 8 = 0 := by
  decide +kernel

set_option maxRecDepth 4096 in
theorem initialParameterCopies_word (s : RamState) (value : BitVec 64)
    (i j : Nat) (hi : i < 16) (hne : i ≠ 1) (hj : j < 4) :
    parameterCopiedWord s initialParameterCopies (0xa0 + 32*i + 8*j) value =
      memLoad s.external (s.regValue .rsi + BitVec.ofNat 64 (64 + 8*j)) 64 := by
  have casesI : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨
      i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 := by omega
  have casesJ : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases casesI with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact (hne rfl).elim | skip
  all_goals rcases casesJ with rfl | rfl | rfl | rfl
  all_goals rfl

theorem initialize_parameter_values [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {x : Nat} (ctx : ExponentPre s boundary x) (hf : Frame s t) (memory : Ram)
    (hm : t.external = parameterCopiesMemory s initialParameterCopies memory) :
    ∀ i < 16, i ≠ 1 →
      Field.MontgomeryAt t (exponentFrameBase s + BitVec.ofNat 64 (0xa0 + 32*i)) 1 := by
  intro i hi hne
  have source := parameters_one ctx.residue.2
  apply Field.montgomeryAt_of_memLoad_limbs source.1
  · have hr := ScalarFrame.stack_readable (frameOffset := 1416) ctx.toCalleePre hf
      (offset := 0xa0 + 32*i) (len := 32) (by decide) (by omega)
    have hs : stackPtr t = exponentFrameBase s := hf.rsp
    rw [hs] at hr
    exact hr.mem
  · intro j hj
    rw [hm, BitVec.add_assoc, ← BitVec.ofNat_add,
      parameterCopiesMemory_word s initialParameterCopies memory
        (0xa0 + 32*i + 8*j) (by omega) (by omega) initialParameterCopies_targets,
      initialParameterCopies_word s _ i j hi hne hj]
    have h := source.memLoad_limb j hj
    simpa only [BitVec.add_assoc, ← BitVec.add_assoc (32 : BitVec 64) 32,
      BitVec.reduceAdd, BitVec.ofNat_add] using h

end P256.Proofs.Sec1.SquareRoot.ExponentInitialize
