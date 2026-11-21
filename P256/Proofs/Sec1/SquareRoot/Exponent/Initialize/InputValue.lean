import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.InputCopy
import P256.Proofs.Field.Representation

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.ExponentInitialize

open P256.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

set_option maxRecDepth 2048 in
theorem inputCopyMemory_word (s : RamState) (memory : Ram) (j : Nat) (hj : j < 4) :
    memLoad (inputCopyMemory s memory)
      (exponentFrameBase s + 0x2f8 + BitVec.ofNat 64 (8*j)) 64 =
      memLoad s.external (s.regValue .rsi + BitVec.ofNat 64 (8*j)) 64 := by
  have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  all_goals
    simp only [inputCopyMemory, List.foldl_cons, List.foldl_nil, BitVec.ofNat_eq_ofNat,
      Nat.reduceMul, BitVec.add_assoc, BitVec.reduceAdd, BitVec.add_zero]
    repeat first
      | rw [memLoad_memStore_apart _ (exponentFrameBase s) _ _ _ 64
          (by unfold OffsetsApart; decide +kernel) (by decide) (by decide)]
      | exact memLoad_memStore _ _ (by decide) (by decide) _

theorem inputCopyMemory_value [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {x : Nat} (ctx : ExponentPre s boundary x) (hf : Frame s t) (memory : Ram)
    (hm : t.external = inputCopyMemory s memory) :
    Field.MontgomeryAt t (exponentFrameBase s + 0x2f8) x := by
  apply Field.montgomeryAt_of_memLoad_limbs ctx.residue.1.1
  · have hr := ScalarFrame.stack_readable (frameOffset := 1416) ctx.toCalleePre hf
      (offset := 0x2f8) (len := 32) (by decide) (by decide)
    have hs : stackPtr t = exponentFrameBase s := hf.rsp
    rw [hs] at hr
    exact hr.mem
  · intro j hj
    rw [hm, inputCopyMemory_word s memory j hj]
    exact ctx.residue.1.memLoad_limb j hj

end P256.Proofs.Sec1.SquareRoot.ExponentInitialize
