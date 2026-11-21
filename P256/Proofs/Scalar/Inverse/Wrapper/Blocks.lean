import P256.Proofs.Scalar.Inverse.Wrapper.Defs
import P256.Proofs.Common.Field.SquareRoot.Exponent.ReadDigit.State

namespace P256.Proofs.Scalar.Inverse.Wrapper

open P256.Proofs.Field.Inverse.SafeGcd
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

theorem load32_low8 (mem : Ram) (a : BitVec 64) :
    ((memLoad mem a 32).setWidth 64).setWidth 8 = memLoad mem a 8 := by
  have h := Common.Field.SquareRoot.memLoad_setWidth_of_le mem a (m := 32) (n := 8)
    (by decide) (by decide)
  have he : ((memLoad mem a 32).setWidth 64).setWidth 8 = (memLoad mem a 32).setWidth 8 := by bv_omega
  exact he.trans h

attribute [local cfg_eval] Operand.read_reg_get

set_option maxHeartbeats 1200000 in
theorem call_block (v : Bool) (code : CodeMap) (hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    (fr : Activation) : (layout fr).BlockSimulation code (if v then .middle else .entry) := by
  cases v <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> refine_intro
  all_goals refine_uir []
  all_goals refine_lifted [load32_low8]
  all_goals first
    | (refine ⟨(), ?_, ?_⟩
       all_goals first
         | (intro uo lo hret _; obtain ⟨_, ⟨r, _⟩, _⟩ := hret; cases r)
         | refine_close [load32_low8])
    | skip
  all_goals try simp only [cfg_eval, BitVec.reduceSetWidth, BitVec.reduceSignExtend,
    BitVec.reduceEq, ite_false, ite_true, Value.get_mk_setWidth, BitVec.setWidth_eq]
  all_goals try wrapper_store fr mem hcode
  all_goals try
    apply Correction.Execution.CrossPage.StoreOk.of_region (b := fr.rdi) (len := 33)
    · repeat' first | assumption | apply Writable.memStore
    · refine_arith
    · refine_arith
    · apply Correction.Execution.writable_codeApart (mem := mem) _ hcode (by decide) (by decide)
      apply Writable.sub (b := fr.rdi) (len := 33)
      · repeat' first | assumption | apply Writable.memStore
      · refine_arith
      · refine_arith
  all_goals try bv_omega
  all_goals try
    iterate 5 apply RamWriteFrame.memStore
    · exact hframe
    all_goals first
      | (refine ⟨fr.region, by simp [Activation.region], ?_, ?_⟩; all_goals simp only [Activation.region]; all_goals bv_omega)
      | (refine ⟨outputRegion fr, by simp, ?_, ?_⟩; all_goals simp only [outputRegion]; all_goals bv_omega)

end P256.Proofs.Scalar.Inverse.Wrapper
