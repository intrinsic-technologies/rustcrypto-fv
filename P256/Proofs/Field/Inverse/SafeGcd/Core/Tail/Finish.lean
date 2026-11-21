import P256.Proofs.Field.Inverse.SafeGcd.Core.Tail.Defs

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.Tail.Finish

open Shared (zeroWords correctionInput)

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

inductive Label where | finish

def program : Program Support.Op Label (fun _ => 0) 0 where
  blocks _ := .terminate (.ret #v[])

def dialect : Dialect Support.Op Unit LoopState where
  eval op := nomatch op
  truth _ := false

@[refine_layout] def outputAtoms (fr : Activation) (controls : RamState) (p : Inputs) (s : LoopState) : List Atom :=
  Machine.Core.doneAt fr ++
  [.words fr.rdi 64 (Correction.correctedWords (correctionInput p s)),
   .mem (fr.rdi + 32) 8 (choiceByte p s), .readable fr.rdi 33, .reg 39 ⟨32, controls.MXCSR⟩, .reg 51 ⟨16, controls.FP87_Control⟩]

def layout (fr : Activation) (controls : RamState) (p : Inputs) : Layout program dialect Machine.lifted Unit where
  start _ := .l117c2f
  Params _ := LoopState
  args _ _ := #v[]
  store _ s := s
  atoms _ _ s := returnedAtoms fr controls p s
  Result := LoopState
  output s := ⟨#v[], none, s⟩
  done _ s := outputAtoms fr controls p s
  retAddr _ := fr.ret
  original _ := fr.original
  regions _ := [fr.region, outputRegion fr]

theorem choice_eq (a b : BitVec 64) :
    ((if b = 0 then 1#8 else 0) &&& (if a = 0 then 0#8 else 1)) =
      BitVec.ofNat 8 (if ¬ a = 0 ∧ b = 0 then 1 else 0) := by
  by_cases ha : a = 0 <;> by_cases hb : b = 0 <;> simp_all

attribute [local cfg_eval] Operand.read_reg_get

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem finish_block (code : CodeMap) (_hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    (fr : Activation) (controls : RamState) (p : Inputs) : (layout fr controls p).BlockSimulation code .finish := by
  refine_intro
  refine_uir []
  all_goals refine_lifted [choiceByte, nonzeroByte, zeroWords]
  all_goals try refine_close [choiceByte, nonzeroByte, zeroWords]
  all_goals try simp only [cfg_eval, BitVec.reduceSetWidth, BitVec.reduceSignExtend,
    BitVec.reduceEq, ite_false, ite_true, Value.get_mk_setWidth, BitVec.setWidth_eq]
  all_goals try
    apply StoreOk.of_region (b := fr.rdi) (len := 33)
    · repeat' first | assumption | apply Writable.memStore
    · refine_arith
    · refine_arith
    · apply Correction.Execution.writable_codeApart (mem := mem) _ _hcode (by decide) (by decide)
      apply Writable.sub (b := fr.rdi) (len := 33)
      · repeat' first | assumption | apply Writable.memStore
      · refine_arith
      · refine_arith
  all_goals try bv_omega
  all_goals try
    apply RamWriteFrame.memStore
    · exact hframe
    · refine ⟨outputRegion fr, by simp, ?_, ?_⟩
      all_goals simp only [outputRegion]
      all_goals bv_omega
  all_goals simp only [setWidth_mergeGPR8, orFlags, Option.getD_some, beq_iff_eq]
  all_goals exact choice_eq _ _

end P256.Proofs.Field.Inverse.SafeGcd.Core.Tail.Finish
