import P256.Proofs.Scalar.Inverse.Wrapper.Defs

namespace P256.Proofs.Scalar.Inverse.Wrapper.Tail

open P256.Proofs.Field.Inverse.SafeGcd
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

inductive Label where | finish

def program : Program Core.Support.Op Label (fun _ => 0) 0 where
  blocks _ := .terminate (.ret #v[])

def dialect : Dialect Core.Support.Op Unit Inputs where
  eval op := nomatch op
  truth _ := false

@[refine_layout] def outputAtoms (fr : Activation) (p : Inputs) : List Atom :=
  Machine.Inverse.doneAt fr ++
  [.words fr.rdi 64 (resultWords p), .mem (fr.rdi + 32) 8 (resultChoice p), .readable fr.rdi 33, .gpr 0 fr.rdi,
   .reg 39 ⟨32, p.mxcsr⟩, .reg 51 ⟨16, p.fcw⟩]

def layout (fr : Activation) : Layout program dialect Machine.lifted Unit where
  start _ := .l118966
  Params _ := Inputs
  args _ _ := #v[]
  store _ p := p
  atoms _ _ p := choiceReturned fr p
  Result := Inputs
  output p := ⟨#v[], none, p⟩
  done _ p := outputAtoms fr p
  retAddr _ := fr.ret
  original _ := fr.original
  regions _ := [fr.region, outputRegion fr]

attribute [local cfg_eval] Operand.read_reg_get

set_option maxHeartbeats 500000 in
theorem finish_block (code : CodeMap) (_hcode : ∀ x ∈ Machine.fnCode, x ∈ code) (fr : Activation) :
    (layout fr).BlockSimulation code .finish := by
  refine_intro
  refine_uir []
  all_goals refine_lifted []
  all_goals try refine_close []
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
  all_goals try
    apply RamWriteFrame.memStore
    · exact hframe
    · refine ⟨outputRegion fr, by simp, ?_, ?_⟩
      all_goals simp only [outputRegion]
      all_goals bv_omega
  all_goals try bv_omega

end P256.Proofs.Scalar.Inverse.Wrapper.Tail
