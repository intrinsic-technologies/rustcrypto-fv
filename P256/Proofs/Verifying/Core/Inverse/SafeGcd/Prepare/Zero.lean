import P256.Proofs.Verifying.Core.Inverse.SafeGcd.Defs
import P256.Proofs.Verifying.Core.Inverse.SafeGcd.Advance

namespace P256.Proofs.Verifying.Core.Inverse.SafeGcd.Prepare.Zero

open P256.Proofs.Field.Inverse.SafeGcd
open P256.Proofs.Field.Inverse.SafeGcd.Core.Shared
open P256.Proofs.Field.Inverse.SafeGcd.Core.Shared.Batch
open P256.Proofs.Field.Inverse.SafeGcd.Core

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

theorem zero_words_eq (a : Vector (BitVec 64) 4) : zeroWords a =
     decide (((a[0] = 0 ∧ a[1] = 0) ∧ a[2] = 0) ∧ a[3] = 0) := by
   simp only [zeroWords, Bool.beq_eq_decide_eq]
   apply Bool.eq_iff_iff.mpr
   simp only [decide_eq_true_eq]
   change ((a[0] ||| a[1] ||| a[2] ||| a[3]) = 0#64) ↔ _
   rw [BitVec.or_eq_zero_iff, BitVec.or_eq_zero_iff, BitVec.or_eq_zero_iff]
   rfl

inductive Label where | entry | finish

@[refine_layout] def exit (halt : Bool) : Machine.Label :=
  match halt with | true => .l114698 | false => .l114574

@[refine_layout] def start (halt : Bool) : Label → Machine.Label
  | .entry => .l11454e | .finish => exit halt

def program : Program Core.Support.Op Label (fun _ => 0) 0 where
  blocks
  | .entry => .terminate (.br ⟨.finish, #v[]⟩)
  | .finish => .terminate (.ret #v[])

def dialect : Dialect Core.Support.Op Unit LoopState where
  eval op := nomatch op
  truth _ := false

@[refine_layout] def atoms (halt : Bool) (l : Label) (fr : Activation) (controls : RamState)
    (p : Inputs) (s : LoopState) : List Atom :=
  match l, halt with
  | .finish, true => frameAtoms fr controls ++ commonAtoms fr p ++ savedInputAtoms fr p ++
    stateAtoms fr s ++ [.gpr 12 s.delta, .fact (zeroWords s.g.words = true)]
  | .finish, false => loopAtoms fr controls p s ++ [.fact (zeroWords s.g.words = false), .gpr 2 s.g.words[0]]
  | .entry, _ => loopAtoms fr controls p s ++ [.fact (zeroWords s.g.words = halt)]

def layout (halt : Bool) (fr : Activation) (controls : RamState) (p : Inputs) :
    Layout program dialect Machine.lifted Unit where
  start := start halt
  Params _ := LoopState
  args _ _ := #v[]
  store _ s := s
  atoms l _ s := atoms halt l fr controls p s
  Result := Empty
  output r := nomatch r
  done _ r := nomatch r
  retAddr _ := fr.ret
  original _ := fr.original
  regions _ := [fr.region, outputRegion fr]

attribute [local cfg_eval] Operand.read_reg_get

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1200000 in
theorem block_true (code : CodeMap) (fr : Activation) (controls : RamState) (p : Inputs) :
    (layout true fr controls p).BlockSimulation code .entry := by
  refine_intro
  simp only [zero_words_eq, decide_eq_true_eq] at *
  obtain ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩ := atom51
  refine_uir []
  all_goals refine_lifted [not_true_eq_false, zero_words_eq, h0, h1, h2, h3]
  all_goals try contradiction
  all_goals try refine_close [zero_words_eq, h0, h1, h2, h3]
  all_goals try first
    | (simpa only [show fr.rsp - 384 + 32 = fr.rsp - 352 by bv_omega] using atom42)
    | (simpa only [show fr.rsp - 344 + 32 = fr.rsp - 312 by bv_omega] using atom44)
    | (simpa only [show fr.rsp - 296 + 32 = fr.rsp - 264 by bv_omega] using atom46)
    | (simpa only [show fr.rsp - 256 + 32 = fr.rsp - 224 by bv_omega] using atom48)
  all_goals try bv_omega
  all_goals simp

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1200000 in
theorem block_false (code : CodeMap) (fr : Activation) (controls : RamState) (p : Inputs) :
    (layout false fr controls p).BlockSimulation code .entry := by
  refine_intro
  simp only [zero_words_eq, decide_eq_false_iff_not] at atom51
  by_cases h0 : g.words[0] = 0
  · by_cases h1 : g.words[1] = 0
    · by_cases h2 : g.words[2] = 0
      · have h3 : g.words[3] ≠ 0 := by
          intro h3
          exact atom51 ⟨⟨⟨h0, h1⟩, h2⟩, h3⟩
        refine_uir []
        all_goals refine_lifted [not_true_eq_false, zero_words_eq, Bool.beq_eq_decide_eq, h0, h1, h2, h3]
        all_goals try contradiction
        all_goals try refine_close [zero_words_eq, h0, h1, h2, h3]
        all_goals try first
          | (simpa only [show fr.rsp - 384 + 32 = fr.rsp - 352 by bv_omega] using atom42)
          | (simpa only [show fr.rsp - 344 + 32 = fr.rsp - 312 by bv_omega] using atom44)
          | (simpa only [show fr.rsp - 296 + 32 = fr.rsp - 264 by bv_omega] using atom46)
          | (simpa only [show fr.rsp - 256 + 32 = fr.rsp - 224 by bv_omega] using atom48)
        all_goals try bv_omega
        all_goals simp
      · refine_uir []
        all_goals refine_lifted [not_true_eq_false, zero_words_eq, Bool.beq_eq_decide_eq, h0, h1, h2]
        all_goals try contradiction
        all_goals try refine_close [zero_words_eq, h0, h1, h2]
        all_goals try first
          | (simpa only [show fr.rsp - 384 + 32 = fr.rsp - 352 by bv_omega] using atom42)
          | (simpa only [show fr.rsp - 344 + 32 = fr.rsp - 312 by bv_omega] using atom44)
          | (simpa only [show fr.rsp - 296 + 32 = fr.rsp - 264 by bv_omega] using atom46)
          | (simpa only [show fr.rsp - 256 + 32 = fr.rsp - 224 by bv_omega] using atom48)
        all_goals try bv_omega
        all_goals simp
    · refine_uir []
      all_goals refine_lifted [not_true_eq_false, zero_words_eq, Bool.beq_eq_decide_eq, h0, h1]
      all_goals try contradiction
      all_goals try refine_close [zero_words_eq, h0, h1]
      all_goals try first
        | (simpa only [show fr.rsp - 384 + 32 = fr.rsp - 352 by bv_omega] using atom42)
        | (simpa only [show fr.rsp - 344 + 32 = fr.rsp - 312 by bv_omega] using atom44)
        | (simpa only [show fr.rsp - 296 + 32 = fr.rsp - 264 by bv_omega] using atom46)
        | (simpa only [show fr.rsp - 256 + 32 = fr.rsp - 224 by bv_omega] using atom48)
      all_goals try bv_omega
      all_goals simp
  · refine_uir []
    all_goals refine_lifted [not_true_eq_false, zero_words_eq, Bool.beq_eq_decide_eq, h0]
    all_goals try contradiction
    all_goals try refine_close [zero_words_eq, h0]
    all_goals try first
      | (simpa only [show fr.rsp - 384 + 32 = fr.rsp - 352 by bv_omega] using atom42)
      | (simpa only [show fr.rsp - 344 + 32 = fr.rsp - 312 by bv_omega] using atom44)
      | (simpa only [show fr.rsp - 296 + 32 = fr.rsp - 264 by bv_omega] using atom46)
      | (simpa only [show fr.rsp - 256 + 32 = fr.rsp - 224 by bv_omega] using atom48)
    all_goals try bv_omega
    all_goals simp

 theorem block (halt : Bool) (code : CodeMap) (fr : Activation) (controls : RamState) (p : Inputs) :
    (layout halt fr controls p).BlockSimulation code .entry := by
  cases halt
  · exact block_false code fr controls p
  · exact block_true code fr controls p

end P256.Proofs.Verifying.Core.Inverse.SafeGcd.Prepare.Zero
