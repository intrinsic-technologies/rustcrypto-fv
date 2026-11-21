import P256.Proofs.Field.Inverse.SafeGcd.Core.Prepare.Selector
import P256.Proofs.Field.Inverse.SafeGcd.Core.Batch.Defs

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.Prepare.Signed

open Shared (batchCount batchInput lowWord)

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

inductive Label where | entry | finish

@[refine_layout] def start : Label → Machine.Label
  | .entry => .l117a59 | .finish => .l117aa0

def program : Program Support.Op Label (fun _ => 0) 0 where
  blocks
  | .entry => .terminate (.br ⟨.finish, #v[]⟩)
  | .finish => .terminate (.ret #v[])

def dialect : Dialect Support.Op Unit LoopState where
  eval op := nomatch op
  truth _ := false

@[refine_layout] def residentAtoms (fr : Activation) (controls : RamState) (p : Inputs) (s : LoopState) : List Atom :=
  Core.residentAtoms fr controls p s ++
  [.mem (fr.rsp - 0x38) 64 (BitVec.ofNat 64 s.remaining),
   .mem (fr.rsp - 0x184) 32 (BitVec.ofNat 32 (batchCount s))]

@[refine_layout] def finishAtoms (fr : Activation) (controls : RamState) (p : Inputs) (s : LoopState) : List Atom :=
  residentAtoms fr controls p s ++ [.gpr 13 (fr.rsp - 0x180)] ++
  Batch.wordAtoms (batchInput s) (batchCount s)

@[refine_layout] def atoms (l : Label) (fr : Activation) (controls : RamState) (p : Inputs)
    (s : LoopState) : List Atom :=
  match l with
  | .entry => Selector.atoms .finish fr controls p s
  | .finish => finishAtoms fr controls p s

def layout (fr : Activation) (controls : RamState) (p : Inputs) : Layout program dialect Machine.lifted Unit where
  start := start
  Params _ := LoopState
  args _ _ := #v[]
  store _ s := s
  atoms l _ s := atoms l fr controls p s
  Result := Empty
  output r := nomatch r
  done _ r := nomatch r
  retAddr _ := fr.ret
  original _ := fr.original
  regions _ := [fr.region, outputRegion fr]

attribute [local cfg_eval] Operand.read_reg_get


set_option maxRecDepth 4096 in
set_option maxHeartbeats 1200000 in
theorem block (code : CodeMap) (_hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    (fr : Activation) (controls : RamState) (p : Inputs) : (layout fr controls p).BlockSimulation code .entry := by
  refine_intro
  try simp only [show fr.rsp - 304 + 32 = fr.rsp - 272 by bv_omega,
    show fr.rsp - 256 + 32 = fr.rsp - 224 by bv_omega,
    show fr.rsp - 216 + 32 = fr.rsp - 184 by bv_omega,
    show fr.rsp - 176 + 32 = fr.rsp - 144 by bv_omega] at *
  refine_uir []
  all_goals refine_lifted [batchInput, lowWord, not_true_eq_false]
  all_goals try contradiction
  all_goals try refine_close [batchInput, lowWord]
  all_goals try simp only [cfg_eval, BitVec.reduceSetWidth, BitVec.reduceSignExtend,
    BitVec.reduceEq, ite_false, ite_true, Value.get_mk_setWidth, BitVec.setWidth_eq]
  all_goals try ct_core_stack_store fr mem _hcode
  all_goals try bv_omega

end P256.Proofs.Field.Inverse.SafeGcd.Core.Prepare.Signed
