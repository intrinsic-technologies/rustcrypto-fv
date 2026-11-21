import P256.Proofs.Verifying.Core.Inverse.SafeGcd.Prepare.Selector
import P256.Proofs.Verifying.Core.Inverse.SafeGcd.Batch.Defs

namespace P256.Proofs.Verifying.Core.Inverse.SafeGcd.Prepare.Signed

open P256.Proofs.Field.Inverse.SafeGcd
open P256.Proofs.Field.Inverse.SafeGcd.Core.Shared
open P256.Proofs.Field.Inverse.SafeGcd.Core.Shared.Batch
open P256.Proofs.Field.Inverse.SafeGcd.Core

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

inductive Label where | entry | finish

@[refine_layout] def start : Label → Machine.Label
  | .entry => .l1145af | .finish => .l114675

def program : Program Core.Support.Op Label (fun _ => 0) 0 where
  blocks
  | .entry => .terminate (.br ⟨.finish, #v[]⟩)
  | .finish => .terminate (.ret #v[])

def dialect : Dialect Core.Support.Op Unit LoopState where
  eval op := nomatch op
  truth _ := false

@[refine_layout] def residentAtoms (fr : Activation) (controls : RamState) (p : Inputs) (s : LoopState) : List Atom :=
  frameAtoms fr controls ++ commonAtoms fr p ++ savedInputAtoms fr p ++ stateAtoms fr s ++
  [.mem (fr.rsp - 0x38) 64 (BitVec.ofNat 64 s.remaining)]

@[refine_layout] def finishAtoms (fr : Activation) (controls : RamState) (p : Inputs) (s : LoopState) : List Atom :=
  residentAtoms fr controls p s ++ [.gpr 9 ((BitVec.ofNat 32 (batchCount s)).setWidth 64)] ++
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
  have hf := atom42
  have hg := atom44
  rw [show fr.rsp - 384 + 32 = fr.rsp - 352 by bv_omega] at hf
  rw [show fr.rsp - 344 + 32 = fr.rsp - 312 by bv_omega] at hg
  refine_uir []
  all_goals refine_lifted [batchInput, lowWord, not_true_eq_false, hf, hg]
  all_goals try contradiction
  all_goals try refine_close [batchInput, lowWord, hf, hg]
  all_goals try simp only [cfg_eval, BitVec.reduceSetWidth, BitVec.reduceSignExtend,
    BitVec.reduceEq, ite_false, ite_true, Value.get_mk_setWidth, BitVec.setWidth_eq]
  all_goals try core_stack_store fr mem _hcode
  all_goals try bv_omega
  all_goals try first
    | (simpa only [show fr.rsp - 384 + 32 = fr.rsp - 352 by bv_omega] using atom42)
    | (simpa only [show fr.rsp - 344 + 32 = fr.rsp - 312 by bv_omega] using atom44)
    | (simpa only [show fr.rsp - 296 + 32 = fr.rsp - 264 by bv_omega] using atom46)
    | (simpa only [show fr.rsp - 256 + 32 = fr.rsp - 224 by bv_omega] using atom48)

end P256.Proofs.Verifying.Core.Inverse.SafeGcd.Prepare.Signed
