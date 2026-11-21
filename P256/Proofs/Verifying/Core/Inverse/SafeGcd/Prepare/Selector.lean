import P256.Proofs.Field.Inverse.SafeGcd.Core.Prepare.Selector
import P256.Proofs.Verifying.Core.Inverse.SafeGcd.Defs
import P256.Proofs.Verifying.Core.Inverse.SafeGcd.Advance

namespace P256.Proofs.Verifying.Core.Inverse.SafeGcd.Prepare.Selector

open P256.Proofs.Field.Inverse.SafeGcd
open P256.Proofs.Field.Inverse.SafeGcd.Core.Shared
open P256.Proofs.Field.Inverse.SafeGcd.Core.Shared.Batch
open P256.Proofs.Field.Inverse.SafeGcd.Core

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

inductive Label where | entry | finish

@[refine_layout] def start : Label → Machine.Label
  | .entry => .l114574 | .finish => .l1145af

def program : Program Core.Support.Op Label (fun _ => 0) 0 where
  blocks
  | .entry => .terminate (.br ⟨.finish, #v[]⟩)
  | .finish => .terminate (.ret #v[])

def dialect : Dialect Core.Support.Op Unit LoopState where
  eval op := nomatch op
  truth _ := false

def flag (s : LoopState) : BitVec 32 :=
  ((BitVec.ofNat 32 s.remaining - 62) &&& ~~~BitVec.ofNat 32 s.remaining) >>> 31

@[refine_layout] def atoms (l : Label) (fr : Activation) (controls : RamState) (p : Inputs)
    (s : LoopState) : List Atom :=
  loopAtoms fr controls p s ++ [.gpr 2 s.g.words[0], .fact (1 ≤ s.remaining),
    .fact (s.remaining ≤ 591)] ++ match l with
  | .entry => []
  | .finish => [.gpr 0 ((-flag s).setWidth 64),
      .gpr 9 ((BitVec.ofNat 32 (batchCount s)).setWidth 64),
      .reg 19 (Value.ofBool false),
      .mem (fr.rsp - 0xd8) 8 ((flag s).setWidth 8),
      .mem (fr.rsp - 0x38) 64 (BitVec.ofNat 64 s.remaining)]

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
  have hselector := P256.Proofs.Field.Inverse.SafeGcd.Core.Prepare.Selector.batchSelector_eq
    (remaining := remaining) (by assumption)
  have hsmall : min remaining 62 < 2^32 := by omega
  have hcount : (BitVec.ofNat 32 (min remaining 62) == 0) = false := by
    simp only [Bool.beq_eq_decide_eq, decide_eq_false_iff_not]
    intro hz
    have hn := congrArg BitVec.toNat hz
    change Nat.mod (min remaining 62) (2^32) = 0 at hn
    have hm : Nat.mod (min remaining 62) (2^32) = min remaining 62 := Nat.mod_eq_of_lt hsmall
    have hz0 := hm.symm.trans hn
    omega
  have hcast : (BitVec.ofNat 64 remaining).setWidth 32 = BitVec.ofNat 32 remaining := by bv_omega
  simp only [P256.Proofs.Field.Inverse.SafeGcd.Core.Prepare.Selector.batchSelector] at hselector
  refine_uir []
  all_goals refine_lifted [flag, batchCount, P256.Proofs.Field.Inverse.SafeGcd.Core.Prepare.Selector.shift_byte, hcast, hselector, hcount]
  all_goals try refine_close [flag, batchCount, P256.Proofs.Field.Inverse.SafeGcd.Core.Prepare.Selector.shift_byte, hcast, hselector, hcount]
  all_goals try simp only [cfg_eval, BitVec.reduceSetWidth, BitVec.reduceSignExtend,
    BitVec.reduceEq, ite_false, ite_true, Value.get_mk_setWidth, BitVec.setWidth_eq]
  all_goals try core_stack_store fr mem _hcode
  all_goals try bv_omega
  all_goals try first
    | (simpa only [show fr.rsp - 384 + 32 = fr.rsp - 352 by bv_omega] using atom42)
    | (simpa only [show fr.rsp - 344 + 32 = fr.rsp - 312 by bv_omega] using atom44)
    | (simpa only [show fr.rsp - 296 + 32 = fr.rsp - 264 by bv_omega] using atom46)
    | (simpa only [show fr.rsp - 256 + 32 = fr.rsp - 224 by bv_omega] using atom48)
  all_goals try simp only [xorFlags, hcount, Option.getD_some]

end P256.Proofs.Verifying.Core.Inverse.SafeGcd.Prepare.Selector
