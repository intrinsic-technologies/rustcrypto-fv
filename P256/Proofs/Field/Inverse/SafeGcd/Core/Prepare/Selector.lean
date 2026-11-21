import P256.Proofs.Field.Inverse.SafeGcd.Core.Defs
import P256.Proofs.Field.Inverse.SafeGcd.Core.Advance

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.Prepare.Selector

open Shared (batchCount)

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

inductive Label where | entry | finish

@[refine_layout] def start : Label → Machine.Label
  | .entry => .l1179fa | .finish => .l117a59

def program : Program Support.Op Label (fun _ => 0) 0 where
  blocks
  | .entry => .terminate (.br ⟨.finish, #v[]⟩)
  | .finish => .terminate (.ret #v[])

def dialect : Dialect Support.Op Unit LoopState where
  eval op := nomatch op
  truth _ := false

def batchSelector (remaining : BitVec 32) : BitVec 32 :=
  let flag := ((remaining - 62) &&& ~~~remaining) >>> 31
  ((remaining ^^^ 62) &&& -flag) ^^^ 62

theorem batchSelector_eq {remaining : Nat} (bound : remaining ≤ 591) :
    batchSelector (BitVec.ofNat 32 remaining) = BitVec.ofNat 32 (min remaining 62) := by
  have checked : ∀ remaining : Fin 592,
      batchSelector (BitVec.ofNat 32 remaining.val) =
        BitVec.ofNat 32 (min remaining.val 62) := by decide +kernel
  exact checked ⟨remaining, by omega⟩

def flag (s : LoopState) : BitVec 32 :=
  ((BitVec.ofNat 32 s.remaining - 62) &&& ~~~BitVec.ofNat 32 s.remaining) >>> 31

@[refine_layout] def atoms (l : Label) (fr : Activation) (controls : RamState) (p : Inputs)
    (s : LoopState) : List Atom :=
  match l with
  | .entry => loopAtoms fr controls p s ++ [.fact (1 ≤ s.remaining), .fact (s.remaining ≤ 591)]
  | .finish => residentAtoms fr controls p s ++
      [.gpr 5 s.delta, .gpr 13 (fr.rsp - 0x180), .gpr 9 0x7fffffffffffffff,
       .gpr 8 ((BitVec.ofNat 32 (batchCount s)).setWidth 64),
       .gpr 1 s.f.words[0], .gpr 2 (s.f.sign.setWidth 64), .gpr 6 s.g.words[0],
       .mem (fr.rsp - 0x180) 8 s.g.sign,
       .mem (fr.rsp - 0x184) 32 (BitVec.ofNat 32 (batchCount s)),
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

theorem shift_byte (v : BitVec 32) :
    ((v >>> 31).setWidth 8).setWidth 32 = v >>> 31 := by bv_omega

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
  have hselector := batchSelector_eq
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
  simp only [batchSelector] at hselector
  refine_uir []
  all_goals refine_lifted [flag, batchCount, shift_byte, hcast, hselector, hcount, xorFlags, Option.getD_some]
  all_goals try contradiction
  all_goals try refine_close [flag, batchCount, shift_byte, hcast, hselector, hcount, xorFlags, Option.getD_some]
  all_goals try simp only [cfg_eval, BitVec.reduceSetWidth, BitVec.reduceSignExtend,
    BitVec.reduceEq, ite_false, ite_true, Value.get_mk_setWidth, BitVec.setWidth_eq]
  all_goals try ct_core_stack_store fr mem _hcode
  all_goals try bv_omega
  all_goals try simp only [xorFlags, hcount, Option.getD_some]

end P256.Proofs.Field.Inverse.SafeGcd.Core.Prepare.Selector
