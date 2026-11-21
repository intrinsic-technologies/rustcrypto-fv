import P256.Proofs.Field.Inverse.SafeGcd.Core.Update.CopyDE

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.Update.Finish

open Shared (batchCount batchResult nextState)

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

@[refine_layout] def haltAtoms (fr : Activation) (controls : RamState) (p : Inputs) (s : LoopState) : List Atom :=
  frameAtoms fr controls ++ commonAtoms fr p ++ savedInputAtoms fr p ++ stateAtoms fr s ++ [.gpr 5 s.delta]

@[refine_layout] def finishAtoms (last : Bool) (fr : Activation) (controls : RamState) (p : Inputs) (s : LoopState) : List Atom :=
  match last with | true => haltAtoms fr controls p s | false => loopAtoms fr controls p s

inductive Label where | entry | finish

@[refine_layout] def exit (last : Bool) : Machine.Label :=
  match last with | true => .l117be8 | false => .l1179fa

@[refine_layout] def start (last : Bool) : Label → Machine.Label
  | .entry => .l1179df | .finish => exit last

def program : Program Support.Op Label (fun _ => 0) 0 where
  blocks
  | .entry => .terminate (.br ⟨.finish, #v[]⟩)
  | .finish => .terminate (.ret #v[])

def dialect : Dialect Support.Op Unit LoopState where
  eval op := nomatch op
  truth _ := false

@[refine_layout] def atoms (last : Bool) (l : Label) (fr : Activation) (controls : RamState) (p : Inputs) (s : LoopState) : List Atom :=
  match l with
  | .entry => CopyDE.updatedAtoms fr controls p s ++
    [.fact (if last then s.remaining = batchCount s else batchCount s < s.remaining)]
  | .finish => finishAtoms last fr controls p (nextState p s)

def layout (last : Bool) (fr : Activation) (controls : RamState) (p : Inputs) : Layout program dialect Machine.lifted Unit where
  start := start last
  Params _ := LoopState
  args _ _ := #v[]
  store _ s := s
  atoms l _ s := atoms last l fr controls p s
  Result := Empty
  output r := nomatch r
  done _ r := nomatch r
  retAddr _ := fr.ret
  original _ := fr.original
  regions _ := [fr.region, outputRegion fr]

theorem count_zero (n : Nat) (hn : n ≤ 591) :
    (BitVec.ofNat 32 n - BitVec.ofNat 32 (min n 62) = 0#32) ↔ n = min n 62 := by
  have hm : min n 62 ≤ 62 := by omega
  bv_omega

attribute [local cfg_eval] Operand.read_reg_get

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem false_block (code : CodeMap) (fr : Activation) (controls : RamState) (p : Inputs) :
    (layout false fr controls p).BlockSimulation code .entry := by
  refine_intro
  try simp only [show fr.rsp - 304 + 32 = fr.rsp - 272 by bv_omega,
    show fr.rsp - 256 + 32 = fr.rsp - 224 by bv_omega,
    show fr.rsp - 216 + 32 = fr.rsp - 184 by bv_omega,
    show fr.rsp - 176 + 32 = fr.rsp - 144 by bv_omega] at *
  all_goals have hcast : (BitVec.ofNat 64 remaining).setWidth 32 = BitVec.ofNat 32 remaining := by bv_omega
  all_goals have hsub : BitVec.ofNat 32 remaining - BitVec.ofNat 32 (min remaining 62) =
      BitVec.ofNat 32 (remaining - min remaining 62) := by bv_omega
  all_goals simp only [batchCount, CopyDE.deState, Shared.nextState] at *
  all_goals have hzero := count_zero remaining (by assumption)
  have hlast : min remaining 62 < remaining := by assumption
  have hbranch : BitVec.ofNat 32 remaining - BitVec.ofNat 32 (min remaining 62) ≠ 0#32 := by
    intro hz
    have heq := hzero.mp hz
    omega
  all_goals refine_uir []
  all_goals refine_lifted [hcast, hbranch, batchCount, Shared.nextState, not_true_eq_false]
  all_goals try contradiction
  all_goals try refine_close [batchCount, Shared.nextState, CopyDE.deState, hcast, hsub]
  all_goals try bv_omega

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem true_block (code : CodeMap) (fr : Activation) (controls : RamState) (p : Inputs) :
    (layout true fr controls p).BlockSimulation code .entry := by
  refine_intro
  try simp only [show fr.rsp - 304 + 32 = fr.rsp - 272 by bv_omega,
    show fr.rsp - 256 + 32 = fr.rsp - 224 by bv_omega,
    show fr.rsp - 216 + 32 = fr.rsp - 184 by bv_omega,
    show fr.rsp - 176 + 32 = fr.rsp - 144 by bv_omega] at *
  all_goals have hcast : (BitVec.ofNat 64 remaining).setWidth 32 = BitVec.ofNat 32 remaining := by bv_omega
  all_goals have hsub : BitVec.ofNat 32 remaining - BitVec.ofNat 32 (min remaining 62) =
      BitVec.ofNat 32 (remaining - min remaining 62) := by bv_omega
  all_goals simp only [batchCount, CopyDE.deState, Shared.nextState] at *
  all_goals have hzero := count_zero remaining (by assumption)
  have hlast : remaining = min remaining 62 := by assumption
  have hbranch : BitVec.ofNat 32 remaining - BitVec.ofNat 32 (min remaining 62) = 0#32 := hzero.mpr hlast
  all_goals refine_uir []
  all_goals refine_lifted [hcast, hbranch, batchCount, Shared.nextState, not_true_eq_false]
  all_goals try contradiction
  all_goals try refine_close [batchCount, Shared.nextState, CopyDE.deState, hcast, hsub]
  all_goals try bv_omega

theorem block (last : Bool) (code : CodeMap) (fr : Activation) (controls : RamState) (p : Inputs) :
    (layout last fr controls p).BlockSimulation code .entry := by
  cases last
  · exact false_block code fr controls p
  · exact true_block code fr controls p

theorem finish_live (last : Bool) (fr : Activation) (controls : RamState) (p : Inputs) (s : LoopState) :
    ∀ a ∈ finishAtoms last fr controls p s, match a with
      | .reg r _ | .low r _ _ => Live (Machine.lifted.live (exit last)) r
      | _ => True := by
  cases last <;> simp only [finishAtoms, haltAtoms, loopAtoms, frameAtoms, commonAtoms,
    outputAtoms, inputAtoms, savedInputAtoms, stateAtoms, signedAtoms, List.forall_mem_append,
    List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  all_goals decide +kernel

theorem advances [Bindings] (last : Bool) {code : CodeMap}
    (hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    {initial : RamState} {fr : Activation} {controls : RamState} {p : Inputs} {s : LoopState} {boundary : ReturnBoundary}
    (hready : EntryReady code initial) (hrip : initial.RIP = 0x111eff)
    (hframe : RamWriteFrame fr.original initial.external [fr.region, outputRegion fr])
    (hout : ReturnOutside boundary code)
    (hlast : if last then s.remaining = batchCount s else batchCount s < s.remaining)
    (hcore : Atom.All code (Machine.lifted.locationOf .l1179df initial).arguments
      initial.external (CopyDE.updatedAtoms fr controls p s)) :
    ∃ fuel final, Advances boundary fuel initial final ∧ EntryReady code final ∧
      final.RIP = Machine.lifted.address (exit last) ∧
      RamWriteFrame fr.original final.external [fr.region, outputRegion fr] ∧
      Atom.All code (Machine.lifted.locationOf (exit last) final).arguments final.external
        (finishAtoms last fr controls p (nextState p s)) := by
  have hi : (layout last fr controls p).Rel code () ⟨.entry, #v[], s⟩
      (Machine.lifted.locationOf .l1179df initial) := by
    refine ⟨rfl, ⟨s, rfl, rfl, ?_⟩, hframe⟩
    change Atom.All code _ initial.external (CopyDE.updatedAtoms fr controls p s ++ [.fact _])
    rw [Atom.all_append]
    exact ⟨hcore, hlast, trivial⟩
  obtain ⟨loc, e, h⟩ := block last code fr controls p () #v[] s _ hi
  obtain ⟨s', _, hs, ha⟩ := h.params
  change s = s' at hs
  subst s'
  exact advance_to (entry := .l1179df) (exit := exit last) hcode hready hrip hout
    (e.reaches []) h.label ha h.frame (finish_live last fr controls p (nextState p s))

end P256.Proofs.Field.Inverse.SafeGcd.Core.Update.Finish
