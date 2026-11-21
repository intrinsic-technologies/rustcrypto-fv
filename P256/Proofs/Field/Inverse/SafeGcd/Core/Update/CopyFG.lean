import P256.Proofs.Field.Inverse.SafeGcd.Core.Update.SecondDefs

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.Update.CopyFG

open Shared (batchCount batchResult fInput gInput linearInput)
open Support (MemoryStable atoms_of_frame)

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

def fgState (s : LoopState) : LoopState := { s with
  f := ⟨LinearShift.shiftedWords (fInput s), LinearShift.resultSign (fInput s)⟩
  g := ⟨LinearShift.shiftedWords (gInput s), LinearShift.resultSign (gInput s)⟩ }

@[refine_layout] def updatedAtoms (fr : Activation) (controls : RamState) (p : Inputs) (s : LoopState) : List Atom :=
  memoryAtoms fr p (fgState s) ++ bounds s ++ preservedAtoms fr controls s (fr.rsp - 0x188)

inductive Label where | entry | finish

@[refine_layout] def start : Label → Machine.Label
  | .entry => .l117849 | .finish => .l1178bb

def program : Program Support.Op Label (fun _ => 0) 0 where
  blocks
  | .entry => .terminate (.br ⟨.finish, #v[]⟩)
  | .finish => .terminate (.ret #v[])

def dialect : Dialect Support.Op Unit LoopState where
  eval op := nomatch op
  truth _ := false

@[refine_layout] def atoms (l : Label) (fr : Activation) (controls : RamState) (p : Inputs) (s : LoopState) : List Atom :=
  match l with
  | .entry => secondReturned fr controls p s
  | .finish => updatedAtoms fr controls p s

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
set_option maxHeartbeats 1500000 in
theorem block (code : CodeMap) (_hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    (fr : Activation) (controls : RamState) (p : Inputs) : (layout fr controls p).BlockSimulation code .entry := by
  refine_intro
  try simp only [show fr.rsp - 304 + 32 = fr.rsp - 272 by bv_omega,
    show fr.rsp - 256 + 32 = fr.rsp - 224 by bv_omega,
    show fr.rsp - 216 + 32 = fr.rsp - 184 by bv_omega,
    show fr.rsp - 176 + 32 = fr.rsp - 144 by bv_omega] at *
  refine_uir []
  all_goals refine_lifted [fgState, batchCount]
  all_goals try refine_close [fgState, batchCount]
  all_goals try simp only [cfg_eval, BitVec.reduceSetWidth, BitVec.reduceSignExtend,
    BitVec.reduceEq, ite_false, ite_true, Value.get_mk_setWidth, BitVec.setWidth_eq]
  all_goals try ct_core_stack_store fr mem _hcode
  all_goals try bv_omega

theorem finish_live (fr : Activation) (controls : RamState) (p : Inputs) (s : LoopState) :
    ∀ a ∈ updatedAtoms fr controls p s, match a with
      | .reg r _ | .low r _ _ => Live (Machine.lifted.live .l1178bb) r
      | _ => True := by
  simp only [updatedAtoms, memoryAtoms, bounds, preservedAtoms, commonAtoms, outputAtoms,
    inputAtoms, savedInputAtoms, stateAtoms, signedAtoms, List.forall_mem_append,
    List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
  decide +kernel

theorem advances [Bindings] {code : CodeMap}
    (hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    {initial : RamState} {fr : Activation} {controls : RamState} {p : Inputs} {s : LoopState} {boundary : ReturnBoundary}
    (hready : EntryReady code initial) (hrip : initial.RIP = 0x111d69)
    (hframe : RamWriteFrame fr.original initial.external [fr.region, outputRegion fr])
    (hout : ReturnOutside boundary code)
    (hcore : Atom.All code (Machine.lifted.locationOf .l117849 initial).arguments
      initial.external (secondReturned fr controls p s)) :
    ∃ fuel final, Advances boundary fuel initial final ∧ EntryReady code final ∧
      final.RIP = 0x111ddb ∧ RamWriteFrame fr.original final.external [fr.region, outputRegion fr] ∧
      Atom.All code (Machine.lifted.locationOf .l1178bb final).arguments final.external
        (updatedAtoms fr controls p s) := by
  have hi : (layout fr controls p).Rel code () ⟨.entry, #v[], s⟩
      (Machine.lifted.locationOf .l117849 initial) := ⟨rfl, ⟨s, rfl, rfl, hcore⟩, hframe⟩
  obtain ⟨loc, e, h⟩ := block code hcode fr controls p () #v[] s _ hi
  obtain ⟨s', _, hs, ha⟩ := h.params
  change s = s' at hs
  subst s'
  exact advance_to (entry := .l117849) (exit := .l1178bb) hcode hready hrip hout
    (e.reaches []) h.label ha h.frame (finish_live fr controls p s)

end P256.Proofs.Field.Inverse.SafeGcd.Core.Update.CopyFG
