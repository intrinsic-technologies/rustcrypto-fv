import P256.Proofs.Field.Inverse.SafeGcd.Core.Tail.Defs

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.Tail.Prefix

open Shared (zeroWords correctionInput)

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

inductive Label where | entry | callee | finish

@[refine_layout] def start : Label → Machine.Label
  | .entry => .l117be8 | .callee => .l1181a0 | .finish => .l117c2f

def program : Program Support.Op Label (fun _ => 0) 0 where
  blocks
  | .entry => .terminate (.call ⟨.callee, #v[]⟩ {target := .finish, kept := #v[], arity := rfl})
  | _ => .terminate (.ret #v[])

def dialect : Dialect Support.Op Unit LoopState where
  eval op := nomatch op
  truth _ := false

@[refine_layout] def atoms (l : Label) (fr : Activation) (controls : RamState) (p : Inputs) (s : LoopState) : List Atom :=
  match l with
  | .entry => Update.Finish.haltAtoms fr controls p s
  | .callee => callAtoms fr controls p s
  | .finish => []

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
  have hbyte := Common.Field.SquareRoot.memLoad_setWidth_of_le mem (fr.rsp - 272)
    (m := 32) (n := 8) (by decide) (by decide)
  have hlow : ((memLoad mem (fr.rsp - 272) 32).setWidth 64).setWidth 8 = f.sign := by
    have hx : ((memLoad mem (fr.rsp - 272) 32).setWidth 64).setWidth 8 =
        (memLoad mem (fr.rsp - 272) 32).setWidth 8 := by bv_omega
    rw [hx, hbyte]
    simpa only [show fr.rsp - 304 + 32 = fr.rsp - 272 by bv_omega] using atom42
  refine_uir []
  all_goals refine_lifted [nonzeroByte, zeroWords, BitVec.or_comm p.a[1] p.a[0], hlow]
  all_goals first
    | (refine ⟨(), ?_, ?_⟩
       all_goals first
         | (intro uo lo hret _
            obtain ⟨_, ⟨r, _⟩, _⟩ := hret
            cases r)
         | refine_close [nonzeroByte, zeroWords, hlow])
    | skip
  all_goals try simp only [cfg_eval, BitVec.reduceSetWidth, BitVec.reduceSignExtend,
    BitVec.reduceEq, ite_false, ite_true, Value.get_mk_setWidth, BitVec.setWidth_eq]
  all_goals try ct_core_stack_store fr mem _hcode
  all_goals try bv_omega
  all_goals try first
    | (simpa only [show fr.rsp - 304 + 32 = fr.rsp - 272 by bv_omega] using atom42)
    | (simpa only [show fr.rsp - 216 + 32 = fr.rsp - 184 by bv_omega] using atom46)
  all_goals try simp only [setWidth_mergeGPR8, orFlags, Option.getD_some,
    BitVec.or_comm p.a[1] p.a[0]]
  all_goals split <;> simp_all only [Bool.beq_eq_decide_eq, decide_eq_false_iff_not,
    Classical.not_not, ite_true, ite_false]

theorem call_live (fr : Activation) (controls : RamState) (p : Inputs) (s : LoopState) :
    ∀ atom ∈ callAtoms fr controls p s, match atom with
      | .reg r _ | .low r _ _ => Live (Machine.lifted.live .l1181a0) r
      | _ => True := by
  simp only [callAtoms, residentAtoms, savedAtoms, outputAtoms, signedAtoms,
    List.forall_mem_append, List.forall_mem_cons, List.not_mem_nil,
    false_implies, implies_true, and_true]
  decide +kernel

theorem advances [Bindings] {code : CodeMap}
    (hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    {initial : RamState} {fr : Activation} {controls : RamState} {p : Inputs} {s : LoopState} {boundary : ReturnBoundary}
    (hready : EntryReady code initial) (hrip : initial.RIP = 0x112108)
    (hframe : RamWriteFrame fr.original initial.external [fr.region, outputRegion fr])
    (hout : ReturnOutside boundary code)
    (hcore : Atom.All code (Machine.lifted.locationOf .l117be8 initial).arguments
      initial.external (atoms .entry fr controls p s)) :
    ∃ fuel final, Advances boundary fuel initial final ∧ EntryReady code final ∧
      final.RIP = 0x1126c0 ∧ RamWriteFrame fr.original final.external [fr.region, outputRegion fr] ∧
      Atom.All code (Machine.lifted.locationOf .l1181a0 final).arguments final.external
        (callAtoms fr controls p s) := by
  have hi : (layout fr controls p).Rel code () ⟨.entry, #v[], s⟩
      (Machine.lifted.locationOf .l117be8 initial) := ⟨rfl, ⟨s, rfl, rfl, hcore⟩, hframe⟩
  have sim := Machine.simulation code hcode hout
  have hb := block code hcode fr controls p () #v[] s _ hi
  change Ahead Machine.lifted code _ _ at hb
  obtain ⟨fuel, final, callee, frame, he, hrel, c', hcall, _⟩ :=
    Support.ahead_call_advances sim
      (Rel.locationOf (P := Machine.lifted) (l := .l117be8) hready hrip) hb
  obtain ⟨s', _, hs, hatoms⟩ := hcall.params
  change s = s' at hs
  subst s'
  have hlabel : callee.label = .l1181a0 := hcall.label
  change Atom.All code callee.arguments callee.store (callAtoms fr controls p s) at hatoms
  rw [hrel.store] at hatoms
  have ha := Support.atoms_locationOf hrel (by
    intro atom hh
    have hh := call_live fr controls p s atom hh
    cases atom with
    | reg _ _ => simpa only [hlabel] using hh
    | low _ _ _ => simpa only [hlabel] using hh
    | mem _ _ _ => trivial
    | words _ _ _ => trivial
    | readable _ _ => trivial
    | writable _ _ => trivial
    | fact _ => trivial) hatoms
  rw [hlabel] at ha
  have hf := hcall.frame
  rw [hrel.store] at hf
  exact ⟨fuel, final, he, ⟨hrel.ready, hrel.sse, hrel.code⟩,
    by rw [hrel.rip, hlabel]; rfl, hf, ha⟩

end P256.Proofs.Field.Inverse.SafeGcd.Core.Tail.Prefix
