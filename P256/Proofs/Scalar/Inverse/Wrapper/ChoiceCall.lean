import P256.Proofs.Scalar.Inverse.Wrapper.Defs

namespace P256.Proofs.Scalar.Inverse.Wrapper

open P256.Proofs.Field.Inverse.SafeGcd
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

namespace Choice

inductive Label where | entry

def program : Program Core.Support.Op Label (fun _ => 0) 0 where
  blocks _ := .terminate (.ret #v[])

def layout (fr : Activation) : Layout program dialect Machine.lifted Unit where
  start _ := .l126f60
  Params _ := Inputs
  args _ _ := #v[]
  store _ p := p
  atoms _ _ p := choiceCall fr p
  Result := Inputs
  output p := ⟨#v[], none, p⟩
  done _ p := choiceReturned fr p
  retAddr _ := 0x112e86
  original _ := fr.original
  regions _ := [fr.region, outputRegion fr]

attribute [local cfg_eval] Operand.read_reg_get

set_option maxHeartbeats 800000 in
theorem block (code : CodeMap) (hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    (fr : Activation) : (layout fr).BlockSimulation code .entry := by
  refine_intro
  refine_uir []
  all_goals refine_lifted []
  all_goals try refine_close []
  all_goals try wrapper_store fr mem hcode
  all_goals try
    apply RamWriteFrame.memStore
    · exact hframe
    · refine ⟨fr.region, by simp, ?_, ?_⟩
      all_goals simp only [Activation.region]
      all_goals bv_omega
  all_goals bv_omega

end Choice

theorem atoms_ret_locationOf [Bindings] {lifted : Lifted} {code : CodeMap}
    {lo : Output Value Ram Reg.count} {final : RamState} {l : lifted.Label}
    {atoms : List Atom} (hrel : Lift.RetRel code lifted lo final)
    (hlive : ∀ atom ∈ atoms, match atom with
      | .reg r _ | .low r _ _ => Live lifted.retLive r
      | _ => True)
    (hatoms : Atom.All code lo.values lo.store atoms) :
    Atom.All code (lifted.locationOf l final).arguments final.external atoms := by
  rw [hrel.store] at hatoms
  induction atoms with
  | nil => trivial
  | cons a atoms ih =>
    refine ⟨?_, ih (fun a ha => hlive a (List.mem_cons_of_mem _ ha)) hatoms.2⟩
    cases a with
    | reg r v =>
      have he := hrel.regs r r.isLt (hlive _ List.mem_cons_self)
      change (Vector.ofFn fun i : Fin Reg.count => (Reg.ofIndex i.val).read final)[r] = v
      rw [Fin.getElem_fin, Vector.getElem_ofFn]
      exact he.symm.trans hatoms.1
    | low r n v =>
      have he := hrel.regs r r.isLt (hlive _ List.mem_cons_self)
      change ((Vector.ofFn fun i : Fin Reg.count => (Reg.ofIndex i.val).read final)[r]).get n = v
      rw [Fin.getElem_fin, Vector.getElem_ofFn, ← he]
      exact hatoms.1
    | mem _ _ _ => simpa only [Atom.All, Atom.Holds] using hatoms.1
    | words _ _ _ => simpa only [Atom.All, Atom.Holds] using hatoms.1
    | readable _ _ => simpa only [Atom.All, Atom.Holds] using hatoms.1
    | writable _ _ => simpa only [Atom.All, Atom.Holds] using hatoms.1
    | fact _ => simpa only [Atom.All, Atom.Holds] using hatoms.1

theorem choice_stage [Bindings] {code : CodeMap}
    (hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    {initial : RamState} {fr : Activation} {p : Inputs} {boundary : ReturnBoundary}
    (hready : EntryReady code initial) (hrip : initial.RIP = 0x119070)
    (hframe : RamWriteFrame fr.original initial.external [fr.region, outputRegion fr])
    (hout : ReturnOutside boundary code)
    (hcore : Atom.All code (Machine.lifted.locationOf .l126f60 initial).arguments
      initial.external (choiceCall fr p)) :
    ∃ fuel final, Advances boundary fuel initial final ∧ EntryReady code final ∧
      final.RIP = 0x112e86 ∧
      RamWriteFrame fr.original final.external [fr.region, outputRegion fr] ∧
      Atom.All code (Machine.lifted.locationOf .l118966 final).arguments final.external
        (choiceReturned fr p) := by
  have hi : (Choice.layout fr).Rel code () ⟨.entry, #v[], p⟩
      (Machine.lifted.locationOf .l126f60 initial) := ⟨rfl, ⟨p, rfl, rfl, hcore⟩, hframe⟩
  have hb := Choice.block code hcode fr () #v[] p _ hi
  change Ahead Machine.lifted code _ _ at hb
  have decode (lo : Output Value Ram Reg.count) (final : RamState)
      (hq : (Choice.layout fr).RetRel code () ⟨#v[], none, p⟩ lo)
      (hrel : Lift.RetRel code Machine.lifted lo final) :
      final.RIP = 0x112e86 ∧
      RamWriteFrame fr.original final.external [fr.region, outputRegion fr] ∧
      Atom.All code (Machine.lifted.locationOf .l118966 final).arguments final.external
        (choiceReturned fr p) := by
    obtain ⟨htag, ⟨r, ho, hatoms⟩, hf⟩ := hq
    have hp : p = r := congrArg (fun o => o.store) ho
    subst r
    refine ⟨(Value.eq_bits (Option.some.inj (htag.symm.trans hrel.rip))).symm, ?_, ?_⟩
    · rwa [hrel.store] at hf
    · apply atoms_ret_locationOf (atoms := choiceReturned fr p) hrel ?_ hatoms
      simp only [choiceReturned, frameAtoms, outputAtoms, List.forall_mem_append,
        List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true, and_true]
      decide +kernel
  have hretCode : ∃ b, (0x112e86, b) ∈ code :=
    ⟨_, hcode _ (Machine.code_l118966 _ (mem_codeRange _ _ 0 (by decide)))⟩
  obtain ⟨fuel, final, lo, he, hrel, hq⟩ := Correction.Execution.ahead_return_advances
    (Machine.simulation code hcode hout)
    (Rel.locationOf (P := Machine.lifted) (l := .l126f60) hready hrip) hb
    (fun lo final hq hrel hboundary =>
      ReturnOutside.ne hout hretCode ((decode lo final hq hrel).1.symm.trans hboundary.1))
  exact ⟨fuel, final, he, ⟨hrel.ready, hrel.sse, hrel.code⟩, decode lo final hq hrel⟩

end P256.Proofs.Scalar.Inverse.Wrapper
