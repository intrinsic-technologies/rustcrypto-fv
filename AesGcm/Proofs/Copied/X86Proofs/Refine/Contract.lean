import AesGcm.Proofs.Copied.X86Proofs.Refine.Simulation
import AesGcm.Proofs.Copied.X86Proofs.Refine.Lemma.Frame
import AesGcm.Proofs.Copied.X86Proofs.Refine.Lemma.Store

namespace X86Proofs.Refine

open X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift Prelude
  Prelude.Execution.CallingConvention

variable {UOp : Nat → Type} {ULabel UValue UStore : Type} {usig : ULabel → Nat} {results : Nat}
  {P : Program UOp ULabel usig results} {D : Dialect UOp UValue UStore} {lifted : Lifted}
  {Ctx : Type}

theorem Layout.withFrame_routine [bindings : Bindings] {m : FrameInfo}
    {frameAt : lifted.Label → Activation → List Atom} {doneAt : Activation → List Atom}
    (core : LayoutCore P D lifted Ctx) {code : CodeMap} {initial : RamState} {fr : Activation}
    {c : Ctx}
    {n : Nat} {regions : Vector MemoryRegion n} {entry : lifted.Label}
    (hready : EntryReady code initial) (hpre : m.Pre code fr initial)
    (liftedBlocks : ∀ l, LiftedBlock code lifted l)
    (blocks : ∀ label, (Layout.withFrame frameAt doneAt core).BlockSimulation code label)
    (hregions : ∀ x, (∀ r ∈ regions, ¬ r.Contains x) →
      ∀ r ∈ fr.region :: core.footprint c fr, ¬ r.Contains x)
    {lab : ULabel} {p : core.Params lab} {o : Output UValue UStore results}
    (hexec : P.Exec D ⟨⟨lab, core.args lab p, core.store lab p⟩, []⟩ o)
    (hcore : Atom.All code (lifted.locationOf entry initial).arguments initial.external
      (core.atoms lab c fr p))
    (hstart : core.start lab = entry) (hentry : ∀ fr, frameAt entry fr = m.entryAtoms fr)
    (hdone : ∀ fr, doneAt fr = m.doneAtoms fr) (haddr : lifted.address entry = m.entry)
    (hfp : m.fpPreserved = [39, 50, 51])
    (hpreserved : ∀ r : Fin Reg.count, r.val ∈ Activation.calleeSavedNumbers → r ∈ m.preserved)
    (hlive : ∀ r ∈ [4, 22, 39, 50, 51] ++ m.preserved.map Fin.val, Live lifted.retLive r) :
    RoutineResult bindings initial regions fun t => SysVCalleeReturn initial t fr.ret ∧
      m.Post fr (core.footprint c fr) t ∧ ∃ r, o = core.output r ∧ ∃ lo,
        Lift.RetRel code lifted lo t ∧ Atom.All code lo.values lo.store (core.done c fr r) := by
  let L := Layout.withFrame frameAt doneAt core
  have hb := hpre.returnBoundary
  have hout : ReturnOutside (returnBoundary initial) code :=
    fun x hx he => hpre.retOutside x hx (he.trans hb.1)

  have hret : ∀ (o : Output UValue UStore results) (t : RamState),
      (∃ lo, L.RetRel code (fr, c) o lo ∧ Lift.FixedRetRel code lifted initial lo t) →
        SysVCalleeReturn initial t fr.ret ∧ m.Post fr (core.footprint c fr) t ∧
          ∃ r, o = core.output r ∧ ∃ lo, Lift.RetRel code lifted lo t ∧
            Atom.All code lo.values lo.store (core.done c fr r) := by
    rintro o t ⟨lo, ⟨htag, ⟨r, ho, hatoms⟩, hframe⟩, ⟨hrel, hfixed⟩⟩
    have hatoms' : Atom.All code lo.values lo.store (doneAt fr ++ core.done c fr r) := hatoms
    rw [hdone, Atom.all_append] at hatoms'
    obtain ⟨hrsp, hdf, hpres, hmxcsr, hftw, hfcw⟩ := doneAtoms_retRel hrel hatoms'.1 hfp hlive
    have hrip : t.RIP = fr.ret := by
      have h := htag.symm.trans hrel.rip
      exact (Value.eq_bits (Option.some.inj h)).symm
    have hframe' : RamWriteFrame fr.original t.external (fr.region :: core.footprint c fr) := by
      rw [← hrel.store]
      exact hframe
    have hcontrol : mxcsrControlBits (((Reg.ofIndex 39).read t).get 32) =
        mxcsrControlBits fr.mxcsr := by
      rw [hmxcsr]
      simp only [Value.get, BitVec.setWidth_eq]

    have hfs : t.FS = initial.FS := congrArg (·.FS) hfixed
    have hpost : m.Post fr (core.footprint c fr) t :=
      ⟨hrip, hrsp, hpres, hdf, hcontrol, hftw, hfcw, hfs.trans hpre.fs, hframe'⟩
    exact ⟨hpost.sysVCalleeReturn hpre hpreserved, hpost, r, ho, lo, hrel, hatoms'.2⟩
  have simM := (Simulation.toMachine ((Lifted.simulationFixed liftedBlocks hout initial).trans
      (L.simulation code (fr, c) blocks))
    (fun o t h => by
      obtain ⟨-, hpost, -⟩ := hret o t (let ⟨lo, h₁, h₂⟩ := h; ⟨lo, h₁, h₂⟩)
      refine ⟨hpost.rip.trans hb.1.symm, ?_⟩
      exact (Value.eq_bits hpost.rsp).trans hb.2.symm)).mono
    (post' := fun (o : Output UValue UStore results) (t : RamState) =>
      MachineInvariant initial regions t ∧ (SysVCalleeReturn initial t fr.ret ∧
        m.Post fr (core.footprint c fr) t ∧ ∃ r, o = core.output r ∧ ∃ lo,
          Lift.RetRel code lifted lo t ∧ Atom.All code lo.values lo.store (core.done c fr r)))
    (by
      rintro o t ⟨lo, h₁, h₂⟩
      have h := hret o t ⟨lo, h₁, h₂⟩
      refine ⟨⟨h₂.rel.ready, h₂.rel.sse, ?_, h.2.1.df⟩, h⟩
      exact RamWriteFrame.memoryWriteFrame (hpre.original ▸ h.2.1.frame) hregions)
  have hnear : nearReturn64Boundary initial = .ok (returnBoundary initial) :=
    nearReturn64Boundary_eq initial hready.ready.dataReady hready.ready.cpu.ss hpre.memReadable
  refine RoutineResult.of_simulation hnear simM hexec.sem
    ⟨⟨lifted.locationOf entry initial, []⟩, ⟨(fr, c), ⟨hstart.symm, ⟨p, rfl, rfl, ?_⟩, ?_⟩, rfl⟩,
      ⟨Rel.locationOf hready (hpre.rip.trans haddr.symm), rfl⟩⟩
  · show Atom.All code (lifted.locationOf entry initial).arguments initial.external
      (frameAt (core.start lab) fr ++ core.atoms lab c fr p)
    rw [hstart, hentry, Atom.all_append]
    exact ⟨hpre.entryAtoms lifted entry, hcore⟩
  · show RamWriteFrame fr.original initial.external _
    rw [← hpre.original]
    exact RamWriteFrame.refl _ _

theorem Layout.withFrame_call {m : FrameInfo} {frameAt : lifted.Label → Activation → List Atom}
    {doneAt : Activation → List Atom} {core : LayoutCore P D lifted Ctx} {code : CodeMap}
    (blocks : ∀ label, (Layout.withFrame frameAt doneAt core).BlockSimulation code label)
    {u : Location UValue UStore ULabel usig} {o : Output UValue UStore results}
    (hexec : P.Exec D ⟨u, []⟩ o) (fr : Activation) (c : Ctx) {l : lifted.Location}
    (hrel : (Layout.withFrame frameAt doneAt core).Rel code (fr, c) u l)
    (hdone : ∀ fr, doneAt fr = m.doneAtoms fr) :
    ∃ lo, lifted.program.Exec (dialect code) ⟨l, []⟩ lo ∧
      (Layout.withFrame frameAt doneAt core).RetRel code (fr, c) o lo ∧
        Atom.All code lo.values lo.store (m.doneAtoms fr) := by
  obtain ⟨lo, he, hr⟩ := ((Layout.withFrame frameAt doneAt core).simulation code (fr, c)
    blocks).exec hexec.sem (a := ⟨l, []⟩) ⟨(fr, c), hrel, rfl⟩
  refine ⟨lo, Program.Exec.of_sem he, hr, ?_⟩
  obtain ⟨-, ⟨r, -, hatoms⟩, -⟩ := hr
  have hatoms' : Atom.All code lo.values lo.store (doneAt fr ++ core.done c fr r) := hatoms
  rw [hdone, Atom.all_append] at hatoms'
  exact hatoms'.1

end X86Proofs.Refine
