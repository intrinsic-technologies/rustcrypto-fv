import P256.Proofs.Common.Refine.Contract

namespace P256.Proofs.Field.Inverse.SafeGcd.FrameCompat

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift
  P256.Proofs.Refine Prelude

def entryRegs : List (Fin Reg.count × Nat) :=
  [(1, 1), (2, 2), (3, 3), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13),
    (14, 14), (15, 15)]

def entryFrame (m : FrameInfo) : LabelFrame := ⟨0, entryRegs, [], m.callSlots⟩

def entryAtoms (m : FrameInfo) (fr : Activation) : List Atom :=
  m.frameAtoms (entryFrame m) fr

def doneAtoms (m : FrameInfo) (fr : Activation) : List Atom :=
  .gpr 4 (fr.rsp + 8) :: .reg 22 ⟨1, 0⟩ :: (m.preserved.map fun r => .gpr r (fr.entryReg r))

structure Pre (m : FrameInfo) (code : CodeMap) (fr : Activation) (s : RamState) :
    Prop where
  rip : s.RIP = m.entry
  original : s.external = fr.original
  regs : ∀ r ∈ Activation.entryNumbers, (Reg.ofIndex r).read s = ⟨64, fr.entryReg r⟩
  ret : memLoad fr.original fr.rsp 64 = fr.ret
  retLow : fr.ret.toNat < 2 ^ 32
  retOutside : ∀ x ∈ code, x.1 ≠ fr.ret
  slot : Readable fr.original fr.rsp 8
  window : 0 < m.window →
    Writable code fr.original (fr.rsp - BitVec.ofNat 64 m.window) m.window
  room : fr.low.toNat + m.window ≤ fr.rsp.toNat
  align : fr.rsp.toNat % 16 = 8
  callSlots : ∀ c ∈ m.callSlots, Readable fr.original c.1 8 ∧ memLoad fr.original c.1 64 = c.2
  callSlotsApart : m.callSlots ≠ [] → FrameInfo.slotsHigh m.callSlots + m.window ≤
    fr.rsp.toNat ∨ fr.rsp.toNat ≤ FrameInfo.slotsLow m.callSlots
  df : RFLAGS.DirectionFlagClear s.RFLAGS

structure Post (m : FrameInfo) (fr : Activation) (footprint : List MemoryRegion)
    (t : RamState) : Prop where
  rip : t.RIP = fr.ret
  rsp : (Reg.ofIndex 4).read t = ⟨64, fr.rsp + 8⟩
  preserved : ∀ r ∈ m.preserved, (Reg.ofIndex r).read t = ⟨64, fr.entryReg r⟩
  df : RFLAGS.DirectionFlagClear t.RFLAGS
  frame : RamWriteFrame fr.original t.external (fr.region :: footprint)

section Entry

variable {m : FrameInfo} {code : CodeMap} {fr : Activation} {s : RamState}

theorem Pre.stackPtr_eq (h : Pre m code fr s) : stackPtr s = fr.rsp :=
  Value.eq_bits (h.regs 4 (by decide))

theorem Pre.stackAtoms (h : Pre m code fr s) (args : Values Value Reg.count) :
    Atom.All code args s.external (m.stackAtoms fr) := by
  unfold FrameInfo.stackAtoms
  rw [Atom.all_append, Atom.all_append, h.original]
  refine ⟨⟨⟨h.slot, h.ret, h.retLow, trivial⟩, ?_⟩, h.align, trivial⟩
  have hroom := h.room
  split
  · exact ⟨show fr.low.toNat ≤ fr.rsp.toNat by omega, trivial⟩
  · exact ⟨h.window (by omega), hroom, trivial⟩

theorem Pre.callSlotAtoms (h : Pre m code fr s) (args : Values Value Reg.count) :
    Atom.All code args s.external (m.callSlotAtoms m.callSlots fr) := by
  have hslots : ∀ cs : List (BitVec 64 × BitVec 64), (∀ c ∈ cs, c ∈ m.callSlots) →
      Atom.All code args s.external
        (cs.flatMap fun c => [.readable c.1 8, .mem c.1 64 c.2]) := by
    intro cs
    induction cs with
    | nil => intro _; trivial
    | cons c cs ih =>
      intro hc
      rw [List.flatMap_cons, Atom.all_append]
      obtain ⟨hr, hv⟩ := h.callSlots c (hc c List.mem_cons_self)
      rw [h.original]
      exact ⟨⟨hr, hv, trivial⟩, h.original ▸ ih fun x hx => hc x (List.mem_cons_of_mem c hx)⟩
  unfold FrameInfo.callSlotAtoms
  split
  · trivial
  · rename_i heq
    rw [Atom.all_append]
    exact ⟨hslots _ fun _ hx => hx,
      h.callSlotsApart (by rw [heq]; exact List.cons_ne_nil _ _), trivial⟩

theorem Pre.entryAtoms (h : Pre m code fr s) (lifted : Lifted) (l : lifted.Label) :
    Atom.All code (lifted.locationOf l s).arguments s.external (entryAtoms m fr) := by
  have hr : ∀ r ∈ Activation.entryNumbers, ∀ hr : r < Reg.count,
      (lifted.locationOf l s).arguments[r] = ⟨64, fr.entryReg r⟩ := fun r hm _ =>
    (Vector.getElem_ofFn _).trans (h.regs r hm)
  unfold FrameCompat.entryAtoms FrameInfo.frameAtoms FrameCompat.entryFrame
  rw [Atom.all_append, Atom.all_append, Atom.all_append]
  refine ⟨⟨⟨⟨hr 4 (by decide) (by decide), (Vector.getElem_ofFn _).trans (Reg.read_df_iff.2 h.df),
    ?_⟩, trivial⟩, h.stackAtoms _⟩, h.callSlotAtoms _⟩
  simp only [entryRegs, List.map_cons, List.map_nil, Atom.All, Atom.Holds]
  exact ⟨hr 1 (by decide) (by decide), hr 2 (by decide) (by decide),
    hr 3 (by decide) (by decide), hr 5 (by decide) (by decide), hr 6 (by decide) (by decide),
    hr 7 (by decide) (by decide), hr 8 (by decide) (by decide), hr 9 (by decide) (by decide),
    hr 12 (by decide) (by decide), hr 13 (by decide) (by decide),
    hr 14 (by decide) (by decide), hr 15 (by decide) (by decide), trivial⟩

theorem Pre.memReadable (h : Pre m code fr s) : MemReadable s (stackPtr s) 8 := by
  rw [h.stackPtr_eq]
  have hslot := h.slot
  rw [← h.original] at hslot
  exact ⟨hslot.low, fun i hi => hslot.present i hi⟩

theorem Pre.returnBoundary (h : Pre m code fr s) :
    (returnBoundary s).rip = fr.ret ∧ (returnBoundary s).rsp = fr.rsp + 8 := by
  refine ⟨?_, by simp only [X86Proofs.returnBoundary, h.stackPtr_eq]⟩
  show memLoad s.external (stackPtr s) 64 = fr.ret
  rw [h.stackPtr_eq, h.original, h.ret]

end Entry

theorem doneAtoms_retRel [Bindings] {code : CodeMap} {lifted : Lifted} {m : FrameInfo}
    {fr : Activation} {lo : Output Value Ram Reg.count} {t : RamState}
    (hrel : RetRel code lifted lo t)
    (h : Atom.All code lo.values lo.store (doneAtoms m fr))
    (hlive : ∀ r ∈ [4, 22] ++ m.preserved.map Fin.val, Live lifted.retLive r) :
    (Reg.ofIndex 4).read t = ⟨64, fr.rsp + 8⟩ ∧ RFLAGS.DirectionFlagClear t.RFLAGS ∧
      ∀ r ∈ m.preserved, (Reg.ofIndex r).read t = ⟨64, fr.entryReg r⟩ := by
  obtain ⟨h4, h22, hp⟩ := h
  have hread : ∀ r : Fin Reg.count, r.val ∈ [4, 22] ++ m.preserved.map Fin.val →
      lo.values[r] = (Reg.ofIndex r).read t := fun r hr =>
    hrel.regs r r.isLt (hlive r hr)
  refine ⟨(hread 4 (List.mem_append_left _ (by decide))).symm.trans h4,
    Reg.read_df_iff.1 ((hread 22 (List.mem_append_left _ (by decide))).symm.trans h22),
    fun r hr => ?_⟩
  have hall : ∀ rs : List (Fin Reg.count), (∀ r ∈ rs, r ∈ m.preserved) →
      Atom.All code lo.values lo.store (rs.map fun r => .gpr r (fr.entryReg r)) →
      ∀ r ∈ rs, (Reg.ofIndex r).read t = ⟨64, fr.entryReg r⟩ := by
    intro rs
    induction rs with
    | nil => intro _ _ _ h; exact absurd h List.not_mem_nil
    | cons r rs ih =>
      intro hsub ha x hx
      obtain ⟨hx0, hrest⟩ := ha
      rcases List.mem_cons.1 hx with rfl | hx
      · exact (hread x (List.mem_append_right _ (List.mem_map_of_mem
          (hsub x List.mem_cons_self)))).symm.trans hx0
      · exact ih (fun y hy => hsub y (List.mem_cons_of_mem r hy)) hrest x hx
  exact hall m.preserved (fun _ h => h) hp r hr

variable {UOp : Nat → Type} {ULabel UValue UStore : Type} {usig : ULabel → Nat} {results : Nat}
  {P : Program UOp ULabel usig results} {D : Dialect UOp UValue UStore} {lifted : Lifted}
  {Ctx : Type}

theorem withFrame_routine [bindings : Bindings] {m : FrameInfo}
    {frameAt : lifted.Label → Activation → List Atom} {doneAt : Activation → List Atom}
    (core : LayoutCore P D lifted Ctx) {code : CodeMap} {initial : RamState} {fr : Activation}
    {c : Ctx}
    {n : Nat} {regions : Vector MemoryRegion n} {entry : lifted.Label}
    (hready : EntryReady code initial) (hpre : Pre m code fr initial)
    (hlifted : ReturnOutside (returnBoundary initial) code →
      Simulation (machineAnyReturn (returnBoundary initial)) (lifted.program.sem (dialect code))
        (Lift.Rel code lifted) (Lift.RetRel code lifted))
    (blocks : ∀ label, (Layout.withFrame frameAt doneAt core).BlockSimulation code label)
    (hregions : ∀ x, (∀ r ∈ regions, ¬ r.Contains x) →
      ∀ r ∈ fr.region :: core.footprint c fr, ¬ r.Contains x)
    {lab : ULabel} {p : core.Params lab} {o : Output UValue UStore results}
    (hexec : P.Exec D ⟨⟨lab, core.args lab p, core.store lab p⟩, []⟩ o)
    (hcore : Atom.All code (lifted.locationOf entry initial).arguments initial.external
      (core.atoms lab c fr p))
    (hstart : core.start lab = entry) (hentry : ∀ fr, frameAt entry fr = entryAtoms m fr)
    (hdone : ∀ fr, doneAt fr = doneAtoms m fr) (haddr : lifted.address entry = m.entry)
    (hlive : ∀ r ∈ [4, 22] ++ m.preserved.map Fin.val, Live lifted.retLive r) :
    RoutineResult bindings initial regions fun t => Post m fr (core.footprint c fr) t ∧
      ∃ r, o = core.output r ∧ ∃ lo, Lift.RetRel code lifted lo t ∧
        Atom.All code lo.values lo.store (core.done c fr r) := by
  let L := Layout.withFrame frameAt doneAt core
  have hb := hpre.returnBoundary
  have hout : ReturnOutside (returnBoundary initial) code :=
    fun x hx he => hpre.retOutside x hx (he.trans hb.1)
  have hret : ∀ (o : Output UValue UStore results) (t : RamState),
      (∃ lo, L.RetRel code (fr, c) o lo ∧ Lift.RetRel code lifted lo t) →
        Post m fr (core.footprint c fr) t ∧ ∃ r, o = core.output r ∧ ∃ lo,
          Lift.RetRel code lifted lo t ∧ Atom.All code lo.values lo.store (core.done c fr r) := by
    rintro o t ⟨lo, ⟨htag, ⟨r, ho, hatoms⟩, hframe⟩, hrel⟩
    have hatoms' : Atom.All code lo.values lo.store (doneAt fr ++ core.done c fr r) := hatoms
    rw [hdone, Atom.all_append] at hatoms'
    obtain ⟨hrsp, hdf, hpres⟩ := doneAtoms_retRel hrel hatoms'.1 hlive
    have hrip : t.RIP = fr.ret := by
      have h := htag.symm.trans hrel.rip
      exact (Value.eq_bits (Option.some.inj h)).symm
    have hframe' : RamWriteFrame fr.original t.external (fr.region :: core.footprint c fr) := by
      rw [← hrel.store]
      exact hframe
    exact ⟨⟨hrip, hrsp, hpres, hdf, hframe'⟩, r, ho, lo, hrel, hatoms'.2⟩
  have simM := (Simulation.toMachine ((hlifted hout).trans (L.simulation code (fr, c) blocks))
    (fun o t h => by
      obtain ⟨hpost, -⟩ := hret o t (let ⟨lo, h₁, h₂⟩ := h; ⟨lo, h₁, h₂⟩)
      refine ⟨hpost.rip.trans hb.1.symm, ?_⟩
      exact (Value.eq_bits hpost.rsp).trans hb.2.symm)).mono
    (post' := fun (o : Output UValue UStore results) (t : RamState) =>
      MachineInvariant initial regions t ∧ (Post m fr (core.footprint c fr) t ∧
        ∃ r, o = core.output r ∧ ∃ lo, Lift.RetRel code lifted lo t ∧
          Atom.All code lo.values lo.store (core.done c fr r)))
    (by
      rintro o t ⟨lo, h₁, h₂⟩
      have h := hret o t ⟨lo, h₁, h₂⟩
      refine ⟨⟨h₂.ready, h₂.sse, ?_, h.1.df⟩, h⟩
      exact RamWriteFrame.memoryWriteFrame (hpre.original ▸ h.1.frame) hregions)
  have hnear : nearReturn64Boundary initial = .ok (returnBoundary initial) :=
    nearReturn64Boundary_eq initial hready.ready.dataReady hready.ready.cpu.ss hpre.memReadable
  refine RoutineResult.of_simulation hnear simM hexec.sem
    ⟨⟨lifted.locationOf entry initial, []⟩, ⟨(fr, c), ⟨hstart.symm, ⟨p, rfl, rfl, ?_⟩, ?_⟩, rfl⟩,
      Rel.locationOf hready (hpre.rip.trans haddr.symm)⟩
  · show Atom.All code (lifted.locationOf entry initial).arguments initial.external
      (frameAt (core.start lab) fr ++ core.atoms lab c fr p)
    rw [hstart, hentry, Atom.all_append]
    exact ⟨hpre.entryAtoms lifted entry, hcore⟩
  · show RamWriteFrame fr.original initial.external _
    rw [← hpre.original]
    exact RamWriteFrame.refl _ _

theorem withFrame_call {m : FrameInfo} {frameAt : lifted.Label → Activation → List Atom}
    {doneAt : Activation → List Atom} {core : LayoutCore P D lifted Ctx} {code : CodeMap}
    (blocks : ∀ label, (Layout.withFrame frameAt doneAt core).BlockSimulation code label)
    {u : Location UValue UStore ULabel usig} {o : Output UValue UStore results}
    (hexec : P.Exec D ⟨u, []⟩ o) (fr : Activation) (c : Ctx) {l : lifted.Location}
    (hrel : (Layout.withFrame frameAt doneAt core).Rel code (fr, c) u l)
    (hdone : ∀ fr, doneAt fr = doneAtoms m fr) :
    ∃ lo, lifted.program.Exec (dialect code) ⟨l, []⟩ lo ∧
      (Layout.withFrame frameAt doneAt core).RetRel code (fr, c) o lo ∧
        Atom.All code lo.values lo.store (doneAtoms m fr) := by
  obtain ⟨lo, he, hr⟩ := ((Layout.withFrame frameAt doneAt core).simulation code (fr, c)
    blocks).exec hexec.sem (a := ⟨l, []⟩) ⟨(fr, c), hrel, rfl⟩
  refine ⟨lo, Program.Exec.of_sem he, hr, ?_⟩
  obtain ⟨-, ⟨r, -, hatoms⟩, -⟩ := hr
  have hatoms' : Atom.All code lo.values lo.store (doneAt fr ++ core.done c fr r) := hatoms
  rw [hdone, Atom.all_append] at hatoms'
  exact hatoms'.1

end P256.Proofs.Field.Inverse.SafeGcd.FrameCompat
