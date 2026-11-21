import P256.Proofs.Common.Refine.Frame
import Prelude.Execution.CallingConvention
import P256.Proofs.Common.Refine.Lemma.Layout
import P256.Proofs.Common.Refine.Lemma.Region
import P256.Proofs.Common.Lift.Simulation

namespace P256.Proofs.Refine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift Prelude
  Prelude.Execution.CallingConvention

section Entry

variable {m : FrameInfo} {code : CodeMap} {fr : Activation} {s : RamState}

theorem FrameInfo.Pre.stackPtr_eq (h : m.Pre code fr s) : stackPtr s = fr.rsp :=
  Value.eq_bits (h.regs 4 (by decide))

theorem FrameInfo.Pre.stackAtoms (h : m.Pre code fr s) (args : Values Value Reg.count) :
    Atom.All code args s.external (m.stackAtoms fr) := by
  unfold FrameInfo.stackAtoms
  rw [Atom.all_append, Atom.all_append, h.original]
  refine ⟨⟨⟨h.slot, h.ret, h.retLow, trivial⟩, ?_⟩, h.align, trivial⟩
  have hroom := h.room
  split
  · exact ⟨show fr.low.toNat ≤ fr.rsp.toNat by omega, trivial⟩
  · exact ⟨h.window (by omega), hroom, trivial⟩

theorem FrameInfo.Pre.callSlotAtoms (h : m.Pre code fr s) (args : Values Value Reg.count) :
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

theorem FrameInfo.Pre.gpr (h : m.Pre code fr s) {lifted : Lifted} {l : lifted.Label}
    (r : Fin Reg.count) (hr : r.val ∈ Activation.entryNumbers := by decide) :
    (Atom.gpr r (fr.entryReg r)).Holds code (lifted.locationOf l s).arguments s.external :=
  (Vector.getElem_ofFn _).trans (h.regs r hr)

theorem FrameInfo.Pre.low (h : m.Pre code fr s) {lifted : Lifted} {l : lifted.Label}
    (r : Fin Reg.count) (w : Nat) (hr : r.val ∈ Activation.entryNumbers := by decide) :
    (Atom.low r w ((fr.entryReg r).setWidth w)).Holds code (lifted.locationOf l s).arguments
      s.external :=
  congrArg (Value.get w) (h.gpr (lifted := lifted) (l := l) r hr)

theorem FrameInfo.Pre.entryAtoms (h : m.Pre code fr s) (lifted : Lifted) (l : lifted.Label) :
    Atom.All code (lifted.locationOf l s).arguments s.external (m.entryAtoms fr) := by
  have hr : ∀ r ∈ Activation.entryNumbers, ∀ hr : r < Reg.count,
      (lifted.locationOf l s).arguments[r] = ⟨64, fr.entryReg r⟩ := fun r hm _ =>
    (Vector.getElem_ofFn _).trans (h.regs r hm)
  unfold FrameInfo.entryAtoms FrameInfo.frameAtoms FrameInfo.entryFrame
  rw [Atom.all_append, Atom.all_append, Atom.all_append]
  refine ⟨⟨⟨⟨hr 4 (by decide) (by decide), (Vector.getElem_ofFn _).trans (Reg.read_df_iff.2 h.df),
    ?_⟩, trivial⟩, h.stackAtoms _⟩, h.callSlotAtoms _⟩
  simp only [FrameInfo.entryRegs, List.map_cons, List.map_nil, Atom.All, Atom.Holds]
  exact ⟨hr 1 (by decide) (by decide), hr 2 (by decide) (by decide),
    hr 3 (by decide) (by decide), hr 5 (by decide) (by decide), hr 6 (by decide) (by decide),
    hr 7 (by decide) (by decide), hr 8 (by decide) (by decide), hr 9 (by decide) (by decide),
    hr 12 (by decide) (by decide), hr 13 (by decide) (by decide),
    hr 14 (by decide) (by decide), hr 15 (by decide) (by decide),
    (Vector.getElem_ofFn _).trans h.mxcsr, (Vector.getElem_ofFn _).trans h.ftw,
    (Vector.getElem_ofFn _).trans h.fcw, trivial⟩

theorem FrameInfo.Pre.memReadable (h : m.Pre code fr s) : MemReadable s (stackPtr s) 8 := by
  rw [h.stackPtr_eq]
  have hslot := h.slot
  rw [← h.original] at hslot
  exact ⟨hslot.low, fun i hi => hslot.present i hi⟩

theorem FrameInfo.Pre.returnBoundary (h : m.Pre code fr s) :
    (returnBoundary s).rip = fr.ret ∧ (returnBoundary s).rsp = fr.rsp + 8 := by
  refine ⟨?_, by simp only [X86Proofs.returnBoundary, h.stackPtr_eq]⟩
  show memLoad s.external (stackPtr s) 64 = fr.ret
  rw [h.stackPtr_eq, h.original, h.ret]

end Entry

theorem doneAtoms_retRel [Bindings] {code : CodeMap} {lifted : Lifted} {m : FrameInfo}
    {fr : Activation} {lo : Output Value Ram Reg.count} {t : RamState}
    (hrel : RetRel code lifted lo t)
    (h : Atom.All code lo.values lo.store (m.doneAtoms fr))
    (hfp : m.fpPreserved = [39, 50, 51])
    (hlive : ∀ r ∈ [4, 22, 39, 50, 51] ++ m.preserved.map Fin.val, Live lifted.retLive r) :
    (Reg.ofIndex 4).read t = ⟨64, fr.rsp + 8⟩ ∧ RFLAGS.DirectionFlagClear t.RFLAGS ∧
      (∀ r ∈ m.preserved, (Reg.ofIndex r).read t = ⟨64, fr.entryReg r⟩) ∧
      (Reg.ofIndex 39).read t = ⟨32, fr.mxcsr⟩ ∧ (Reg.ofIndex 50).read t = ⟨16, fr.ftw⟩ ∧
      (Reg.ofIndex 51).read t = ⟨16, fr.fcw⟩ := by
  obtain ⟨h4, h22, hrest⟩ := h
  obtain ⟨hp, hfpAtoms⟩ := (Atom.all_append _ _).1 hrest
  rw [hfp] at hfpAtoms
  obtain ⟨h39, h50, h51, -⟩ := hfpAtoms
  have hread : ∀ r : Fin Reg.count, r.val ∈ [4, 22, 39, 50, 51] ++ m.preserved.map Fin.val →
      lo.values[r] = (Reg.ofIndex r).read t := fun r hr =>
    hrel.regs r r.isLt (hlive r hr)
  refine ⟨(hread 4 (List.mem_append_left _ (by decide))).symm.trans h4,
    Reg.read_df_iff.1 ((hread 22 (List.mem_append_left _ (by decide))).symm.trans h22),
    fun r hr => ?_, (hread 39 (List.mem_append_left _ (by decide))).symm.trans h39,
    (hread 50 (List.mem_append_left _ (by decide))).symm.trans h50,
    (hread 51 (List.mem_append_left _ (by decide))).symm.trans h51⟩
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

theorem FrameInfo.Post.sysVCalleeReturn {m : FrameInfo} {code : CodeMap} {fr : Activation}
    {footprint : List MemoryRegion} {s t : RamState} (hpost : m.Post fr footprint t)
    (hpre : m.Pre code fr s)
    (hpreserved : ∀ r : Fin Reg.count, r.val ∈ Activation.calleeSavedNumbers → r ∈ m.preserved) :
    SysVCalleeReturn s t fr.ret := by
  have gpr (r : Fin Reg.count) (hr : r.val ∈ Activation.calleeSavedNumbers) :
      (Reg.ofIndex r).read t = (Reg.ofIndex r).read s :=
    (hpost.preserved r (hpreserved r hr)).trans
      (hpre.regs r (Activation.calleeSavedNumbers_sub _ hr)).symm
  have hrsp : s.regValue .rsp = fr.rsp := Value.eq_bits (hpre.regs 4 (by decide))
  have hmxcsr : s.MXCSR = fr.mxcsr := Value.eq_bits hpre.mxcsr
  have hftw : s.FP87_Tag_Word = fr.ftw := Value.eq_bits hpre.ftw
  have hftw' : t.FP87_Tag_Word = fr.ftw := Value.eq_bits hpost.ftw
  exact {
    rip := hpost.rip
    rspPopped := (Value.eq_bits hpost.rsp).trans (by rw [hrsp])
    rbx := Value.eq_bits (gpr 3 (by decide))
    rbp := Value.eq_bits (gpr 5 (by decide))
    r12 := Value.eq_bits (gpr 12 (by decide))
    r13 := Value.eq_bits (gpr 13 (by decide))
    r14 := Value.eq_bits (gpr 14 (by decide))
    r15 := Value.eq_bits (gpr 15 (by decide))
    directionFlag := hpost.df
    mxcsrControl := hpost.mxcsrControl.trans (by rw [hmxcsr])
    x87Control := (Value.eq_bits hpost.fcw).trans (Value.eq_bits hpre.fcw).symm
    x87Mode := fun h => by
      unfold X87StackEmpty at h ⊢
      rw [hftw', ← hftw, h]
    fs := hpost.fs.trans hpre.fs.symm }

theorem sysVCalleeReturn_calleeSaved {σ : Type} {initial final : X86.State σ} {ret : BitVec 64}
    (h : SysVCalleeReturn initial final ret) :
    ∀ r ∈ ([.rbx, .rbp, .r12, .r13, .r14, .r15] : List Syntax.Reg),
      final.regValue r = initial.regValue r := by
  simp only [List.mem_cons, List.mem_nil_iff, or_false, forall_eq_or_imp, forall_eq]
  exact ⟨h.rbx, h.rbp, h.r12, h.r13, h.r14, h.r15⟩

theorem RamWriteFrame.memoryWriteFrame {initial t : RamState} {rs : List MemoryRegion} {n : Nat}
    {regions : Vector MemoryRegion n} (h : RamWriteFrame initial.external t.external rs)
    (hregions : ∀ x, (∀ r ∈ regions, ¬ r.Contains x) → ∀ r ∈ rs, ¬ r.Contains x) :
    MemoryWriteFrame initial t regions := by
  intro a ha
  refine h.outside a ⟨by omega, fun r hr => ?_⟩
  have hc := hregions a.toNat ha r hr
  simp only [contains_iff, not_and, Nat.not_lt] at hc
  omega

end P256.Proofs.Refine
