import P256.Proofs.Program.Compare.Body
import P256.Proofs.Program.Compare.Frame.TailCall
import P256.Proofs.Program.Compare.Tail.Main

namespace P256.Proofs.Program.Compare

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Spec.Program P256.Spec.Program.Routines

theorem tail_call_working {initial s t : RamState}
    (hsp : stackPtr s = stackPtr initial - 56)
    (h : (callEffect (fun _ ↦ 0x11cd30) 0x11c8ce s).Holds s t) :
    AgreesExcept (workingChanges initial) s t := by
  have ha : pushAddr s = stackPtr initial - 64 := by
    rw [pushAddr, hsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd]
  apply h.agrees.widen
  · intro c hc hm
    simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · simp [workingChanges, callChanges]
    · simp [Component.isMem] at hm
    · simp [workingChanges, callChanges]
  · intro x c hc hcov
    simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact hcov.elim
    · refine ⟨.mem (stackPtr initial - 64) 64, by simp [workingChanges, callChanges], ?_⟩
      obtain ⟨i, hi, he⟩ := hcov
      exact ⟨i, by omega, ha ▸ he⟩
    · exact hcov.elim

theorem body_tail [Bindings] {boundary : ReturnBoundary} {initial s : RamState}
    (hp : CallPre initial) (hb : CallBoundary boundary initial) (hs : TailReady initial s) :
    ∃ fuel t, Advances boundary fuel s t ∧ BodyResult initial t := by
  obtain ⟨called, hac, hrc, hcc, hec⟩ := Frame.tail_call_of_callPre hp hs.ready hs.code
    hs.rip hs.saved hs.frame.grow hb.1
  have hfc := tail_call_working hs.saved.rsp hec
  have h1 : (Operand.reg 1 : Operand 64).read called = (Operand.reg 1 : Operand 64).read s :=
    hec.agrees.read (by simp)
  have h2 : (Operand.reg 2 : Operand 64).read called = (Operand.reg 2 : Operand 64).read s :=
    hec.agrees.read (by simp)
  have h6 : (Operand.reg 6 : Operand 64).read called = (Operand.reg 6 : Operand 64).read s :=
    hec.agrees.read (by simp)
  obtain ⟨n, body, hab, hrb, hcb, hspb, hmb, hfb, hipb, heqb⟩ :=
    Tail.small_tail boundary called hrc hcc hb.register hec.rip
      (by rw [h1]; exact hs.small)
      (by rw [h1, h6]; exact hs.left.of_holds hec)
      (by rw [h1, h2]; exact hs.right.of_holds hec)
  have hread : MemReadable s (pushAddr s) 8 := by
    have hh := hp.frame.stack_sub_readable (offset := 64) (len := 8) (by decide) (by decide)
    have ha : pushAddr s = stackPtr initial - 64 := by
      rw [pushAddr, hs.saved.rsp]
      simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd]
    rw [ha]
    exact ⟨hh.low, fun i hi ↦ hs.frame.grow _ (hh.mem i hi)⟩
  obtain ⟨returned, har, hrr, hcr, her⟩ :=
    Frame.tail_return_after_call hec hread hrb hcb hipb hmb hspb hb.1
  have hmr : returned.external = called.external :=
    (her.agrees.external (by simp [Component.Covers])).trans hmb
  have hspr : stackPtr returned = stackPtr s := by
    change (Operand.reg 4 : Operand 64).read returned = _
    rw [her.writes, hspb]
    exact (callEffect_stack hec).2
  have h13r : returned.regValue .r13 = s.regValue .r13 := by
    have hc13 : (Operand.reg 13 : Operand 64).read called = (Operand.reg 13 : Operand 64).read s :=
      hec.agrees.read (by simp)
    have hb13 : (Operand.reg 13 : Operand 64).read body = (Operand.reg 13 : Operand 64).read called :=
      hfb.read (by decide)
    have hr13 : (Operand.reg 13 : Operand 64).read returned = (Operand.reg 13 : Operand 64).read body :=
      her.agrees.read (by simp)
    exact hr13.trans (hb13.trans hc13)
  have hfr : AgreesExcept (workingChanges initial) initial returned := working_trans hs.frame
    ((hfc.trans (hfb.trans her.agrees)).mono
      (by simp [workingChanges, callChanges, Tail.changes]))
  have hsaved : Frame.Saved initial returned :=
    hs.saved.after_tail_call hec hmr hspr h13r
  have hbs : BodyState initial returned := ⟨hrr, hcr, hsaved, hfr⟩
  have hipr : returned.RIP = 0x11c8ce := by
    rw [her.rip]
    change memLoad body.external (stackPtr body) 64 = _
    rw [hspb, hmb]
    exact (callEffect_stack hec).1
  obtain ⟨m, t, hat, hrt, hct, het, _⟩ :=
    tail_return_jump boundary returned hrr hcr hipr hb.register
  have hbst := hbs.of_registers hrt hct (het.agrees.mono (by simp [bodyChanges]))
  have heax : (Operand.reg 0 : Operand 32).read t = (Operand.reg 0 : Operand 32).read body :=
    (het.agrees.read (by simp)).trans (her.agrees.read (by simp))
  refine ⟨1 + n + 1 + m, t, ((hac.trans hab).trans har).trans hat, ⟨hbst, het.rip, ?_⟩⟩
  rw [heax, heqb, h1, h2, h6]
  exact (bytesEqual_working_iff hfc hs.stackLeft hs.stackRight).trans hs.equal_iff

end P256.Proofs.Program.Compare
