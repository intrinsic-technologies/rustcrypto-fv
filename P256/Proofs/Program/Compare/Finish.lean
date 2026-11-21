import P256.Proofs.Program.Compare.Input
import P256.Proofs.Program.Compare.Boundary
import P256.Proofs.Program.Compare.Frame.Epilogue
import P256.Proofs.Program.Compare.Mismatch.Main

namespace P256.Proofs.Program.Compare

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Spec.Program P256.Spec.Program.Routines

def bodyChanges : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 3, .reg 5, .reg 6, .reg 7, .reg 8,
    .reg 9, .reg 10, .reg 11, .reg 12, .reg 14, .reg 15, .flags, .rip]

structure BodyState [Bindings] (initial s : RamState) : Prop where
  ready : ReadyToStep s
  code : CodeIn Extracted.programSections.toCodeMap s
  saved : Frame.Saved initial s
  frame : AgreesExcept (workingChanges initial) initial s

structure BodyResult [Bindings] (initial s : RamState) : Prop extends BodyState initial s where
  rip : s.RIP = 0x11c923
  zero_iff : (Operand.reg 0 : Operand 32).read s = 0 ↔
    BytesEqual initial ((Operand.reg 7 : Operand 64).read initial)
      ((Operand.reg 6 : Operand 64).read initial) ((Operand.reg 2 : Operand 64).read initial).toNat

theorem CallBoundary.outside_restore {boundary : ReturnBoundary} {s : RamState}
    (h : CallBoundary boundary s) : Frame.Outside boundary.rip := by
  by_cases hlo : boundary.rip.toNat < 0x11c923
  · exact Or.inl hlo
  · right
    by_cases hhi : 0x11c92f < boundary.rip.toNat
    · exact hhi
    · exact False.elim (h.1 (inRoutine_inProgram ⟨by omega, by omega⟩))

theorem BodyState.of_registers [Bindings] {initial s t : RamState}
    (hs : BodyState initial s) (hr : ReadyToStep t) (hc : CodeIn Extracted.programSections.toCodeMap t)
    (hf : AgreesExcept bodyChanges s t) : BodyState initial t := by
  refine ⟨hr, hc, hs.saved.of_memory ?_ ?_ ?_, working_trans hs.frame ?_⟩
  · exact hf.external (by simp [bodyChanges, Component.Covers])
  · exact hf.read (n := 64) (r := 4) (by decide)
  · exact hf.read (n := 64) (r := 13) (by decide)
  · exact hf.mono (by simp [bodyChanges, workingChanges, callChanges])

theorem BodyState.of_prologue [Bindings] {initial s : RamState}
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programSections.toCodeMap s)
    (he : (Frame.prologueEffect initial).Holds initial s) : BodyState initial s :=
  ⟨hr, hc, Frame.prologue_saved he, prologue_working he⟩

theorem body_mismatch [Bindings] {boundary : ReturnBoundary} {initial s : RamState}
    (hs : BodyState initial s) (hb : RegisterBoundary boundary s) (hip : s.RIP = 0x11c8d0)
    (hne : (Operand.reg 0 : Operand 64).read s ≠ (Operand.reg 7 : Operand 64).read s ∨
      (Operand.reg 3 : Operand 64).read s ≠ (Operand.reg 14 : Operand 64).read s)
    (hbytes : ¬ BytesEqual initial ((Operand.reg 7 : Operand 64).read initial)
      ((Operand.reg 6 : Operand 64).read initial) ((Operand.reg 2 : Operand 64).read initial).toNat) :
    ∃ fuel t, Advances boundary fuel s t ∧ BodyResult initial t := by
  obtain ⟨t, ht, hipt, hnet⟩ := Mismatch.main_mismatch boundary s hs.ready hs.code hb hip hne
  obtain ⟨n, ha⟩ := ht.advances
  have hs' := hs.of_registers ht.ready ht.code
    (ht.frame.mono (by simp [Mismatch.changes, bodyChanges]))
  exact ⟨n, t, ha, ⟨hs', hipt, ⟨fun hz ↦ False.elim (hnet hz),
    fun he ↦ False.elim (hbytes he)⟩⟩⟩

theorem finish [Bindings] {boundary : ReturnBoundary} {initial s : RamState}
    (hp : CallPre initial) (hb : CallBoundary boundary initial) (hs : BodyResult initial s) :
    ∃ fuel t, Advances boundary fuel s t ∧ Result initial t := by
  have hread : MemReadable s (stackPtr s + 16) 48 := by
    rw [hs.saved.rsp]
    have he : stackPtr initial - (56 : BitVec 64) + 16 = stackPtr initial - 40 := by
      simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd]
    rw [he]
    have h := hp.frame.stack_sub_readable (offset := 40) (len := 48) (by decide) (by decide)
    exact ⟨h.low, fun i hi ↦ hs.frame.grow _ (h.mem i hi)⟩
  have hret : Frame.word s 56 = (returnBoundary initial).rip := by
    dsimp only [Frame.word]
    rw [hs.saved.rsp, BitVec.sub_add_cancel]
    exact working_return_word hs.frame
  obtain ⟨n, t, ha, hr, hc, he, hcs, hsp, heax⟩ := Frame.epilogue hs.ready hs.code
    ⟨hs.rip, hread⟩ hs.saved hb.outside_restore
    (by rw [hret]; exact hp.frame.returnLow) (Or.inl (hret ▸ hb.2))
  have hf : AgreesExcept (workingChanges initial) initial t := working_trans hs.frame
    (he.agrees.mono (by simp [Frame.effect, Effect.components, workingChanges, callChanges]))
  refine ⟨n, t, ha, ⟨⟨hr, hc, he.rip.trans hret, hsp, working_calleeSaved hf hcs, hcs⟩, ?_⟩⟩
  rw [heax]
  exact hs.zero_iff

end P256.Proofs.Program.Compare
