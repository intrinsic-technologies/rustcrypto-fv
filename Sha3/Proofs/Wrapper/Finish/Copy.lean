import Sha3.Proofs.Wrapper.Finish.Copy.Steps
import Sha3.Proofs.Wrapper.Finish.Copy.Contract

namespace Sha3.Proofs.Wrapper.Finish

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

theorem final_copy_steps [bindings : Bindings] (hstride : UnitStringStride bindings)
    {initial s : RamState} {v : Variant} {mode : Mode} {keccak fullState : Bool} {inputs : Array Input} {split : Nat}
    {state : Incremental.State} {out : BitVec 64}
    (hCall : ValidInvocation bindings v mode initial inputs split keccak fullState)
    (hMode : mode.hasBeforeOutput = true)
    (inv : Invariant initial v mode s keccak fullState) (saved : SavedFrame initial s mode fullState)
    (ip : s.RIP = (mode.entry v keccak fullState).entryAddress + BitVec.ofNat 64 (startOffset v mode keccak fullState))
    (sp : stackPtr s = frameBase initial v mode keccak fullState)
    (slot : (Operand.mem (frameBase initial v mode keccak fullState + BitVec.ofNat 64 (mode.outputSlotOffset v keccak fullState)) : Operand 64).read s = out)
    (metadata : (Operand.mem (frameBase initial v mode keccak fullState + BitVec.ofNat 64 (mode.stateOffset v keccak fullState) + 200) : Operand 8).read s =
      BitVec.ofNat 8 state.cursor)
    (lanes : Permutation.memoryLanes (frameBase initial v mode keccak fullState + BitVec.ofNat 64 (mode.stateOffset v keccak fullState)) s = state.lanes) :
    ∃ t, Advances (returnBoundary initial) 48 s t ∧ Invariant initial v mode t keccak fullState ∧
      SavedFrame initial t mode fullState ∧
      t.RIP = Copy.callPC v mode keccak fullState + (14 : BitVec 64) ∧
      stackPtr t = frameBase initial v mode keccak fullState ∧
      t.regValue .rdi = frameBase initial v mode keccak fullState + BitVec.ofNat 64 (Copy.destinationOffset mode v fullState) ∧ t.regValue .rsi = out ∧
      (Operand.mem (frameBase initial v mode keccak fullState + BitVec.ofNat 64 (Copy.destinationOffset mode v fullState) + 200) : Operand 8).read t =
        BitVec.ofNat 8 state.cursor ∧
      Permutation.memoryLanes (frameBase initial v mode keccak fullState + BitVec.ofNat 64 (Copy.destinationOffset mode v fullState)) t = state.lanes ∧
      MemoryWriteFrame s t #v[Stack.region initial (mode.entry v keccak fullState).minStackBytes] := by
  obtain ⟨hd, hs, hApart, hdAlign, hfAlign, hfSmall, hPush⟩ :=
    Copy.layout_bounds mode v keccak fullState hMode
  obtain ⟨hSlotBefore, slotValue⟩ := Copy.outputSlot_bounds mode v keccak fullState hMode
  have inside : frameBase initial v mode keccak fullState ≠ (returnBoundary initial).rsp := by
    apply stackSub_ne_returnBoundary
    change BitVec.ofNat 64 8 + BitVec.ofNat 64 (mode.frameSize v keccak fullState) ≠ 0
    rw [← BitVec.ofNat_add]
    exact ofNat_ne_zero (by omega) (by omega)
  obtain ⟨imageSlice1, imageSlice2, imageSlice3, imageSlice4⟩ := Copy.prefixSlices v mode fullState
  have image := Copy.prefixImage v mode keccak fullState hMode
  obtain ⟨a, h1, ia, ipa, spa, arbx, adst, asrc, alen, hagree⟩ :=
    Copy.prefix_steps (destination := Copy.destinationDisp mode v fullState)
      (source := Copy.sourceDisp mode v fullState) hCall inv ip sp
      (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
        image.slice 0 imageSlice1)
      (image.slice (leaLen (.sib 4 none 0 (Copy.destinationDisp mode v fullState)))
        imageSlice2)
      (image.slice (leaLen (.sib 4 none 0 (Copy.destinationDisp mode v fullState)) +
        leaLen (.sib 4 none 0 (Copy.sourceDisp mode v fullState)))
        imageSlice3)
      (image.slice (leaLen (.sib 4 none 0 (Copy.destinationDisp mode v fullState)) +
        leaLen (.sib 4 none 0 (Copy.sourceDisp mode v fullState)) + 5)
        imageSlice4)
      (by
        change stackPtr s ≠ _
        rw [sp]
        exact inside)
  rw [Copy.destinationDisp_value] at arbx adst
  rw [Copy.sourceDisp_value mode v fullState hMode] at asrc
  rw [Copy.prefixLength] at ipa
  have hsa : AgreesExcept (Copy.changes initial v mode (Copy.destinationOffset mode v fullState) keccak fullState) s a := hagree.mono (by
    intro c hc
    simp only [Copy.prefixChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> simp [Copy.changes])
  obtain ⟨b, h2, ib, ipb, spb, retb, hab⟩ := Copy.call_steps hCall hMode ia (by simpa [Copy.callPC, BitVec.ofNat_add, BitVec.add_assoc] using ipa) spa
  have bdst : (Operand.reg 7 : Operand 64).read b = frameBase initial v mode keccak fullState + BitVec.ofNat 64 (Copy.destinationOffset mode v fullState) :=
    (hab.read (by simp)).trans adst
  have bsrc : (Operand.reg 6 : Operand 64).read b = frameBase initial v mode keccak fullState + BitVec.ofNat 64 (mode.stateOffset v keccak fullState) :=
    (hab.read (by simp)).trans asrc
  have blen : (Operand.reg 2 : Operand 64).read b = 208 :=
    (hab.read (by simp)).trans alen
  have brbx : (Operand.reg 3 : Operand 64).read b = frameBase initial v mode keccak fullState + BitVec.ofNat 64 (Copy.destinationOffset mode v fullState) :=
    (hab.read (by simp)).trans arbx
  have hab' : AgreesExcept (Copy.changes initial v mode (Copy.destinationOffset mode v fullState) keccak fullState) a b := hab.mono (by
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> simp [Copy.changes])
  have hsb := Copy.changes_trans hsa hab'
  have pre := Copy.memcpy_pre hCall hMode ib ipb spb bdst bsrc blen retb
  obtain ⟨c, h3, result⟩ := Memcpy.memcpy208_steps hstride (returnBoundary initial) b
    ib.ready ib.code pre
  have hbc : AgreesExcept (Memcpy.clobbers (frameBase initial v mode keccak fullState + BitVec.ofNat 64 (Copy.destinationOffset mode v fullState))) b c :=
    bdst ▸ result.agrees
  have ic := ib.of_agreesExcept hCall result.ready hbc
    (Copy.destination_writes hCall.stackAvailable (by omega)) (by simp [Memcpy.clobbers])
  have spc : stackPtr c = frameBase initial v mode keccak fullState := by
    rw [result.rsp, spb, BitVec.sub_add_cancel]
  have ipc : c.RIP = Copy.callPC v mode keccak fullState + (6 : BitVec 64) := by
    rw [result.rip, retb]
  have crbx : (Operand.reg 3 : Operand 64).read c = frameBase initial v mode keccak fullState + BitVec.ofNat 64 (Copy.destinationOffset mode v fullState) :=
    (hbc.read (by simp [Memcpy.clobbers])).trans brbx
  have hbc' : AgreesExcept (Copy.changes initial v mode (Copy.destinationOffset mode v fullState) keccak fullState) b c := hbc.mono (by
    intro q hq
    simp only [Memcpy.clobbers, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [Copy.changes])
  have hsc := Copy.changes_trans hsb hbc'
  have slotc : (Operand.mem (frameBase initial v mode keccak fullState + BitVec.ofNat 64 (mode.outputSlotOffset v keccak fullState)) : Operand 64).read c = out :=
    (Copy.changes_read (offset := mode.outputSlotOffset v keccak fullState) hsc
      (Or.inl (by omega)) (by omega) (by omega)).trans slot
  have suffixImage := Copy.suffixImage v mode keccak fullState hMode
  obtain ⟨t, h4, it, ipt, spt, tdst, tout, hct⟩ :=
    Copy.suffix_steps (destination := BitVec.ofNat 64 (Copy.destinationOffset mode v fullState))
      (outputSlot := BitVec.ofNat 8 (mode.outputSlotOffset v keccak fullState)) hCall ic ipc spc crbx
      (by simpa only [slotValue] using slotc)
      (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
        suffixImage.slice 0 rfl)
      (suffixImage.slice 3 (Copy.suffixSlice v mode keccak fullState hMode))
      (by
        rw [slotValue]
        exact ic.frameReadable hCall.stackAvailable
          (by omega))
      (by
        change stackPtr c ≠ _
        rw [spc]
        exact inside)
  have hct' : AgreesExcept (Copy.changes initial v mode (Copy.destinationOffset mode v fullState) keccak fullState) c t := hct.mono (by
    intro q hq
    simp only [Copy.prefixChanges, List.mem_cons, List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl <;> simp [Copy.changes])
  have hst := Copy.changes_trans hsc hct'
  have copy : ∀ i < 208,
      t.external[frameBase initial v mode keccak fullState + BitVec.ofNat 64 (Copy.destinationOffset mode v fullState) + BitVec.ofNat 64 i]? =
        s.external[frameBase initial v mode keccak fullState + BitVec.ofNat 64 (mode.stateOffset v keccak fullState) + BitVec.ofNat 64 i]? := by
    intro i hi
    rw [hct.external Copy.prefixChanges_noMem]
    have hh := result.copy i hi
    rw [bdst, bsrc] at hh
    rw [hh]
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact Copy.changes_byte hsb (by rcases hApart with hApart | hApart <;> omega) (by omega) (by omega)
  refine ⟨t, h1.trans (h2.trans (h3.trans h4)), it, Copy.changes_saved saved hst (by rw [hPush]; omega),
    (by simpa only [BitVec.add_assoc, show (6 : BitVec 64) + 8 = 14 from by decide] using ipt), spt, tdst, tout, ?_, ?_, hst.memoryWriteFrame (Copy.changes_writes (v := v) (mode := mode) (keccak := keccak) (fullState := fullState) (destination := Copy.destinationOffset mode v fullState) hCall.stackAvailable (by rw [hPush]; omega))⟩
  · exact (Copy.copied_read (offset := 200) copy (by decide)).trans metadata
  · rw [← lanes]
    funext i
    exact Copy.copied_read (offset := 8 * i.val) copy (by have := i.isLt; omega)

end Sha3.Proofs.Wrapper.Finish
