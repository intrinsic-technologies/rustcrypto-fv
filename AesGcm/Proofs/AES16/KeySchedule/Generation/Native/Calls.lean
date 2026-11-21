import AesGcm.Proofs.AES16.KeySchedule.Generation.Memory
import AesGcm.Proofs.Machine.Runtime.Frame

namespace AesGcm.Proofs.Machine.AES16.KeySchedule.Generation.Native

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift
  X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

private theorem slot_bounds (cs : List (BitVec 64 × BitVec 64))
    (hcs : cs ⊆ [(0x201210, 0x103880), (0x201230, 0x101230)]) :
    FrameInfo.slotsHigh cs ≤ 0x201238 ∧ 0x201210 ≤ FrameInfo.slotsLow cs := by
  induction cs with
  | nil => decide
  | cons c cs ih =>
    have hc := hcs (List.Mem.head _)
    have hi := ih (fun _ h ↦ hcs (List.Mem.tail _ h))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    all_goals
      simp only [FrameInfo.slotsHigh, FrameInfo.slotsLow, List.map_cons, List.foldr_cons,
        BitVec.reduceToNat] at *
      omega

private theorem slot_atoms {use256 : Bool} {code : CodeMap} {mem : Ram} {sp : BitVec 64}
    (hmemory : MemoryReady use256 code mem sp)
    (args : Values Value Reg.count) (fr : Activation) (m : FrameInfo)
    (hsp : fr.rsp = sp - 8) (hwindow : m.window ≤ 240)
    (hcs : m.callSlots ⊆ [(0x201210, 0x103880), (0x201230, 0x101230)]) :
    Atom.All code args mem (m.callSlotAtoms m.callSlots fr) := by
  have hsub : (sp - 8).toNat = sp.toNat - 8 := by
    have := hmemory.hroom
    bv_omega
  have hdata (cs : List (BitVec 64 × BitVec 64))
      (h : cs ⊆ [(0x201210, 0x103880), (0x201230, 0x101230)]) :
      Atom.All code args mem
        (cs.flatMap (fun c ↦ [.readable c.1 8, .mem c.1 64 c.2])) := by
    induction cs with
    | nil => trivial
    | cons c cs ih =>
      have hc := h (List.Mem.head _)
      have ht := ih (fun _ hin ↦ h (List.Mem.tail _ hin))
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact ⟨hmemory.hreadPanic, hmemory.hpanic, ht⟩
      · exact ⟨hmemory.hreadBounds, hmemory.hbounds, ht⟩
  unfold FrameInfo.callSlotAtoms
  split
  · trivial
  · rw [atoms_append]
    refine ⟨hdata _ hcs, ?_, trivial⟩
    change FrameInfo.slotsHigh m.callSlots + m.window ≤ fr.rsp.toNat ∨
      fr.rsp.toNat ≤ FrameInfo.slotsLow m.callSlots
    have hb := slot_bounds m.callSlots hcs
    have ha := hmemory.hslotsApart
    have hr := hmemory.hroom
    rw [hsp, hsub]
    cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] at ha <;> omega

theorem pushed_call_exec
    (P : Lifted) (code : CodeMap) (label : P.Label) (m : FrameInfo)
    (footprint : Activation → List MemoryRegion) (pre post : Activation → Ram → Prop)
    (hcontract : CallContract P code label m footprint pre post)
    {use256 : Bool} (mem : Ram) (args : Values Value Reg.count) (sp ret : BitVec 64)
    (hmemory : MemoryReady use256 code mem sp)
    (hsp : args[4].get 64 = sp - 8) (hTypes : GPRsTyped args)
    (h39 : args[39] = ⟨32, args[39].get 32⟩)
    (h50 : args[50] = ⟨16, args[50].get 16⟩)
    (h51 : args[51] = ⟨16, args[51].get 16⟩)
    (hDF : args[22] = ⟨1, 0⟩) (hRetLow : ret.toNat < 2 ^ 32)
    (hwindow : m.window ≤ 240)
    (hslots : m.callSlots ⊆ [(0x201210, 0x103880), (0x201230, 0x101230)])
    (hPre : pre (activationOfValues (memStore mem (sp - 8) ret) args ret (sp - 248))
      (memStore mem (sp - 8) ret)) :
    ∃ output : Output Value Ram Reg.count,
      P.program.Exec (dialect code) ⟨⟨label, args, memStore mem (sp - 8) ret⟩, []⟩ output ∧
      output.tag = some ⟨64, ret⟩ ∧
      Atom.All code output.values output.store
        (m.doneAtoms (activationOfValues (memStore mem (sp - 8) ret) args ret (sp - 248))) ∧
      GPRsTyped output.values ∧
      RamWriteFrame (memStore mem (sp - 8) ret) output.store
        ((activationOfValues (memStore mem (sp - 8) ret) args ret (sp - 248)).region ::
          footprint (activationOfValues (memStore mem (sp - 8) ret) args ret (sp - 248))) ∧
      post (activationOfValues (memStore mem (sp - 8) ret) args ret (sp - 248)) output.store := by
  have hroom := hmemory.hroom
  have hsub : (sp - 8).toNat = sp.toNat - 8 := by bv_omega
  have hpush : RamWriteFrame mem (memStore mem (sp - 8) ret) (regions use256 sp) := by
    apply (RamWriteFrame.refl _ _).memStore ret
    refine ⟨span (sp - 248) 248, List.Mem.head _, ?_⟩
    simp only [InRegion, span, stack_sub_toNat hmemory, hsub]
    have := stack_limit hmemory
    cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] at * <;> omega
  have pushedReady := memoryReady_of_frame hmemory hpush (regions_within_stack hmemory)
  apply callContract_exec_values P code label m footprint pre post hcontract
    (memStore mem (sp - 8) ret) args ret (sp - 248) hTypes h39 h50 h51 hDF
  · rw [hsp]
    apply pushedReady.hstack.readable.sub
    · rw [stack_sub_toNat pushedReady, hsub]
      omega
    · rw [stack_sub_toNat pushedReady, hsub]
      cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  · rw [hsp]
    exact memLoad_memStore_same _ _ _ (by decide) (by decide)
  · exact hRetLow
  · intro _
    rw [hsp]
    have hoff : (BitVec.ofNat 64 m.window).toNat = m.window := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    have hw : (sp - 8 - BitVec.ofNat 64 m.window).toNat =
        sp.toNat - 8 - m.window := by
      rw [BitVec.toNat_sub_of_le, hsub, hoff]
      change (BitVec.ofNat 64 m.window).toNat ≤ (sp - 8).toNat
      rw [hoff, hsub]
      omega
    apply pushedReady.hstack.sub
    · rw [stack_sub_toNat pushedReady, hw]
      omega
    · rw [stack_sub_toNat pushedReady, hw]
      cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega
  · rw [hsp, hsub, stack_sub_toNat hmemory]
    omega
  · rw [hsp, hsub]
    have := hmemory.hAlign
    omega
  · exact slot_atoms pushedReady args _ m hsp hwindow hslots
  · exact hPre

theorem pushed_call_done (m : FrameInfo)
    (hpreserved : m.preserved = [3, 5, 12, 13, 14, 15])
    (hfp : m.fpPreserved = [39, 50, 51])
    (code : CodeMap) (mem : Ram) (args : Values Value Reg.count) (sp ret low : BitVec 64)
    (output : Output Value Ram Reg.count)
    (hsp : args[4].get 64 = sp - 8) (hTypes : GPRsTyped args)
    (h39 : args[39] = ⟨32, args[39].get 32⟩)
    (h50 : args[50] = ⟨16, args[50].get 16⟩)
    (h51 : args[51] = ⟨16, args[51].get 16⟩) (hDF : args[22] = ⟨1, 0⟩)
    (hdone : Atom.All code output.values output.store
      (m.doneAtoms (activationOfValues mem args ret low))) :
    output.values[4] = ⟨64, sp⟩ ∧
      (∀ r : Fin Reg.count, r.val ∈ [3, 5, 12, 13, 14, 15, 22, 39, 50, 51] →
        output.values[r] = args[r]) := by
  simp only [FrameInfo.doneAtoms, hpreserved, hfp, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, Atom.All, Atom.Holds, Atom.gpr,
    Activation.entryReg, Activation.entryValue, activationOfValues] at hdone
  rcases hdone with ⟨hs, hdf, h3, h5, h12, h13, h14, h15, h39', h50', h51', -⟩
  refine ⟨?_, ?_⟩
  · rw [hsp, BitVec.sub_add_cancel] at hs
    exact hs
  · rintro ⟨r, hr⟩ hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact h3.trans (hTypes.value 3).symm
    · exact h5.trans (hTypes.value 5).symm
    · exact h12.trans (hTypes.value 12).symm
    · exact h13.trans (hTypes.value 13).symm
    · exact h14.trans (hTypes.value 14).symm
    · exact h15.trans (hTypes.value 15).symm
    · exact hdf.trans hDF.symm
    · exact h39'.trans h39.symm
    · exact h50'.trans h50.symm
    · exact h51'.trans h51.symm

end AesGcm.Proofs.Machine.AES16.KeySchedule.Generation.Native
