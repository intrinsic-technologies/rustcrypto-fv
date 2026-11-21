import Md5.Proofs.Buffered.DigestGeometry
import Md5.Proofs.Buffered.Epilogue

namespace Md5.Proofs.Buffered

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem digest_finish [bindings : Bindings] {initial s t : RamState}
    {boundary : ReturnBoundary} {input : ByteArray}
    (hCall : Digest.ValidCall bindings initial input)
    (hp : DigestPrepared initial boundary input s)
    (hq : Finalize.Post .digest boundary input s t)
    (hBoundaryRsp : boundary.rsp = stackPtr initial + 8)
    (hLow : boundary.rip.toNat < userAddressLimit) :
    ∃ fuel final cs, Returns boundary fuel s final ∧ ReadyToStep final ∧
      AgreesExcept cs initial final ∧
      MemoryWriteFrame initial final
        #v[Digest.outputRegion initial, Stack.region initial Digest.minStackBytes] ∧
      Digest.readOutput initial final =
        .ok (Standards.RFC.MD5.messageDigest (Standards.RFC.MD5.bitsOfBytes input)) ∧
      CalleeSavedRegistersUnchanged initial final ∧ DirectionFlagUnset final := by
  have hSource : MemReadable t (stackPtr t + 8) 16 := by
    rw [hq.rsp]
    exact Stores.readable_of_agrees (hp.pre.toStorage.stackWritable 8 16 (by decide)).readable hq.agrees
  have hScratch : Memory.MemWritable t (stackPtr t + 112) 16 := by
    rw [hq.rsp]
    exact Stores.writable_of_agrees (hp.pre.toStorage.stackWritable 112 16 (by decide)) hq.agrees
  have hOutput : Memory.MemWritable t (t.regValue .rbx) 16 := by
    rw [hp.outputPointer hq]
    exact Stores.writable_of_agrees (outputWritable hCall) (hp.agrees.trans hq.agrees)
  have hScratchCode : ∀ i < 16, ¬ InProgram (stackPtr t + 112 + BitVec.ofNat 64 i) := by
    rw [hq.rsp]
    exact (hp.pre.toStorage.stackRange 112 16 (by decide)).code
  have hOutputCode : ∀ i < 16, ¬ InProgram (t.regValue .rbx + BitVec.ofNat 64 i) := by
    rw [hp.outputPointer hq]
    exact outputAvoids hCall
  obtain ⟨u, hOutRun, huReady, huCode, huRip, huAgrees, hCopy⟩ :=
    digest_output hq.ready hq.code hq.rip hp.pre.boundaryOutside
      hSource hScratch hOutput hScratchCode hOutputCode
  have huRsp : stackPtr u = stackPtr t :=
    huAgrees.read (n := 64) (r := 4) (by simp [digestOutputChanges])
  have hSaved (offset : Nat) (hl : 264 ≤ offset) (hh : offset + 8 ≤ 304) :
      (Operand.mem (stackPtr u + BitVec.ofNat 64 offset) : Operand 64).read u =
        (Operand.mem (stackPtr s + BitVec.ofNat 64 offset) : Operand 64).read s := by
    rw [huRsp]
    exact (hp.outputSaved hCall hq huAgrees hl hh).trans
      (hp.finalizeSaved hCall.stackAvailable hq hl hh)
  have hSlots : ∀ i < 5,
      MemReadable u (stackPtr u + BitVec.ofNat 64 (264 + 8 * i)) 8 := by
    intro i hi
    rw [huRsp, hq.rsp]
    exact Stores.readable_of_agrees (hp.stackReadable hCall.stackAvailable _ _ (by omega))
      (hq.agrees.trans huAgrees)
  have hRet : boundary.rip = (Operand.mem (stackPtr u + 296) : Operand 64).read u := by
    exact (hSaved 296 (by decide) (by decide) |>.trans hp.returnSlot).symm
  have hRsp : boundary.rsp = stackPtr u + 304 := by
    rw [huRsp, hq.rsp, hp.stack, hBoundaryRsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  obtain ⟨final, hReturn, hfReady, hfAgrees, hfRbx, hfR12, hfR14, hfR15⟩ :=
    digest_epilogue huReady huCode huRip hSlots hRet hRsp hLow hp.pre.boundaryOutside
  have hFinalMemory : final.external = u.external :=
    hfAgrees.external (by simp [Component.Covers])
  have hAll := ((hp.agrees.trans hq.agrees).trans huAgrees).trans hfAgrees
  obtain ⟨n, hFinalize⟩ := hq.advances
  refine ⟨n + (6 + 6), final, _, hFinalize.returns (hOutRun.returns hReturn), hfReady,
    hAll, ?_, ?_, ?_, hAll.directionFlagClear (by
      simp [digestPreparationChanges, Finalize.Kind.changes, Finalize.Kind.workRegisters,
        Finalize.Kind.localChanges, digestOutputChanges]) hCall.directionFlagUnset⟩
  · intro address ha
    rw [hFinalMemory, hp.outputFrame hCall hq huAgrees address ha]
    rw [hq.frame hp.pre.toStorage address (by
      intro region hr hc
      simp only [Vector.mem_singleton] at hr
      subst region
      exact ha _ (by simp) (hp.finalizeStackSubset hCall.stackAvailable hc))]
    exact hp.frame hCall.stackAvailable address (by
      intro region hr hc
      simp only [Vector.mem_singleton] at hr
      subst region
      exact ha _ (by simp) hc)
  · apply readVector_of_hasBytes
    refine ⟨by simp [MemoryRegion.HasLength, Digest.outputRegion, registerRegion, ByteArray.size], ?_⟩
    intro i
    have hi : i.val < 16 := by simpa only [ByteArray.size, Vector.size_toArray] using i.isLt
    have hd := hq.digest.2 i
    rw [hFinalMemory]
    change u.external[BitVec.ofNat 64 ((initial.regValue .rdx).toNat + i.val)]? = _
    rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      ← hp.outputPointer hq, hCopy i.val hi]
    simpa only [Finalize.Kind.resultRegion, Finalize.Kind.resultOffset, hq.rsp,
      BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using hd
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hfRbx.trans ((hSaved 264 (by decide) (by decide)).trans hp.savedRbx)
    · exact hAll.read (n := 64) (r := 5) (by
        simp [digestPreparationChanges, Finalize.Kind.changes, Finalize.Kind.workRegisters,
          Finalize.Kind.localChanges, digestOutputChanges])
    · exact hfR12.trans ((hSaved 272 (by decide) (by decide)).trans hp.savedR12)
    · exact hAll.read (n := 64) (r := 13) (by
        simp [digestPreparationChanges, Finalize.Kind.changes, Finalize.Kind.workRegisters,
          Finalize.Kind.localChanges, digestOutputChanges])
    · exact hfR14.trans ((hSaved 280 (by decide) (by decide)).trans hp.savedR14)
    · exact hfR15.trans ((hSaved 288 (by decide) (by decide)).trans hp.savedR15)

end Md5.Proofs.Buffered
