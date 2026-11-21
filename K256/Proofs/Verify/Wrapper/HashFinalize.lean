import K256.Proofs.Verify.Wrapper.HashFinalize.Mark
import K256.Proofs.Verify.Wrapper.HashFinalize.Compress
import K256.Proofs.Verify.Wrapper.HashFinalize.Clear

namespace K256.Proofs.Verify.Wrapper

open K256.Spec K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  CFG Lift Refine Verify.LIR Standards.SECG.ECC Standards.NIST.SHA2 Hash.FinalBlocks

variable {initial : RamState} {key msg sig : ByteArray} {p : Curve.Point} {r s : Nat}
    {a : Core.Registers} {m : Ram}

set_option maxRecDepth 2048 in
theorem hashFinalize (compress : Verify.Hash.Update.Compresses)
    (call : ValidCall verifyingKeyVerify initial [key,msg,sig]) (buffer : HashBuffer initial a m p r s msg) :
    ∃ b t, Core.Reaches .l103170 a m .l103306 b t ∧ HashOutput initial b t p r s msg := by
  let sp := localSp initial
  have dst {t : Ram} (mem : Memory initial t) : Readable t (sp+160) 64 :=
    (Hash.Update.writable (off := 376) call mem
      (by dsimp only [sp,localSp]; bv_omega) (by decide) (by decide) (by decide)).readable
  obtain ⟨b,t,marked,h,bytes⟩ := HashFinalize.mark call buffer
  let first := Hash.compressBlocks Hash.initialHash msg
  let pre := if msg.size % 64 < 56 then first else Hash.compressBlocks first (Hash.paddedBuffer msg)
  have ready : ∃ c u, Core.Reaches .l103170 a m .l103289 c u ∧
      HashFinalize.State initial c u p r s msg pre ∧
      (⟨(sp+8).toNat,56⟩ : MemoryRegion).HasBytes u (Hash.finalPrefix msg) := by
    by_cases small : msg.size % 64 < 56
    · simp only [small, ite_true] at marked
      exact ⟨b,t,marked,by simpa only [pre,small,ite_true] using h,shortPrefix t sp msg small bytes⟩
    · simp only [small, ite_false] at marked
      obtain ⟨c,u,run,h'⟩ := HashFinalize.compressBlock compress call h false (Hash.paddedBuffer msg)
        (Hash.paddedBuffer_size msg) (stagedFirst t sp (returnAddress false) msg bytes (dst h.memory))
      obtain ⟨d,v,cleared,h'',headBytes⟩ := HashFinalize.clear call h' small
      exact ⟨d,v,marked.trans (run.trans cleared),by simpa only [pre,small,ite_false] using h'',headBytes⟩
  obtain ⟨c,u,path,hc,headBytes⟩ := ready
  have length := congrArg (Value.get 64) hc.length
  obtain ⟨d,v,finish,out⟩ := HashFinalize.compressBlock compress call hc true (Hash.finalBlock msg)
    (Hash.finalBlock_size msg) (by
      change (⟨(sp+160).toNat,64⟩ : MemoryRegion).HasBytes (callMemory true u sp _) _
      rw [length]
      exact stagedLast u sp (returnAddress true) msg headBytes (dst hc.memory))
  have eqHash : Hash.compressBlocks pre (Hash.finalBlock msg) =
      Hash.compressBlocks Hash.initialHash (Hash.bytePadding msg) := by
    rw [Hash.compressBlocks_bytePadding_eq, Hash.compressBlocks_single _ _ (Hash.finalBlock_size msg),
      Hash.finalBlock_eq]
    by_cases small : msg.size % 64 < 56
    · simp only [pre,first,small,ite_true]
    · simp only [pre,first,small,ite_false]
      rw [Hash.compressBlocks_single _ _ (Hash.paddedBuffer_size msg)]
      simp only [Hash.tailFirst,Hash.paddedBuffer,small,ite_false]
  exact ⟨d,v,path.trans finish,out.toFrame,out.operands,eqHash ▸ out.state,out.r14Width,
    congrArg Value.width out.length⟩

end K256.Proofs.Verify.Wrapper
