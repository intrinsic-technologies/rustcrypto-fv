import AesGcm.Proofs.Machine.GHASHUpdate.BatchValues
import AesGcm.Proofs.Machine.GHASHUpdate.Loop

namespace AesGcm.Proofs.Machine.GHASHUpdate
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime AesGcm.Proofs.Machine.GHASHInterface

set_option maxHeartbeats 800000 in
theorem driver_batch_exec (code : CodeMap) (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (hmultiply : MultiplyContract code) (args : Values Value Reg.count) (mem : Ram)
    (sp src ptr dst low : BitVec 64)
    (hsp : args[4].get 64 = sp) (hsrc : args[6].get 64 = src)
    (hptr : args[12].get 64 = ptr) (hdst : memLoad mem ptr 64 = dst)
    (htypes : GPRsTyped args)
    (h39 : args[39] = ⟨32, args[39].get 32⟩)
    (h50 : args[50] = ⟨16, args[50].get 16⟩)
    (h51 : args[51] = ⟨16, args[51].get 16⟩) (hdf : args[22] = ⟨1, 0⟩)
    (hstack : Writable code mem (sp - 312) 312)
    (hroom : low.toNat + 312 ≤ sp.toNat) (halign : sp.toNat % 16 = 0)
    (hr : Readable mem src 64) (hp : Readable mem ptr 8)
    (hsrcsep : (⟨low.toNat, sp.toNat - low.toNat⟩ : MemoryRegion).Disjoint (span src 64))
    (hptrsep : (⟨low.toNat, sp.toNat - low.toNat⟩ : MemoryRegion).Disjoint (span ptr 8))
    (hw : Writable code mem dst 32)
    (hsep : (⟨low.toNat, sp.toNat - low.toNat⟩ : MemoryRegion).Disjoint (span dst 32)) :
    ∃ o : Output Value Ram Reg.count,
      (LIR.program.sem (dialect code)).Reaches
        ⟨⟨.l1099c0, args, mem⟩, []⟩ ⟨⟨.l1099cc, o.values, o.store⟩, []⟩ ∧
      o.values[4] = ⟨64, sp⟩ ∧ o.values[15] = ⟨64, src + 64⟩ ∧
      (∀ r : Fin 53, r.val ∈ [3, 5, 12, 13, 14, 22, 39, 50, 51] → o.values[r] = args[r]) ∧
      GPRsTyped o.values ∧
      RamWriteFrame mem o.store [⟨low.toNat, sp.toNat - low.toNat⟩, span (dst + 16) 16] ∧
      (let result := updateBlocks mem src 4
          (memLoad mem dst 64) (memLoad mem (dst + 8) 64)
          (memLoad mem (dst + 16) 64, memLoad mem (dst + 24) 64)
       memLoad o.store (dst + 16) 64 = result.1 ∧ memLoad o.store (dst + 24) 64 = result.2) := by
  have hwret : Writable code mem (sp - 8) 8 :=
    hstack.of_offsets (addr_sub _ _) (addr_sub _ _) (by decide)
  obtain ⟨a, hcall, asp, aptr, a15, keep, aTypes⟩ :=
    driver_batch_call_runBlock code hcode args mem sp src ptr hsp hsrc hptr htypes hwret
  have a39 : a[39] = args[39] := keep 39 (by decide)
  have a50 : a[50] = args[50] := keep 50 (by decide)
  have a51 : a[51] = args[51] := keep 51 (by decide)
  have a22 : a[22] = args[22] := keep 22 (by decide)
  have a6 : a[6] = args[6] := keep 6 (by decide)
  obtain ⟨o, hexec, htag, hspout, hpres, htypesout, hframe, hpost⟩ :=
    batch_pushed code hcode hmultiply mem a sp src ptr dst 0x1099cc low
      (by rw [asp]; rfl) (by rw [aptr]; rfl) (by rw [a6]; exact hsrc) hdst aTypes
      (by rw [a39]; exact h39) (by rw [a50]; exact h50) (by rw [a51]; exact h51)
      (a22.trans hdf) (by decide) hstack hroom halign hr hp hsrcsep hptrsep hw hsep
  have ha : driverBatchFrame.Accepts (dialect code) o.tag = true := by rw [htag]; rfl
  have hresume := CFGCall.exec_reaches_resume hexec driverBatchFrame [] ha
  have hstep : LIR.program.step (dialect code) ⟨⟨.l1099c0, args, mem⟩, []⟩ =
      .next ⟨⟨.l109ac0, a, memStore mem (sp - 8) (0x1099cc#64)⟩, [driverBatchFrame]⟩ := by
    rw [Program.step, hcall]
    rfl
  refine ⟨o, (Semantics.Reaches.single hstep).trans hresume, hspout,
    (hpres 15 (by decide)).trans a15, ?_, htypesout, hframe, hpost⟩
  intro r hr
  apply (hpres r ?_).trans (keep r ?_)
  all_goals
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
    omega

end AesGcm.Proofs.Machine.GHASHUpdate
