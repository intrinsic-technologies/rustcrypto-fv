import P256.Proofs.Sec1Serialize.Tail.Finish.CopySetup
import P256.Proofs.Program.Copy

set_option autoImplicit false

namespace P256.Proofs.Sec1Serialize

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

theorem copy_result [Bindings] {s v : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} (pre : CalleePre s boundary 0x110d70 72 65 328)
    (setup : CopyEntry s v boundary bytes) :
    ∃ w, FrameState s w 65 328 312 ∧ (∃ n, Advances boundary n s w) ∧
      w.RIP = 0x1111e1 ∧ w.regValue .rbp = s.regValue .rdi ∧
      (registerRegion s .rdi 65).HasBytes w.external bytes := by
  obtain ⟨w, result, copied, agrees⟩ := memcpy_correct setup.pre setup.count (by decide)
  have memory : MemoryWriteFrame v w
      #v[registerRegion s .rdi 65, workRegion s 328] := by
    apply agrees.memoryWriteFrame
    intro c hc a ha
    simp only [Copy.copyComponents, Copy.registerComponents, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with ((rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl)) | (rfl | rfl)
    all_goals try exact ha.elim
    refine ⟨registerRegion s .rdi 65, by simp, ?_⟩
    obtain ⟨i, hi, he⟩ := ha
    rw [he, setup.destination]
    exact memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) hi
  have state : FrameState s w 65 328 312 := by
    refine ⟨result.bindingsSupported, result.machine, result.loaded, result.directionFlag,
      fun a ha => result.allocated a (setup.state.allocated a ha),
      memoryWriteFrame_trans setup.state.frame (output_work_frame pre memory), ?_, ?_, ?_,
      result.mxcsr.trans setup.state.mxcsr, result.fp87.trans setup.state.fp87⟩
    · have hsp : stackPtr w = stackPtr v + 8 := result.rsp
      rw [hsp, setup.state.rsp]
      simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
      rfl
    · intro entry he
      have hb : entry.2 ≤ 48 := by
        simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at he
        rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact (output_work_read pre (by decide) memory hb (by omega)).trans (setup.state.saved entry he)
    · have h := output_work_read pre (by decide) memory (offset := 0) (n := 64) (by decide) (by decide)
      simp only [BitVec.sub_zero] at h
      exact h.trans setup.state.returnAddress
  refine ⟨w, state, ?_, result.rip.trans setup.returnAddress, ?_, ?_⟩
  · obtain ⟨n, hn⟩ := setup.execution
    obtain ⟨m, hm⟩ := result.execution
    exact ⟨n + m, hn.trans hm⟩
  · exact (agrees.read (n := 64) (r := 5) (by simp [Copy.copyComponents, Copy.registerComponents])).trans setup.savedDestination
  · refine ⟨setup.selected.1, ?_⟩
    intro i
    have hsize : bytes.size = 65 := setup.selected.1
    have hc := copied i.val (hsize ▸ i.isLt)
    rw [setup.destination, setup.source] at hc
    have hb := setup.selected.2 i
    change v.external[BitVec.ofNat 64 ((stackPtr s - 296).toNat + i.val)]? = _ at hb
    change w.external[BitVec.ofNat 64 ((s.regValue .rdi).toNat + i.val)]? = _
    simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hb ⊢
    exact hc.trans hb

end P256.Proofs.Sec1Serialize
