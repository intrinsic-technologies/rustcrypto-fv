import P256.Proofs.Nonce.Initialize.Prepare.Load
import P256.Proofs.Common.Encoding.Serialize.Convert.SavePointer

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Prepare

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Common.Encoding.Serialize (read_mem_of_agrees)

theorem store_order [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} (pre : InitializePre initial boundary orderAddress)
    (state : OrderLoaded initial s boundary orderAddress) (rip : s.RIP = 0x1077de) :
    ∃ t, OrderLoaded initial t boundary orderAddress ∧ t.RIP = 0x1077fe := by
  obtain ⟨s1, a1, r1, e1⟩ :=
    (mov_m64_r64_effect_step 0x1077de 0x48 (by simp [RexWPrefix]) 7
      (.sib 4 none 0 (.d32 200)) (by decide +kernel) rfl rfl).advances
      (readyToStep state.stage.machine state.stage.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.stage.loaded) 0x77de _
        (by decide +kernel) (by decide +kernel))
      ⟨rip, stack_writable8 pre state.stage (offset := 200) (by decide) (by decide),
        ScalarFrame.stack_code pre.toCalleePre state.stage.toFrameState (offset := 200) (by decide) (by decide) (codeOffset := 0x77de) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x77e6 (by decide)))
  have raw1 : AgreesExcept [.mem (stackPtr s + 200) 8, .rip] s s1 := by simpa [movM64R64Effect_components, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e1.agrees
  have f1 := after_store pre state.stage a1 r1 raw1 (by decide)
  have g1 := raw1
  obtain ⟨s2, a2, r2, e2⟩ :=
    (mov_m64_r64_effect_step 0x1077e6 0x4c (by simp [RexWPrefix]) 2
      (.sib 4 none 0 (.d32 208)) (by decide +kernel) rfl rfl).advances
      (readyToStep f1.machine f1.bindingsSupported)
      (programText_slice (programLoaded_codeIn f1.loaded) 0x77e6 _
        (by decide +kernel) (by decide +kernel))
      ⟨e1.rip, stack_writable8 pre f1 (offset := 208) (by decide) (by decide),
        ScalarFrame.stack_code pre.toCalleePre f1.toFrameState (offset := 208) (by decide) (by decide) (codeOffset := 0x77e6) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x77ee (by decide)))
  have raw2 : AgreesExcept [.mem (stackPtr s1 + 208) 8, .rip] s1 s2 := by simpa [movM64R64Effect_components, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e2.agrees
  have f2 := after_store pre f1 a2 r2 raw2 (by decide)
  have sp2 : stackPtr s1 = stackPtr s := g1.read (n := 64) (r := 4) (by simp)
  have g2 : AgreesExcept [.mem (stackPtr s + 208) 8, .rip] s1 s2 := by
    simpa only [sp2] using raw2
  obtain ⟨s3, a3, r3, e3⟩ :=
    (mov_m64_r64_effect_step 0x1077ee 0x48 (by simp [RexWPrefix]) 2
      (.sib 4 none 0 (.d32 216)) (by decide +kernel) rfl rfl).advances
      (readyToStep f2.machine f2.bindingsSupported)
      (programText_slice (programLoaded_codeIn f2.loaded) 0x77ee _
        (by decide +kernel) (by decide +kernel))
      ⟨e2.rip, stack_writable8 pre f2 (offset := 216) (by decide) (by decide),
        ScalarFrame.stack_code pre.toCalleePre f2.toFrameState (offset := 216) (by decide) (by decide) (codeOffset := 0x77ee) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x77f6 (by decide)))
  have raw3 : AgreesExcept [.mem (stackPtr s2 + 216) 8, .rip] s2 s3 := by simpa [movM64R64Effect_components, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e3.agrees
  have f3 := after_store pre f2 a3 r3 raw3 (by decide)
  have sp3 : stackPtr s2 = stackPtr s := (g1.trans g2).read (n := 64) (r := 4) (by simp)
  have g3 : AgreesExcept [.mem (stackPtr s + 216) 8, .rip] s2 s3 := by
    simpa only [sp3] using raw3
  obtain ⟨s4, a4, r4, e4⟩ :=
    (mov_m64_r64_effect_step 0x1077f6 0x48 (by simp [RexWPrefix]) 1
      (.sib 4 none 0 (.d32 224)) (by decide +kernel) rfl rfl).advances
      (readyToStep f3.machine f3.bindingsSupported)
      (programText_slice (programLoaded_codeIn f3.loaded) 0x77f6 _
        (by decide +kernel) (by decide +kernel))
      ⟨e3.rip, stack_writable8 pre f3 (offset := 224) (by decide) (by decide),
        ScalarFrame.stack_code pre.toCalleePre f3.toFrameState (offset := 224) (by decide) (by decide) (codeOffset := 0x77f6) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x77fe (by decide)))
  have raw4 : AgreesExcept [.mem (stackPtr s3 + 224) 8, .rip] s3 s4 := by simpa [movM64R64Effect_components, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e4.agrees
  have f4 := after_store pre f3 a4 r4 raw4 (by decide)
  have sp4 : stackPtr s3 = stackPtr s := ((g1.trans g2).trans g3).read (n := 64) (r := 4) (by simp)
  have g4 : AgreesExcept [.mem (stackPtr s + 224) 8, .rip] s3 s4 := by
    simpa only [sp4] using raw4
  have total := (((g1.trans g2).trans g3).trans g4)
  refine ⟨s4, ⟨⟨f4, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩, e4.rip⟩
  · exact (total.read (n := 64) (r := 6) (by simp)).trans state.secret
  · have sp : stackPtr s4 = stackPtr s := total.read (n := 64) (r := 4) (by simp)
    rw [sp]
    apply Eq.trans _ state.output
    apply read_mem_of_agrees total
    intro i hi c hc
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with (((rfl | rfl) | (rfl | rfl)) | (rfl | rfl)) | (rfl | rfl)
    all_goals try exact id
    all_goals rintro ⟨j, hj, he⟩
    all_goals apply OffsetsApart.ne (base := stackPtr s) (hi := hi) (hj := hj) (hl := by decide) _ he
    all_goals unfold OffsetsApart; decide +kernel
  · exact (total.read (n := 64) (r := 11) (by simp)).trans state.length
  · exact (total.read (n := 64) (r := 8) (by simp)).trans state.count
  · exact (total.read (n := 64) (r := 0) (by simp)).trans state.source
  · exact (total.read (n := 64) (r := 9) (by simp)).trans state.entropy
  · exact (total.read (n := 64) (r := 15) (by simp)).trans state.order0
  · exact (total.read (n := 64) (r := 14) (by simp)).trans state.order1
  · exact (total.read (n := 64) (r := 13) (by simp)).trans state.order2
  · exact (total.read (n := 64) (r := 5) (by simp)).trans state.order3

end P256.Proofs.Nonce.Initialize.Prepare
