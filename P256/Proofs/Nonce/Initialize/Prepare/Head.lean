import P256.Proofs.Nonce.Initialize.Prepare.Memory

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Prepare

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

structure InputData [Bindings] (initial s : RamState) (boundary : ReturnBoundary) : Prop where
  stage : Stage initial s boundary
  secret : s.regValue .rsi = initial.regValue .rsi
  output : memLoad s.external (stackPtr s + 192) 64 = initial.regValue .rdi
  length : s.regValue .r11 = 32
  count : s.regValue .r8 = 32
  source : s.regValue .rax = initial.regValue .rcx
  entropy : s.regValue .r9 = 1

structure Inputs [Bindings] (initial s : RamState) (boundary : ReturnBoundary)
    (orderAddress : BitVec 64) : Prop extends InputData initial s boundary where
  order : s.regValue .rdi = orderAddress

theorem head [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} (pre : InitializePre initial boundary orderAddress)
    (stage : Stage initial s boundary) (rip : s.RIP = 0x1077a1)
    (agrees : AgreesExcept (saveFrame initial ++ [.flags]) initial s) :
    ∃ t, Inputs initial t boundary orderAddress ∧ t.RIP = 0x1077b7 := by
  obtain ⟨s1, a1, r1, e1⟩ :=
    (mov_r64_r64_effect_step 0x1077a1 0x48 0xc8 (by simp [RexWPrefix]) rfl).advances
      (readyToStep stage.machine stage.bindingsSupported)
      (programText_slice (programLoaded_codeIn stage.loaded) 0x77a1 _
        (by decide +kernel) (by decide +kernel)) rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x77a4 (by decide)))
  have g1 : AgreesExcept [.reg 0, .rip] s s1 := e1.agrees
  have f1 := stage.after_registers a1 r1 g1 (by simp [Component.Covers]) (by simp)
  obtain ⟨s2, a2, r2, e2⟩ :=
    (mov_r64_r64_effect_step 0x1077a4 0x49 0xd3 (by simp [RexWPrefix]) rfl).advances
      (readyToStep f1.machine f1.bindingsSupported)
      (programText_slice (programLoaded_codeIn f1.loaded) 0x77a4 _
        (by decide +kernel) (by decide +kernel)) e1.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x77a7 (by decide)))
  have g2 : AgreesExcept [.reg 11, .rip] s1 s2 := e2.agrees
  have f2 := f1.after_registers a2 r2 g2 (by simp [Component.Covers]) (by simp)
  obtain ⟨s3, a3, r3, e3⟩ :=
    (mov_m64_r64_effect_step 0x1077a7 0x48 (by simp [RexWPrefix]) 7
      (.sib 4 none 0 (.d32 192)) (by decide +kernel) rfl rfl).advances
      (readyToStep f2.machine f2.bindingsSupported)
      (programText_slice (programLoaded_codeIn f2.loaded) 0x77a7 _
        (by decide +kernel) (by decide +kernel))
      ⟨e2.rip, stack_writable8 pre f2 (by decide) (by decide),
        ScalarFrame.stack_code pre.toCalleePre f2.toFrameState (by decide) (by decide)
          (codeOffset := 0x77a7) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x77af (by decide)))
  have g3 : AgreesExcept [.mem (stackPtr s2 + 192) 8, .rip] s2 s3 := by
    simpa [movM64R64Effect_components, storeAddrAt, AddrMode.addr, AddrMode.reg64,
      Disp.value, stackPtr] using e3.agrees
  have f3 := after_store pre f2 a3 r3 g3 (by decide)
  obtain ⟨s4, a4, r4, e4⟩ :=
    (mov_r64_m64_effect_step 0x1077af 0x48 (by simp [RexWPrefix]) 7
      (.sib 4 none 0 (.d32 296)) (by decide +kernel) rfl rfl).advances
      (readyToStep f3.machine f3.bindingsSupported)
      (programText_slice (programLoaded_codeIn f3.loaded) 0x77af _
        (by decide +kernel) (by decide +kernel)) ⟨e3.rip, argument_readable pre f3⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x77b7 (by decide)))
  have g4 : AgreesExcept [.reg 7, .rip] s3 s4 := e4.agrees
  have f4 := f3.after_registers a4 r4 g4 (by simp [Component.Covers]) (by simp)
  have total := ((g1.trans g2).trans g3).trans g4
  have sp : stackPtr s4 = stackPtr s2 := (g3.trans g4).read (n := 64) (r := 4) (by simp)
  refine ⟨s4, ⟨⟨f4, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩, e4.rip⟩
  · exact (agrees.trans total).read (n := 64) (r := 6) (by simp [saveFrame])
  · rw [sp, g4.external (by simp [Component.Covers])]
    exact e3.writes.trans (((agrees.trans g1).trans g2).read
      (n := 64) (r := 7) (by simp [saveFrame]))
  · exact ((g3.trans g4).read (n := 64) (r := 11) (by simp)).trans
      (e2.writes.trans ((agrees.trans g1).read (n := 64) (r := 2)
        (by simp [saveFrame]) |>.trans pre.secretLength))
  · exact ((agrees.trans total).read (n := 64) (r := 8) (by simp [saveFrame])).trans pre.digestLength
  · exact (((g2.trans g3).trans g4).read (n := 64) (r := 0) (by simp)).trans
      (e1.writes.trans (agrees.read (n := 64) (r := 1) (by simp [saveFrame])))
  · exact ((agrees.trans total).read (n := 64) (r := 9) (by simp [saveFrame])).trans pre.entropyPointer

  · exact e4.writes.trans (argument_order pre f3)

end P256.Proofs.Nonce.Initialize.Prepare
