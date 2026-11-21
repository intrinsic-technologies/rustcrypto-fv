import P256.Proofs.Nonce.Initialize.Prepare.Head
import P256.Proofs.Common.Instructions.Bswap

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Prepare

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Instructions

structure OrderLoaded [Bindings] (initial s : RamState) (boundary : ReturnBoundary)
    (orderAddress : BitVec 64) : Prop extends InputData initial s boundary where
  order0 : s.regValue .r15 = memLoad initial.external orderAddress 64
  order1 : s.regValue .r14 = memLoad initial.external (orderAddress + 8) 64
  order2 : s.regValue .r13 = memLoad initial.external (orderAddress + 16) 64
  order3 : s.regValue .rbp = memLoad initial.external (orderAddress + 24) 64

theorem load_order [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} (pre : InitializePre initial boundary orderAddress)
    (state : Inputs initial s boundary orderAddress) (rip : s.RIP = 0x1077b7) :
    ∃ t, OrderLoaded initial t boundary orderAddress ∧ t.RIP = 0x1077de := by
  have pointer1 : s.regValue .rdi = orderAddress := state.order
  obtain ⟨s1, a1, r1, e1⟩ :=
    (mov_r64_m64_effect_step 0x1077b7 0x4c (by simp [RexWPrefix]) 7
      (.base 7 .none) (by decide +kernel) rfl rfl).advances (readyToStep state.stage.machine state.stage.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.stage.loaded) 0x77b7 _
        (by decide +kernel) (by decide +kernel)) ⟨rip, by
        change MemReadable s (s.regValue .rdi + 0) 8
        rw [pointer1]
        exact order_readable pre state.stage 0 (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x77ba (by decide)))
  have g1 : AgreesExcept [.reg 15, .rip] s s1 := e1.agrees
  have f1 := state.stage.after_registers a1 r1 g1 (by simp [Component.Covers]) (by simp)
  have word1 : s1.regValue .r15 = memLoad initial.external (orderAddress + 0) 64 := by
    have h : s1.regValue .r15 = memLoad s.external (s.regValue .rdi + 0) 64 := e1.writes
    rw [pointer1] at h
    exact h.trans (order_word pre state.stage 0 (by decide))
  have pointer2 : s1.regValue .rdi = orderAddress := (g1.read (n := 64) (r := 7) (by simp)).trans state.order
  obtain ⟨s2, a2, r2, e2⟩ :=
    (mov_r64_m64_effect_step 0x1077ba 0x4c (by simp [RexWPrefix]) 6
      (.base 7 (.d8 8)) (by decide +kernel) rfl rfl).advances (readyToStep f1.machine f1.bindingsSupported)
      (programText_slice (programLoaded_codeIn f1.loaded) 0x77ba _
        (by decide +kernel) (by decide +kernel)) ⟨e1.rip, by
        change MemReadable s1 (s1.regValue .rdi + 8) 8
        rw [pointer2]
        exact order_readable pre f1 8 (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x77be (by decide)))
  have g2 : AgreesExcept [.reg 14, .rip] s1 s2 := e2.agrees
  have f2 := f1.after_registers a2 r2 g2 (by simp [Component.Covers]) (by simp)
  have word2 : s2.regValue .r14 = memLoad initial.external (orderAddress + 8) 64 := by
    have h : s2.regValue .r14 = memLoad s1.external (s1.regValue .rdi + 8) 64 := e2.writes
    rw [pointer2] at h
    exact h.trans (order_word pre f1 8 (by decide))
  obtain ⟨s3, a3, r3, e3⟩ :=
    (mov_r64_r64_effect_step 0x1077be 0x4c 0xf9 (by simp [RexWPrefix]) rfl).advances (readyToStep f2.machine f2.bindingsSupported)
      (programText_slice (programLoaded_codeIn f2.loaded) 0x77be _
        (by decide +kernel) (by decide +kernel)) e2.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x77c1 (by decide)))
  have g3 : AgreesExcept [.reg 1, .rip] s2 s3 := e3.agrees
  have f3 := f2.after_registers a3 r3 g3 (by simp [Component.Covers]) (by simp)
  obtain ⟨s4, a4, r4, e4⟩ :=
    (bswap_r64_effect_step 0x1077c1 1).advances (readyToStep f3.machine f3.bindingsSupported)
      (programText_slice (programLoaded_codeIn f3.loaded) 0x77c1 _
        (by decide +kernel) (by decide +kernel)) e3.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x77c4 (by decide)))
  have g4 : AgreesExcept [.reg 1, .rip] s3 s4 := e4.agrees
  have f4 := f3.after_registers a4 r4 g4 (by simp [Component.Covers]) (by simp)
  obtain ⟨s5, a5, r5, e5⟩ :=
    (mov_r64_r64_effect_step 0x1077c4 0x4c 0xf2 (by simp [RexWPrefix]) rfl).advances (readyToStep f4.machine f4.bindingsSupported)
      (programText_slice (programLoaded_codeIn f4.loaded) 0x77c4 _
        (by decide +kernel) (by decide +kernel)) e4.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x77c7 (by decide)))
  have g5 : AgreesExcept [.reg 2, .rip] s4 s5 := e5.agrees
  have f5 := f4.after_registers a5 r5 g5 (by simp [Component.Covers]) (by simp)
  obtain ⟨s6, a6, r6, e6⟩ :=
    (bswap_r64_effect_step 0x1077c7 2).advances (readyToStep f5.machine f5.bindingsSupported)
      (programText_slice (programLoaded_codeIn f5.loaded) 0x77c7 _
        (by decide +kernel) (by decide +kernel)) e5.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x77ca (by decide)))
  have g6 : AgreesExcept [.reg 2, .rip] s5 s6 := e6.agrees
  have f6 := f5.after_registers a6 r6 g6 (by simp [Component.Covers]) (by simp)
  have pointer7 : s6.regValue .rdi = orderAddress := ((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).read (n := 64) (r := 7) (by simp)).trans state.order
  obtain ⟨s7, a7, r7, e7⟩ :=
    (mov_r64_m64_effect_step 0x1077ca 0x4c (by simp [RexWPrefix]) 5
      (.base 7 (.d8 16)) (by decide +kernel) rfl rfl).advances (readyToStep f6.machine f6.bindingsSupported)
      (programText_slice (programLoaded_codeIn f6.loaded) 0x77ca _
        (by decide +kernel) (by decide +kernel)) ⟨e6.rip, by
        change MemReadable s6 (s6.regValue .rdi + 16) 8
        rw [pointer7]
        exact order_readable pre f6 16 (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x77ce (by decide)))
  have g7 : AgreesExcept [.reg 13, .rip] s6 s7 := e7.agrees
  have f7 := f6.after_registers a7 r7 g7 (by simp [Component.Covers]) (by simp)
  have word7 : s7.regValue .r13 = memLoad initial.external (orderAddress + 16) 64 := by
    have h : s7.regValue .r13 = memLoad s6.external (s6.regValue .rdi + 16) 64 := e7.writes
    rw [pointer7] at h
    exact h.trans (order_word pre f6 16 (by decide))
  obtain ⟨s8, a8, r8, e8⟩ :=
    (mov_r64_r64_effect_step 0x1077ce 0x4d 0xea (by simp [RexWPrefix]) rfl).advances (readyToStep f7.machine f7.bindingsSupported)
      (programText_slice (programLoaded_codeIn f7.loaded) 0x77ce _
        (by decide +kernel) (by decide +kernel)) e7.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x77d1 (by decide)))
  have g8 : AgreesExcept [.reg 10, .rip] s7 s8 := e8.agrees
  have f8 := f7.after_registers a8 r8 g8 (by simp [Component.Covers]) (by simp)
  obtain ⟨s9, a9, r9, e9⟩ :=
    (bswap_r64_effect_step 0x1077d1 10).advances (readyToStep f8.machine f8.bindingsSupported)
      (programText_slice (programLoaded_codeIn f8.loaded) 0x77d1 _
        (by decide +kernel) (by decide +kernel)) e8.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x77d4 (by decide)))
  have g9 : AgreesExcept [.reg 10, .rip] s8 s9 := e9.agrees
  have f9 := f8.after_registers a9 r9 g9 (by simp [Component.Covers]) (by simp)
  have pointer10 : s9.regValue .rdi = orderAddress := (((((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).trans g8).trans g9).read (n := 64) (r := 7) (by simp)).trans state.order
  obtain ⟨s10, a10, r10, e10⟩ :=
    (mov_r64_m64_effect_step 0x1077d4 0x48 (by simp [RexWPrefix]) 5
      (.base 7 (.d8 24)) (by decide +kernel) rfl rfl).advances (readyToStep f9.machine f9.bindingsSupported)
      (programText_slice (programLoaded_codeIn f9.loaded) 0x77d4 _
        (by decide +kernel) (by decide +kernel)) ⟨e9.rip, by
        change MemReadable s9 (s9.regValue .rdi + 24) 8
        rw [pointer10]
        exact order_readable pre f9 24 (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x77d8 (by decide)))
  have g10 : AgreesExcept [.reg 5, .rip] s9 s10 := e10.agrees
  have f10 := f9.after_registers a10 r10 g10 (by simp [Component.Covers]) (by simp)
  have word10 : s10.regValue .rbp = memLoad initial.external (orderAddress + 24) 64 := by
    have h : s10.regValue .rbp = memLoad s9.external (s9.regValue .rdi + 24) 64 := e10.writes
    rw [pointer10] at h
    exact h.trans (order_word pre f9 24 (by decide))
  obtain ⟨s11, a11, r11, e11⟩ :=
    (mov_r64_r64_effect_step 0x1077d8 0x48 0xef (by simp [RexWPrefix]) rfl).advances (readyToStep f10.machine f10.bindingsSupported)
      (programText_slice (programLoaded_codeIn f10.loaded) 0x77d8 _
        (by decide +kernel) (by decide +kernel)) e10.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x77db (by decide)))
  have g11 : AgreesExcept [.reg 7, .rip] s10 s11 := e11.agrees
  have f11 := f10.after_registers a11 r11 g11 (by simp [Component.Covers]) (by simp)
  obtain ⟨s12, a12, r12, e12⟩ :=
    (bswap_r64_effect_step 0x1077db 7).advances (readyToStep f11.machine f11.bindingsSupported)
      (programText_slice (programLoaded_codeIn f11.loaded) 0x77db _
        (by decide +kernel) (by decide +kernel)) e11.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x77de (by decide)))
  have g12 : AgreesExcept [.reg 7, .rip] s11 s12 := e12.agrees
  have f12 := f11.after_registers a12 r12 g12 (by simp [Component.Covers]) (by simp)
  have total := (((((((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).trans g8).trans g9).trans g10).trans g11).trans g12)
  have inputs : InputData initial s12 boundary := by
    refine ⟨f12, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (total.read (n := 64) (r := 6) (by simp)).trans state.secret
    · have sp : stackPtr s12 = stackPtr s := total.read (n := 64) (r := 4) (by simp)
      rw [sp, total.external (by simp [Component.Covers])]
      exact state.output
    · exact (total.read (n := 64) (r := 11) (by simp)).trans state.length
    · exact (total.read (n := 64) (r := 8) (by simp)).trans state.count
    · exact (total.read (n := 64) (r := 0) (by simp)).trans state.source
    · exact (total.read (n := 64) (r := 9) (by simp)).trans state.entropy
  have hz : orderAddress + (0 : BitVec 64) = orderAddress := BitVec.add_zero _
  rw [hz] at word1
  refine ⟨s12, ⟨inputs, ?_, ?_, ?_, ?_⟩, e12.rip⟩
  · exact (((((((((((g2.trans g3).trans g4).trans g5).trans g6).trans g7).trans g8).trans g9).trans g10).trans g11).trans g12).read (n := 64) (r := 15) (by simp)).trans word1
  · exact ((((((((((g3.trans g4).trans g5).trans g6).trans g7).trans g8).trans g9).trans g10).trans g11).trans g12).read (n := 64) (r := 14) (by simp)).trans word2
  · exact (((((g8.trans g9).trans g10).trans g11).trans g12).read (n := 64) (r := 13) (by simp)).trans word7
  · exact ((g11.trans g12).read (n := 64) (r := 5) (by simp)).trans word10

end P256.Proofs.Nonce.Initialize.Prepare
