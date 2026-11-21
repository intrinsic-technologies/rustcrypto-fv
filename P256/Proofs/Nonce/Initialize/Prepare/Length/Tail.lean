import P256.Proofs.Nonce.Initialize.Prepare.Length.Low
import P256.Proofs.Nonce.Initialize.Conversions.ScaleBits
import P256.Proofs.Common.Encoding.Serialize.Tail.Selection.Cmov
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Prepare.Length

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Instructions
open P256.Proofs.Nonce.Initialize.Conversions

theorem tail [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} (pre : InitializePre initial boundary orderAddress)
    (stage : Stage initial s boundary) (rip : s.RIP = 0x1078d2)
    (count : s.regValue .r8 = 32) (bits : s.regValue .rcx = 256)
    (length : s.regValue .r11 = 32) :
    ∃ t, Stage initial t boundary ∧ t.RIP = 0x107916 ∧
      t.regValue .rbp = 0 ∧ t.regValue .rsi = 32 ∧ t.regValue .r9 = 256 ∧
      memLoad t.external (stackPtr s + 176) 64 = 32 ∧
      AgreesExcept [.mem (stackPtr s + 176) 8, .reg 9, .reg 2, .reg 5,
        .reg 6, .flags, .rip] s t := by
  obtain ⟨s1, a1, r1, e1⟩ :=
    (lea_r9d_r8_scale8_effect_step 0x1078d2).advances (readyToStep stage.machine stage.bindingsSupported)
      (programText_slice (programLoaded_codeIn stage.loaded) 0x78d2 _ (by decide +kernel) (by decide +kernel)) rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x78da (by decide)))
  have g1 : AgreesExcept [.reg 9, .rip] s s1 := e1.agrees
  have f1 := stage.after_registers a1 r1 g1 (by simp [Component.Covers]) (by simp)
  have nine1 : s1.regValue .r9 = 256 := by
    have h : s1.regValue .r9 = ((((s.regValue .r8 <<< (3 : Nat)) + 0).setWidth 32).setWidth 64) := e1.writes
    rwa [count] at h
  obtain ⟨s2, a2, r2, e2⟩ :=
    (xor_r32_r32_effect_step 0x1078da 0xd2 rfl).advances (readyToStep f1.machine f1.bindingsSupported)
      (programText_slice (programLoaded_codeIn f1.loaded) 0x78da _ (by decide +kernel) (by decide +kernel)) e1.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x78dc (by decide)))
  have g2 : AgreesExcept [.reg 2, .flags, .rip] s1 s2 := e2.agrees
  have f2 := f1.after_registers a2 r2 g2 (by simp [Component.Covers]) (by simp)
  have two2 : s2.regValue .rdx = 0 := by
    have h := e2.writes
    change s2.regValue .rdx = (((s1.regValue .rdx).setWidth 32) ^^^
      ((s1.regValue .rdx).setWidth 32)).setWidth 64 at h
    simpa using h
  have nine2 : s2.regValue .r9 = 256 := (g2.read (n := 64) (r := 9) (by simp)).trans nine1
  obtain ⟨s3, a3, r3, e3⟩ :=
    (mov_r32_r32_rex_effect_step 0x1078dc 0x44 0xcd (by simp [RexNoWPrefix]) rfl).advances (readyToStep f2.machine f2.bindingsSupported)
      (programText_slice (programLoaded_codeIn f2.loaded) 0x78dc _ (by decide +kernel) (by decide +kernel)) e2.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x78df (by decide)))
  have g3 : AgreesExcept [.reg 5, .rip] s2 s3 := e3.agrees
  have f3 := f2.after_registers a3 r3 g3 (by simp [Component.Covers]) (by simp)
  have bp3 : s3.regValue .rbp = 256 := by
    have h : s3.regValue .rbp = ((s2.regValue .r9).setWidth 32).setWidth 64 := e3.writes
    rwa [nine2] at h
  have cx3 : s3.regValue .rcx = 256 := (((g1.trans g2).trans g3).read (n := 64) (r := 1) (by simp)).trans bits
  obtain ⟨s4, a4, r4, e4⟩ :=
    (sub_r32_r32_effect_step 0x1078df 0xcd rfl).advances (readyToStep f3.machine f3.bindingsSupported)
      (programText_slice (programLoaded_codeIn f3.loaded) 0x78df _ (by decide +kernel) (by decide +kernel)) e3.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x78e1 (by decide)))
  have g4 : AgreesExcept [.reg 5, .flags, .rip] s3 s4 := e4.agrees
  have f4 := f3.after_registers a4 r4 g4 (by simp [Component.Covers]) (by simp)
  have bp4 : s4.regValue .rbp = 0 := by
    have h : s4.regValue .rbp = ((s3.regValue .rbp).setWidth 32 - (s3.regValue .rcx).setWidth 32).setWidth 64 := e4.writes
    rwa [bp3, cx3] at h
  have two4 : s4.regValue .rdx = 0 := ((g3.trans g4).read (n := 64) (r := 2) (by simp)).trans two2
  obtain ⟨s5, a5, r5, e5⟩ :=
    (cmov_r32_r32_effect_step 0x1078e1 0x42 0xea (.inl rfl) rfl).advances (readyToStep f4.machine f4.bindingsSupported)
      (programText_slice (programLoaded_codeIn f4.loaded) 0x78e1 _ (by decide +kernel) (by decide +kernel)) e4.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x78e4 (by decide)))
  have g5 : AgreesExcept [.reg 5, .rip] s4 s5 := e5.agrees
  have f5 := f4.after_registers a5 r5 g5 (by simp [Component.Covers]) (by simp)
  have bp5 : s5.regValue .rbp = 0 := by
    have h : s5.regValue .rbp = ((if (StatusFlags.ofRFLAGS s4.RFLAGS).CF then
      (s4.regValue .rdx).setWidth 32 else (s4.regValue .rbp).setWidth 32).setWidth 64) := e5.writes
    simpa [two4, bp4] using h
  obtain ⟨s6, a6, r6, e6⟩ :=
    (mov_r32_r32_effect_step 0x1078e4 0xea rfl).advances (readyToStep f5.machine f5.bindingsSupported)
      (programText_slice (programLoaded_codeIn f5.loaded) 0x78e4 _ (by decide +kernel) (by decide +kernel)) e5.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x78e6 (by decide)))
  have g6 : AgreesExcept [.reg 2, .rip] s5 s6 := e6.agrees
  have f6 := f5.after_registers a6 r6 g6 (by simp [Component.Covers]) (by simp)
  have two6 : s6.regValue .rdx = 0 := by
    have h : s6.regValue .rdx = ((s5.regValue .rbp).setWidth 32).setWidth 64 := e6.writes
    rwa [bp5] at h
  obtain ⟨s7, a7, r7, e7⟩ :=
    (shr_r32_imm8_effect_step 0x1078e6 0xea 3 rfl rfl).advances (readyToStep f6.machine f6.bindingsSupported)
      (programText_slice (programLoaded_codeIn f6.loaded) 0x78e6 _ (by decide +kernel) (by decide +kernel)) e6.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x78e9 (by decide)))
  have g7 : AgreesExcept [.reg 2, .flags, .rip] s6 s7 := e7.agrees
  have f7 := f6.after_registers a7 r7 g7 (by simp [Component.Covers]) (by simp)
  have zero7 : (StatusFlags.ofRFLAGS s7.RFLAGS).ZF = true := by
    have h := e7.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS s7.RFLAGS).ZF = (((s6.regValue .rdx).setWidth 32 >>> (3 : Nat)) == 0) at h
    rwa [two6] at h
  have sp7 : stackPtr s7 = stackPtr s := ((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).read (n := 64) (r := 4) (by simp)
  have eleven7 : s7.regValue .r11 = 32 :=
    ((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).read (n := 64) (r := 11) (by simp) |>.trans length
  obtain ⟨s8, a8, r8, e8⟩ :=
    (mov_m64_r64_effect_step 0x1078e9 0x4c (by simp [RexWPrefix]) 3
      (.sib 4 none 0 (.d32 176)) (by decide +kernel) rfl rfl).advances (readyToStep f7.machine f7.bindingsSupported)
      (programText_slice (programLoaded_codeIn f7.loaded) 0x78e9 _ (by decide +kernel) (by decide +kernel)) ⟨e7.rip, stack_writable8 pre f7 (by decide) (by decide), by
        change RangeApart (stackPtr s7 + 176) 8 0x1078e9 8
        exact ScalarFrame.stack_code (offset := 176) (len := 8) (codeOffset := 0x78e9)
          (codeLen := 8) pre.toCalleePre f7.toFrameState (by decide) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x78f1 (by decide)))
  have g8 : AgreesExcept [.mem (stackPtr s7 + 176) 8, .rip] s7 s8 := by
    simpa [movM64R64Effect_components, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e8.agrees
  have f8 := after_store pre f7 a8 r8 g8 (by decide)
  have word8 : memLoad s8.external (stackPtr s + 176) 64 = 32 := by
    have h : memLoad s8.external (stackPtr s7 + 176) 64 = s7.regValue .r11 := e8.writes
    rwa [sp7, eleven7] at h
  obtain ⟨s9, step9, r9, raw9⟩ := jcc_rel8_effect_step 0x1078f1 4 0x20 s8 r8
    (programText_slice (programLoaded_codeIn f8.loaded) 0x78f1 _ (by decide +kernel) (by decide +kernel))
    ⟨e8.rip, fun _ => by decide +kernel⟩
  have zero8 : (StatusFlags.ofRFLAGS s8.RFLAGS).ZF = true := by
    rw [g8.rflags (by simp) (by simp)]
    exact zero7
  have e9 := jccEffect_taken (show condHolds 4 (StatusFlags.ofRFLAGS s8.RFLAGS) = true from zero8) raw9
  have a9 : Advances boundary 1 s8 s9 := Advances.of_step step9 (.inl (by
    rw [e9.rip]
    exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7913 (by decide))))
  have g9 : AgreesExcept [.rip] s8 s9 := e9.agrees
  have f9 := f8.after_registers a9 r9 g9 (by simp [Component.Covers]) (by simp)
  obtain ⟨s10, a10, r10, e10⟩ :=
    (mov_r64_r64_effect_step 0x107913 0x4c 0xc6 (by simp [RexWPrefix]) rfl).advances (readyToStep f9.machine f9.bindingsSupported)
      (programText_slice (programLoaded_codeIn f9.loaded) 0x7913 _ (by decide +kernel) (by decide +kernel)) e9.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7916 (by decide)))
  have g10 : AgreesExcept [.reg 6, .rip] s9 s10 := e10.agrees
  have f10 := f9.after_registers a10 r10 g10 (by simp [Component.Covers]) (by simp)
  have total := (((((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).trans g8).trans g9).trans g10)
  refine ⟨s10, f10, e10.rip, ?_, ?_, ?_, ?_, ?_⟩
  · exact (((((g6.trans g7).trans g8).trans g9).trans g10).read (n := 64) (r := 5) (by simp)).trans bp5
  · exact e10.writes.trans ((((((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).trans g8).trans g9).read (n := 64) (r := 8) (by simp)).trans count)
  · exact (((((((((g2.trans g3).trans g4).trans g5).trans g6).trans g7).trans g8).trans g9).trans g10).read (n := 64) (r := 9) (by simp)).trans nine1
  · rw [(g9.trans g10).external (by simp [Component.Covers])]
    exact word8
  · exact total.mono (by simp only [sp7]; simp)

end P256.Proofs.Nonce.Initialize.Prepare.Length
