import P256.Proofs.Common.Encoding.Parser.ByteStore
import P256.Proofs.Nonce.Fill.Tail.Decode.Scan.State
import P256.Proofs.Nonce.Initialize.Conversions.Bsr.Effect
import P256.Proofs.Nonce.Initialize.Conversions.XorImmediate
import P256.Proofs.Nonce.Initialize.Conversions.Neg32
import P256.Proofs.Common.Instructions.Cmov32
import P256.Proofs.Common.Instructions.Setb.Triple
import P256.Proofs.Common.Instructions.Setb.Memory.Triple
import P256.Proofs.Common.Instructions.Carry.Effect
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.And.Generated.Imm8.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Sub.Generated.RR.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Instructions.NopMem.Triple

import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill.Tail.Decode.Scan

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Proofs.Common.Instructions P256.Proofs.Nonce.Initialize.Conversions.Bsr
open P256.Proofs.Nonce.Initialize.Conversions.XorImmediate P256.Proofs.Common.Instructions.Setb
open P256.Proofs.Nonce.Initialize.Conversions.Neg32

theorem head [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} {original state : Nonce.State}
    (pre : Pre initial boundary orderAddress original)
    (input : Updated initial s orderAddress state) :
    ∃ t, Advances boundary 11 s t ∧ ScanState initial t orderAddress state ∧
      t.RIP = 0x107419 ∧
      t.regValue .r15 = orderAddress ∧
      t.regValue .rcx = 0xffffffff00000000 ∧
      t.regValue .rdx = 0 ∧
      t.regValue .rax = 0 ∧
      t.regValue .r12 = frameBase initial + 8 := by
  let s0 := s
  have f0 : ScanState initial s0 orderAddress state :=
    ⟨input.toFrame, input.toSlots, input.generator, input.output⟩
  obtain ⟨s1, a1, ready1, e1⟩ :=
    (mov_r64_m64_effect_step 0x1073eb 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 144)) (by decide +kernel) rfl rfl).advances
      (readyToStep f0.machine f0.bindingsSupported)
      (programText_slice (programLoaded_codeIn f0.loaded) 0x73eb _
        (by decide +kernel) (by decide +kernel)) ⟨input.rip, by
        change MemReadable s0 (stackPtr s0 + 144) 8
        exact Fill.stack_readable pre f0.toFrame (offset := 144) (len := 8) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x73f3 (by decide)))
  have g1 : AgreesExcept [.reg 0, .rip] s0 s1 := e1.agrees
  have f1 := f0.after_registers ready1 g1 (by simp [Component.Covers]) (by simp)
  have h1_rax : s1.regValue .rax = initial.regValue .rdi := by
    have h : s1.regValue .rax = memLoad s0.external (stackPtr s0 + 144) 64 := e1.writes
    rw [f0.rsp, f0.generatorPointerSlot] at h
    exact h
  obtain ⟨s2, a2, ready2, e2⟩ :=
    (mov_r64_m64_effect_step 0x1073f3 0x4c (by simp [RexWPrefix]) 7 (.base 0 .none) (by decide +kernel) rfl rfl).advances
      (readyToStep f1.machine f1.bindingsSupported)
      (programText_slice (programLoaded_codeIn f1.loaded) 0x73f3 _
        (by decide +kernel) (by decide +kernel)) ⟨e1.rip, by
        change MemReadable s1 ((s1.regValue .rax) + 0) 8
        simpa using (show MemReadable s1 (s1.regValue .rax) 8 from by
          rw [h1_rax]
          exact readable_of_grow (memoryRegion_memReadable pre.outputBounded pre.outputAllocated (Nat.le_refl _) (by change (initial.regValue .rdi).toNat + 8 ≤ (initial.regValue .rdi).toNat + 72; omega)) f1.allocated)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x73f6 (by decide)))
  have g2 : AgreesExcept [.reg 15, .rip] s1 s2 := e2.agrees
  have f2 := f1.after_registers ready2 g2 (by simp [Component.Covers]) (by simp)
  have h2_r15 : s2.regValue .r15 = orderAddress := by
    have h : s2.regValue .r15 = memLoad s1.external (s1.regValue .rax + 0) 64 := e2.writes
    have zeroAddr : (s1.regValue .rax + 0 : BitVec 64) = s1.regValue .rax := BitVec.add_zero _
    rw [zeroAddr] at h
    rw [h1_rax, f1.generator.1] at h
    exact h
  have h2_rax : s2.regValue .rax = initial.regValue .rdi := (g2.read (n := 64) (r := 0) (by simp)).trans h1_rax
  obtain ⟨s3, a3, ready3, e3⟩ :=
    (mov_r64_m64_effect_step 0x1073f6 0x49 (by simp [RexWPrefix]) 1 (.base 15 (.d8 24)) (by decide +kernel) rfl rfl).advances
      (readyToStep f2.machine f2.bindingsSupported)
      (programText_slice (programLoaded_codeIn f2.loaded) 0x73f6 _
        (by decide +kernel) (by decide +kernel)) ⟨e2.rip, by
        change MemReadable s2 (s2.regValue .r15 + 24) 8
        exact by
          rw [h2_r15]
          exact f2.order_readable pre (offset := 24) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x73fa (by decide)))
  have g3 : AgreesExcept [.reg 1, .rip] s2 s3 := e3.agrees
  have f3 := f2.after_registers ready3 g3 (by simp [Component.Covers]) (by simp)
  have h3_rcx : s3.regValue .rcx = 0xffffffff00000000 := by
    have h : s3.regValue .rcx = memLoad s2.external (s2.regValue .r15 + 24) 64 := e3.writes
    rw [h2_r15] at h
    exact h.trans ((f2.generator.2.1.memLoad_limb 3 (by decide)).trans (by decide +kernel))
  have h3_rax : s3.regValue .rax = initial.regValue .rdi := (g3.read (n := 64) (r := 0) (by simp)).trans h2_rax
  have h3_r15 : s3.regValue .r15 = orderAddress := (g3.read (n := 64) (r := 15) (by simp)).trans h2_r15
  obtain ⟨s4, a4, ready4, e4⟩ :=
    (mov_r32_imm32_effect_step 0x1073fa 0xba (by decide) 127).advances
      (readyToStep f3.machine f3.bindingsSupported)
      (programText_slice (programLoaded_codeIn f3.loaded) 0x73fa _
        (by decide +kernel) (by decide +kernel)) e3.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x73ff (by decide)))
  have g4 : AgreesExcept [.reg 2, .rip] s3 s4 := e4.agrees
  have f4 := f3.after_registers ready4 g4 (by simp [Component.Covers]) (by simp)
  have h4_rdx : s4.regValue .rdx = 127 := by
    have h : s4.regValue .rdx = 127 := e4.writes
    exact h
  have h4_rax : s4.regValue .rax = initial.regValue .rdi := (g4.read (n := 64) (r := 0) (by simp)).trans h3_rax
  have h4_r15 : s4.regValue .r15 = orderAddress := (g4.read (n := 64) (r := 15) (by simp)).trans h3_r15
  have h4_rcx : s4.regValue .rcx = 0xffffffff00000000 := (g4.read (n := 64) (r := 1) (by simp)).trans h3_rcx
  obtain ⟨s5, a5, ready5, e5⟩ :=
    (bsr_r64_r64_effect_step 0x1073ff 0x48 0xd1 (by simp [RexWPrefix]) rfl).advances
      (readyToStep f4.machine f4.bindingsSupported)
      (programText_slice (programLoaded_codeIn f4.loaded) 0x73ff _
        (by decide +kernel) (by decide +kernel)) e4.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7403 (by decide)))
  have g5 : AgreesExcept [.reg 2, .flags, .rip] s4 s5 := e5.agrees
  have f5 := f4.after_registers ready5 g5 (by simp [Component.Covers]) (by simp)
  have h5_rdx : s5.regValue .rdx = 63 := by
    have h : s5.regValue .rdx = (bsrSpec64 (s4.regValue .rdx) (s4.regValue .rcx)).1 := e5.writes
    rw [h4_rcx, h4_rdx] at h
    exact h.trans (by decide +kernel)
  have h5_rax : s5.regValue .rax = initial.regValue .rdi := (g5.read (n := 64) (r := 0) (by simp)).trans h4_rax
  have h5_r15 : s5.regValue .r15 = orderAddress := (g5.read (n := 64) (r := 15) (by simp)).trans h4_r15
  have h5_rcx : s5.regValue .rcx = 0xffffffff00000000 := (g5.read (n := 64) (r := 1) (by simp)).trans h4_rcx
  obtain ⟨s6, a6, ready6, e6⟩ :=
    (xor_r32_imm8_effect_step 0x107403 0xf2 63 rfl rfl).advances
      (readyToStep f5.machine f5.bindingsSupported)
      (programText_slice (programLoaded_codeIn f5.loaded) 0x7403 _
        (by decide +kernel) (by decide +kernel)) e5.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7406 (by decide)))
  have g6 : AgreesExcept [.reg 2, .flags, .rip] s5 s6 := e6.agrees
  have f6 := f5.after_registers ready6 g6 (by simp [Component.Covers]) (by simp)
  have h6_rdx : s6.regValue .rdx = 0 := by
    have h : s6.regValue .rdx = ((s5.regValue .rdx).setWidth 32 ^^^ 63).setWidth 64 := e6.writes
    rw [h5_rdx] at h
    exact h
  have h6_rax : s6.regValue .rax = initial.regValue .rdi := (g6.read (n := 64) (r := 0) (by simp)).trans h5_rax
  have h6_r15 : s6.regValue .r15 = orderAddress := (g6.read (n := 64) (r := 15) (by simp)).trans h5_r15
  have h6_rcx : s6.regValue .rcx = 0xffffffff00000000 := (g6.read (n := 64) (r := 1) (by simp)).trans h5_rcx
  obtain ⟨s7, a7, ready7, e7⟩ :=
    (mov_m8_imm8_effect_step 0x107406 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl 1).advances
      (readyToStep f6.machine f6.bindingsSupported)
      (programText_slice (programLoaded_codeIn f6.loaded) 0x7406 _
        (by decide +kernel) (by decide +kernel)) ⟨e6.rip, by
        change MemWritable s6 (stackPtr s6 + 8) 1
        exact f6.stack_writable1 pre, by
        exact Fill.stack_code pre f6.toFrame (offset := 8) (len := 1) (codeOffset := 0x7406) (codeLen := 5) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x740b (by decide)))
  have g7 : AgreesExcept [.mem (stackPtr s6 + 8) 1, .rip] s6 s7 := by simpa [movM8Imm8Effect_components, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e7.agrees
  have f7 := f6.after_store pre ready7 g7 (by decide) (by
    intro slot hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> unfold OffsetsApart <;> decide +kernel)
  have scratch7 : memLoad s7.external (stackPtr s7 + 8) 8 = 1 := by
    have h : memLoad s7.external (stackPtr s6 + 8) 8 = 1 := e7.writes
    rwa [show stackPtr s6 = stackPtr s7 by rw [f6.rsp, f7.rsp]] at h
  have h7_rax : s7.regValue .rax = initial.regValue .rdi := (g7.read (n := 64) (r := 0) (by simp)).trans h6_rax
  have h7_r15 : s7.regValue .r15 = orderAddress := (g7.read (n := 64) (r := 15) (by simp)).trans h6_r15
  have h7_rcx : s7.regValue .rcx = 0xffffffff00000000 := (g7.read (n := 64) (r := 1) (by simp)).trans h6_rcx
  have h7_rdx : s7.regValue .rdx = 0 := (g7.read (n := 64) (r := 2) (by simp)).trans h6_rdx
  obtain ⟨s8, a8, ready8, e8⟩ :=
    (lea_r64_effect_step 0x10740b 0x4c (by simp [RexWPrefix]) 4 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl).advances
      (readyToStep f7.machine f7.bindingsSupported)
      (programText_slice (programLoaded_codeIn f7.loaded) 0x740b _
        (by decide +kernel) (by decide +kernel)) e7.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7410 (by decide)))
  have g8 : AgreesExcept [.reg 12, .rip] s7 s8 := e8.agrees
  have f8 := f7.after_registers ready8 g8 (by simp [Component.Covers]) (by simp)
  have h8_r12 : s8.regValue .r12 = frameBase initial + 8 := by
    have h : s8.regValue .r12 = stackPtr s7 + 8 := e8.writes
    rw [f7.rsp] at h
    exact h
  have h8_rax : s8.regValue .rax = initial.regValue .rdi := (g8.read (n := 64) (r := 0) (by simp)).trans h7_rax
  have h8_r15 : s8.regValue .r15 = orderAddress := (g8.read (n := 64) (r := 15) (by simp)).trans h7_r15
  have h8_rcx : s8.regValue .rcx = 0xffffffff00000000 := (g8.read (n := 64) (r := 1) (by simp)).trans h7_rcx
  have h8_rdx : s8.regValue .rdx = 0 := (g8.read (n := 64) (r := 2) (by simp)).trans h7_rdx
  have scratch8 : memLoad s8.external (stackPtr s8 + 8) 8 = 1 := by
    rw [show stackPtr s8 = stackPtr s7 by rw [f8.rsp, f7.rsp], g8.external (by simp [Component.Covers])]
    exact scratch7
  obtain ⟨s9, a9, ready9, e9⟩ :=
    (movzx_r32_m8_effect_step 0x107410 0 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl).advances
      (readyToStep f8.machine f8.bindingsSupported)
      (programText_slice (programLoaded_codeIn f8.loaded) 0x7410 _
        (by decide +kernel) (by decide +kernel)) ⟨e8.rip, by
        change MemReadable s8 (stackPtr s8 + 8) 1
        exact Fill.stack_readable pre f8.toFrame (offset := 8) (len := 1) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7415 (by decide)))
  have g9 : AgreesExcept [.reg 0, .rip] s8 s9 := e9.agrees
  have f9 := f8.after_registers ready9 g9 (by simp [Component.Covers]) (by simp)
  have h9_rax : s9.regValue .rax = 1 := by
    have h : s9.regValue .rax = (memLoad s8.external (stackPtr s8 + 8) 8).setWidth 64 := e9.writes
    rw [scratch8] at h
    exact h
  have h9_r15 : s9.regValue .r15 = orderAddress := (g9.read (n := 64) (r := 15) (by simp)).trans h8_r15
  have h9_rcx : s9.regValue .rcx = 0xffffffff00000000 := (g9.read (n := 64) (r := 1) (by simp)).trans h8_rcx
  have h9_rdx : s9.regValue .rdx = 0 := (g9.read (n := 64) (r := 2) (by simp)).trans h8_rdx
  have h9_r12 : s9.regValue .r12 = frameBase initial + 8 := (g9.read (n := 64) (r := 12) (by simp)).trans h8_r12
  have scratch9 : memLoad s9.external (stackPtr s9 + 8) 8 = 1 := by
    rw [show stackPtr s9 = stackPtr s8 by rw [f9.rsp, f8.rsp], g9.external (by simp [Component.Covers])]
    exact scratch8
  obtain ⟨s10, a10, ready10, e10⟩ :=
    (neg_r32_effect_step 0x107415 0xd8 rfl rfl).advances
      (readyToStep f9.machine f9.bindingsSupported)
      (programText_slice (programLoaded_codeIn f9.loaded) 0x7415 _
        (by decide +kernel) (by decide +kernel)) e9.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7417 (by decide)))
  have g10 : AgreesExcept [.reg 0, .flags, .rip] s9 s10 := e10.agrees
  have f10 := f9.after_registers ready10 g10 (by simp [Component.Covers]) (by simp)
  have h10_rax : s10.regValue .rax = 4294967295 := by
    have h : s10.regValue .rax = (-(s9.regValue .rax).setWidth 32).setWidth 64 := e10.writes
    rw [h9_rax] at h
    exact h
  have h10_r15 : s10.regValue .r15 = orderAddress := (g10.read (n := 64) (r := 15) (by simp)).trans h9_r15
  have h10_rcx : s10.regValue .rcx = 0xffffffff00000000 := (g10.read (n := 64) (r := 1) (by simp)).trans h9_rcx
  have h10_rdx : s10.regValue .rdx = 0 := (g10.read (n := 64) (r := 2) (by simp)).trans h9_rdx
  have h10_r12 : s10.regValue .r12 = frameBase initial + 8 := (g10.read (n := 64) (r := 12) (by simp)).trans h9_r12
  have scratch10 : memLoad s10.external (stackPtr s10 + 8) 8 = 1 := by
    rw [show stackPtr s10 = stackPtr s9 by rw [f10.rsp, f9.rsp], g10.external (by simp [Component.Covers])]
    exact scratch9
  obtain ⟨s11, a11, ready11, e11⟩ :=
    (and_r32_r32_effect_step 0x107417 0xd0 rfl).advances
      (readyToStep f10.machine f10.bindingsSupported)
      (programText_slice (programLoaded_codeIn f10.loaded) 0x7417 _
        (by decide +kernel) (by decide +kernel)) e10.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7419 (by decide)))
  have g11 : AgreesExcept [.reg 0, .flags, .rip] s10 s11 := e11.agrees
  have f11 := f10.after_registers ready11 g11 (by simp [Component.Covers]) (by simp)
  have h11_rax : s11.regValue .rax = 0 := by
    have h : s11.regValue .rax = ((s10.regValue .rax).setWidth 32 &&& (s10.regValue .rdx).setWidth 32).setWidth 64 := e11.writes
    rw [h10_rax, h10_rdx] at h
    exact h
  have h11_r15 : s11.regValue .r15 = orderAddress := (g11.read (n := 64) (r := 15) (by simp)).trans h10_r15
  have h11_rcx : s11.regValue .rcx = 0xffffffff00000000 := (g11.read (n := 64) (r := 1) (by simp)).trans h10_rcx
  have h11_rdx : s11.regValue .rdx = 0 := (g11.read (n := 64) (r := 2) (by simp)).trans h10_rdx
  have h11_r12 : s11.regValue .r12 = frameBase initial + 8 := (g11.read (n := 64) (r := 12) (by simp)).trans h10_r12
  have scratch11 : memLoad s11.external (stackPtr s11 + 8) 8 = 1 := by
    rw [show stackPtr s11 = stackPtr s10 by rw [f11.rsp, f10.rsp], g11.external (by simp [Component.Covers])]
    exact scratch10
  exact ⟨s11, ((((((((((a1.trans a2).trans a3).trans a4).trans a5).trans a6).trans a7).trans a8).trans a9).trans a10).trans a11), f11, e11.rip, h11_r15, h11_rcx, h11_rdx, h11_rax, h11_r12⟩

end P256.Proofs.Nonce.Fill.Tail.Decode.Scan
