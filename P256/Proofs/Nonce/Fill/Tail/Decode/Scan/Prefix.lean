import P256.Proofs.Common.Encoding.Parser.ByteStore
import P256.Proofs.Nonce.Fill.Tail.Decode.Scan.Head
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

import P256.Proofs.Common.Encoding.Serialize.Tail.ByteOps.Store
import X86Proofs.Instructions.Test.Generated.RR.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill.Tail.Decode.Scan

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Proofs.Common.Instructions P256.Proofs.Nonce.Initialize.Conversions.Bsr
open P256.Proofs.Nonce.Initialize.Conversions.XorImmediate P256.Proofs.Common.Instructions.Setb
open P256.Proofs.Nonce.Initialize.Conversions.Neg32

theorem scan_prefix [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} {original state : Nonce.State}
    (pre : Pre initial boundary orderAddress original)
    (input : Updated initial s orderAddress state) :
    ∃ t, Advances boundary 35 s t ∧ ScanState initial t orderAddress state ∧
      t.RIP = 0x107473 ∧
      t.regValue .r15 = orderAddress ∧
      t.regValue .rcx = 0 ∧
      t.regValue .rdx = 0 ∧
      t.regValue .rax = 0 ∧
      t.regValue .r12 = frameBase initial + 8 ∧
      t.regValue .r8 = 0 ∧
      t.regValue .r9 = 0 := by
  obtain ⟨s11, a0, f11, rip11, h11_r15, h11_rcx, h11_rdx, h11_rax, h11_r12⟩ := head pre input
  obtain ⟨s12, a12, ready12, e12⟩ :=
    (mov_r64_m64_effect_step 0x107419 0x49 (by simp [RexWPrefix]) 6 (.base 15 (.d8 16)) (by decide +kernel) rfl rfl).advances
      (readyToStep f11.machine f11.bindingsSupported)
      (programText_slice (programLoaded_codeIn f11.loaded) 0x7419 _
        (by decide +kernel) (by decide +kernel)) ⟨rip11, by
        change MemReadable s11 (s11.regValue .r15 + 16) 8
        exact by
          rw [h11_r15]
          exact f11.order_readable pre (offset := 16) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x741d (by decide)))
  have g12 : AgreesExcept [.reg 6, .rip] s11 s12 := e12.agrees
  have f12 := f11.after_registers ready12 g12 (by simp [Component.Covers]) (by simp)
  have h12_rsi : s12.regValue .rsi = 0xffffffffffffffff := by
    have h : s12.regValue .rsi = memLoad s11.external (s11.regValue .r15 + 16) 64 := e12.writes
    rw [h11_r15] at h
    exact h.trans ((f11.generator.2.1.memLoad_limb 2 (by decide)).trans (by decide +kernel))
  have h12_rax : s12.regValue .rax = 0 := (g12.read (n := 64) (r := 0) (by simp)).trans h11_rax
  have h12_r15 : s12.regValue .r15 = orderAddress := (g12.read (n := 64) (r := 15) (by simp)).trans h11_r15
  have h12_rcx : s12.regValue .rcx = 0xffffffff00000000 := (g12.read (n := 64) (r := 1) (by simp)).trans h11_rcx
  have h12_rdx : s12.regValue .rdx = 0 := (g12.read (n := 64) (r := 2) (by simp)).trans h11_rdx
  have h12_r12 : s12.regValue .r12 = frameBase initial + 8 := (g12.read (n := 64) (r := 12) (by simp)).trans h11_r12
  obtain ⟨s13, a13, ready13, e13⟩ :=
    (mov_r32_imm32_effect_step 0x10741d 0xbf (by decide) 127).advances
      (readyToStep f12.machine f12.bindingsSupported)
      (programText_slice (programLoaded_codeIn f12.loaded) 0x741d _
        (by decide +kernel) (by decide +kernel)) e12.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7422 (by decide)))
  have g13 : AgreesExcept [.reg 7, .rip] s12 s13 := e13.agrees
  have f13 := f12.after_registers ready13 g13 (by simp [Component.Covers]) (by simp)
  have h13_rdi : s13.regValue .rdi = 127 := by
    have h : s13.regValue .rdi = 127 := e13.writes
    try simp only [ite_self] at h
    exact h
  have h13_rax : s13.regValue .rax = 0 := (g13.read (n := 64) (r := 0) (by simp)).trans h12_rax
  have h13_r15 : s13.regValue .r15 = orderAddress := (g13.read (n := 64) (r := 15) (by simp)).trans h12_r15
  have h13_rcx : s13.regValue .rcx = 0xffffffff00000000 := (g13.read (n := 64) (r := 1) (by simp)).trans h12_rcx
  have h13_rdx : s13.regValue .rdx = 0 := (g13.read (n := 64) (r := 2) (by simp)).trans h12_rdx
  have h13_r12 : s13.regValue .r12 = frameBase initial + 8 := (g13.read (n := 64) (r := 12) (by simp)).trans h12_r12
  have h13_rsi : s13.regValue .rsi = 0xffffffffffffffff := (g13.read (n := 64) (r := 6) (by simp)).trans h12_rsi
  obtain ⟨s14, a14, ready14, e14⟩ :=
    (bsr_r64_r64_effect_step 0x107422 0x48 0xfe (by simp [RexWPrefix]) rfl).advances
      (readyToStep f13.machine f13.bindingsSupported)
      (programText_slice (programLoaded_codeIn f13.loaded) 0x7422 _
        (by decide +kernel) (by decide +kernel)) e13.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7426 (by decide)))
  have g14 : AgreesExcept [.reg 7, .flags, .rip] s13 s14 := e14.agrees
  have f14 := f13.after_registers ready14 g14 (by simp [Component.Covers]) (by simp)
  have h14_rdi : s14.regValue .rdi = 63 := by
    have h : s14.regValue .rdi = (bsrSpec64 (s13.regValue .rdi) (s13.regValue .rsi)).1 := e14.writes
    rw [h13_rsi, h13_rdi] at h
    exact h.trans (by decide +kernel)
  have h14_rax : s14.regValue .rax = 0 := (g14.read (n := 64) (r := 0) (by simp)).trans h13_rax
  have h14_r15 : s14.regValue .r15 = orderAddress := (g14.read (n := 64) (r := 15) (by simp)).trans h13_r15
  have h14_rcx : s14.regValue .rcx = 0xffffffff00000000 := (g14.read (n := 64) (r := 1) (by simp)).trans h13_rcx
  have h14_rdx : s14.regValue .rdx = 0 := (g14.read (n := 64) (r := 2) (by simp)).trans h13_rdx
  have h14_r12 : s14.regValue .r12 = frameBase initial + 8 := (g14.read (n := 64) (r := 12) (by simp)).trans h13_r12
  have h14_rsi : s14.regValue .rsi = 0xffffffffffffffff := (g14.read (n := 64) (r := 6) (by simp)).trans h13_rsi
  obtain ⟨s15, a15, ready15, e15⟩ :=
    (xor_r32_imm8_effect_step 0x107426 0xf7 63 rfl rfl).advances
      (readyToStep f14.machine f14.bindingsSupported)
      (programText_slice (programLoaded_codeIn f14.loaded) 0x7426 _
        (by decide +kernel) (by decide +kernel)) e14.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7429 (by decide)))
  have g15 : AgreesExcept [.reg 7, .flags, .rip] s14 s15 := e15.agrees
  have f15 := f14.after_registers ready15 g15 (by simp [Component.Covers]) (by simp)
  have h15_rdi : s15.regValue .rdi = 0 := by
    have h : s15.regValue .rdi = ((s14.regValue .rdi).setWidth 32 ^^^ 63).setWidth 64 := e15.writes
    rw [h14_rdi] at h
    try simp only [ite_self] at h
    exact h
  have h15_rax : s15.regValue .rax = 0 := (g15.read (n := 64) (r := 0) (by simp)).trans h14_rax
  have h15_r15 : s15.regValue .r15 = orderAddress := (g15.read (n := 64) (r := 15) (by simp)).trans h14_r15
  have h15_rcx : s15.regValue .rcx = 0xffffffff00000000 := (g15.read (n := 64) (r := 1) (by simp)).trans h14_rcx
  have h15_rdx : s15.regValue .rdx = 0 := (g15.read (n := 64) (r := 2) (by simp)).trans h14_rdx
  have h15_r12 : s15.regValue .r12 = frameBase initial + 8 := (g15.read (n := 64) (r := 12) (by simp)).trans h14_r12
  have h15_rsi : s15.regValue .rsi = 0xffffffffffffffff := (g15.read (n := 64) (r := 6) (by simp)).trans h14_rsi
  obtain ⟨s16, a16, ready16, e16⟩ :=
    (xor_r32_r32_effect_step 0x107429 0xd2 rfl).advances
      (readyToStep f15.machine f15.bindingsSupported)
      (programText_slice (programLoaded_codeIn f15.loaded) 0x7429 _
        (by decide +kernel) (by decide +kernel)) e15.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x742b (by decide)))
  have g16 : AgreesExcept [.reg 2, .flags, .rip] s15 s16 := e16.agrees
  have f16 := f15.after_registers ready16 g16 (by simp [Component.Covers]) (by simp)
  have h16_rdx : s16.regValue .rdx = 0 := by
    have h : s16.regValue .rdx = ((s15.regValue .rdx).setWidth 32 ^^^ (s15.regValue .rdx).setWidth 32).setWidth 64 := e16.writes
    rw [h15_rdx] at h
    try simp only [ite_self] at h
    exact h
  have h16_rax : s16.regValue .rax = 0 := (g16.read (n := 64) (r := 0) (by simp)).trans h15_rax
  have h16_r15 : s16.regValue .r15 = orderAddress := (g16.read (n := 64) (r := 15) (by simp)).trans h15_r15
  have h16_rcx : s16.regValue .rcx = 0xffffffff00000000 := (g16.read (n := 64) (r := 1) (by simp)).trans h15_rcx
  have h16_r12 : s16.regValue .r12 = frameBase initial + 8 := (g16.read (n := 64) (r := 12) (by simp)).trans h15_r12
  have h16_rsi : s16.regValue .rsi = 0xffffffffffffffff := (g16.read (n := 64) (r := 6) (by simp)).trans h15_rsi
  have h16_rdi : s16.regValue .rdi = 0 := (g16.read (n := 64) (r := 7) (by simp)).trans h15_rdi
  obtain ⟨s17, a17, ready17, e17⟩ :=
    (test_r64_r64_effect_step 0x10742b 0x48 0xc9 (by simp [RexWPrefix]) rfl).advances
      (readyToStep f16.machine f16.bindingsSupported)
      (programText_slice (programLoaded_codeIn f16.loaded) 0x742b _
        (by decide +kernel) (by decide +kernel)) e16.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x742e (by decide)))
  have g17 : AgreesExcept [.flags, .rip] s16 s17 := e17.agrees
  have f17 := f16.after_registers ready17 g17 (by simp [Component.Covers]) (by simp)
  have zf17 : (StatusFlags.ofRFLAGS s17.RFLAGS).ZF = false := by
    have h := e17.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS s17.RFLAGS).ZF = ((s16.regValue .rcx &&& s16.regValue .rcx) == 0) at h
    rw [h16_rcx] at h
    exact h
  have h17_rax : s17.regValue .rax = 0 := (g17.read (n := 64) (r := 0) (by simp)).trans h16_rax
  have h17_r15 : s17.regValue .r15 = orderAddress := (g17.read (n := 64) (r := 15) (by simp)).trans h16_r15
  have h17_rcx : s17.regValue .rcx = 0xffffffff00000000 := (g17.read (n := 64) (r := 1) (by simp)).trans h16_rcx
  have h17_rdx : s17.regValue .rdx = 0 := (g17.read (n := 64) (r := 2) (by simp)).trans h16_rdx
  have h17_r12 : s17.regValue .r12 = frameBase initial + 8 := (g17.read (n := 64) (r := 12) (by simp)).trans h16_r12
  have h17_rsi : s17.regValue .rsi = 0xffffffffffffffff := (g17.read (n := 64) (r := 6) (by simp)).trans h16_rsi
  have h17_rdi : s17.regValue .rdi = 0 := (g17.read (n := 64) (r := 7) (by simp)).trans h16_rdi
  obtain ⟨s18, a18, ready18, e18⟩ :=
    (setcc_m8_effect_step 0x10742e 0x94 (.inr rfl) 0 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl).advances
      (readyToStep f17.machine f17.bindingsSupported)
      (programText_slice (programLoaded_codeIn f17.loaded) 0x742e _
        (by decide +kernel) (by decide +kernel)) ⟨e17.rip, by
        change MemWritable s17 (stackPtr s17 + 8) 1
        exact f17.stack_writable1 pre, by
        exact Fill.stack_code pre f17.toFrame (offset := 8) (len := 1) (codeOffset := 0x742e) (codeLen := 5) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7433 (by decide)))
  have g18 : AgreesExcept [.mem (stackPtr s17 + 8) 1, .rip] s17 s18 := by simpa [movM8Imm8Effect_components, setccM8Effect_components, storeEffect_components, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e18.agrees
  have f18 := f17.after_store pre ready18 g18 (by decide) (by
    intro slot hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> unfold OffsetsApart <;> decide +kernel)
  have scratch18 : memLoad s18.external (stackPtr s18 + 8) 8 = 0 := by
    have h : memLoad s18.external (stackPtr s17 + 8) 8 = (if (StatusFlags.ofRFLAGS s17.RFLAGS).ZF then 1 else 0) := e18.writes
    rw [zf17] at h
    rwa [show stackPtr s17 = stackPtr s18 by rw [f17.rsp, f18.rsp]] at h
  have h18_rax : s18.regValue .rax = 0 := (g18.read (n := 64) (r := 0) (by simp)).trans h17_rax
  have h18_r15 : s18.regValue .r15 = orderAddress := (g18.read (n := 64) (r := 15) (by simp)).trans h17_r15
  have h18_rcx : s18.regValue .rcx = 0xffffffff00000000 := (g18.read (n := 64) (r := 1) (by simp)).trans h17_rcx
  have h18_rdx : s18.regValue .rdx = 0 := (g18.read (n := 64) (r := 2) (by simp)).trans h17_rdx
  have h18_r12 : s18.regValue .r12 = frameBase initial + 8 := (g18.read (n := 64) (r := 12) (by simp)).trans h17_r12
  have h18_rsi : s18.regValue .rsi = 0xffffffffffffffff := (g18.read (n := 64) (r := 6) (by simp)).trans h17_rsi
  have h18_rdi : s18.regValue .rdi = 0 := (g18.read (n := 64) (r := 7) (by simp)).trans h17_rdi
  have zf18 : (StatusFlags.ofRFLAGS s18.RFLAGS).ZF = false := by
    rw [g18.rflags (by simp) (by simp)]
    exact zf17
  obtain ⟨s19, a19, ready19, e19⟩ :=
    (setcc_r8_effect_step 0x107433 0x94 0xc2 (.inr rfl) rfl (by decide)).advances
      (readyToStep f18.machine f18.bindingsSupported)
      (programText_slice (programLoaded_codeIn f18.loaded) 0x7433 _
        (by decide +kernel) (by decide +kernel)) e18.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7436 (by decide)))
  have g19 : AgreesExcept [.reg 2, .rip] s18 s19 := e19.agrees
  have f19 := f18.after_registers ready19 g19 (by simp [Component.Covers]) (by simp)
  have h19_rdx : s19.regValue .rdx = 0 := by
    have h : s19.regValue .rdx = mergeGPR 8 (if (StatusFlags.ofRFLAGS s18.RFLAGS).ZF then 1 else 0) (s18.regValue .rdx) := e19.writes
    rw [h18_rdx, zf18] at h
    try simp only [ite_self] at h
    exact h
  have h19_rax : s19.regValue .rax = 0 := (g19.read (n := 64) (r := 0) (by simp)).trans h18_rax
  have h19_r15 : s19.regValue .r15 = orderAddress := (g19.read (n := 64) (r := 15) (by simp)).trans h18_r15
  have h19_rcx : s19.regValue .rcx = 0xffffffff00000000 := (g19.read (n := 64) (r := 1) (by simp)).trans h18_rcx
  have h19_r12 : s19.regValue .r12 = frameBase initial + 8 := (g19.read (n := 64) (r := 12) (by simp)).trans h18_r12
  have h19_rsi : s19.regValue .rsi = 0xffffffffffffffff := (g19.read (n := 64) (r := 6) (by simp)).trans h18_rsi
  have h19_rdi : s19.regValue .rdi = 0 := (g19.read (n := 64) (r := 7) (by simp)).trans h18_rdi
  have scratch19 : memLoad s19.external (stackPtr s19 + 8) 8 = 0 := by
    rw [show stackPtr s19 = stackPtr s18 by rw [f19.rsp, f18.rsp], g19.external (by simp [Component.Covers])]
    exact scratch18
  have zf19 : (StatusFlags.ofRFLAGS s19.RFLAGS).ZF = false := by
    rw [g19.rflags (by simp) (by simp)]
    exact zf18
  obtain ⟨s20, a20, ready20, e20⟩ :=
    (movzx_r32_m8_effect_step 0x107436 1 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl).advances
      (readyToStep f19.machine f19.bindingsSupported)
      (programText_slice (programLoaded_codeIn f19.loaded) 0x7436 _
        (by decide +kernel) (by decide +kernel)) ⟨e19.rip, by
        change MemReadable s19 (stackPtr s19 + 8) 1
        exact Fill.stack_readable pre f19.toFrame (offset := 8) (len := 1) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x743b (by decide)))
  have g20 : AgreesExcept [.reg 1, .rip] s19 s20 := e20.agrees
  have f20 := f19.after_registers ready20 g20 (by simp [Component.Covers]) (by simp)
  have h20_rcx : s20.regValue .rcx = 0 := by
    have h : s20.regValue .rcx = (memLoad s19.external (stackPtr s19 + 8) 8).setWidth 64 := e20.writes
    rw [scratch19] at h
    try simp only [ite_self] at h
    exact h
  have h20_rax : s20.regValue .rax = 0 := (g20.read (n := 64) (r := 0) (by simp)).trans h19_rax
  have h20_r15 : s20.regValue .r15 = orderAddress := (g20.read (n := 64) (r := 15) (by simp)).trans h19_r15
  have h20_rdx : s20.regValue .rdx = 0 := (g20.read (n := 64) (r := 2) (by simp)).trans h19_rdx
  have h20_r12 : s20.regValue .r12 = frameBase initial + 8 := (g20.read (n := 64) (r := 12) (by simp)).trans h19_r12
  have h20_rsi : s20.regValue .rsi = 0xffffffffffffffff := (g20.read (n := 64) (r := 6) (by simp)).trans h19_rsi
  have h20_rdi : s20.regValue .rdi = 0 := (g20.read (n := 64) (r := 7) (by simp)).trans h19_rdi
  have scratch20 : memLoad s20.external (stackPtr s20 + 8) 8 = 0 := by
    rw [show stackPtr s20 = stackPtr s19 by rw [f20.rsp, f19.rsp], g20.external (by simp [Component.Covers])]
    exact scratch19
  have zf20 : (StatusFlags.ofRFLAGS s20.RFLAGS).ZF = false := by
    rw [g20.rflags (by simp) (by simp)]
    exact zf19
  obtain ⟨s21, a21, ready21, e21⟩ :=
    (neg_r32_effect_step 0x10743b 0xd9 rfl rfl).advances
      (readyToStep f20.machine f20.bindingsSupported)
      (programText_slice (programLoaded_codeIn f20.loaded) 0x743b _
        (by decide +kernel) (by decide +kernel)) e20.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x743d (by decide)))
  have g21 : AgreesExcept [.reg 1, .flags, .rip] s20 s21 := e21.agrees
  have f21 := f20.after_registers ready21 g21 (by simp [Component.Covers]) (by simp)
  have h21_rcx : s21.regValue .rcx = 0 := by
    have h : s21.regValue .rcx = (-(s20.regValue .rcx).setWidth 32).setWidth 64 := e21.writes
    rw [h20_rcx] at h
    try simp only [ite_self] at h
    exact h
  have h21_rax : s21.regValue .rax = 0 := (g21.read (n := 64) (r := 0) (by simp)).trans h20_rax
  have h21_r15 : s21.regValue .r15 = orderAddress := (g21.read (n := 64) (r := 15) (by simp)).trans h20_r15
  have h21_rdx : s21.regValue .rdx = 0 := (g21.read (n := 64) (r := 2) (by simp)).trans h20_rdx
  have h21_r12 : s21.regValue .r12 = frameBase initial + 8 := (g21.read (n := 64) (r := 12) (by simp)).trans h20_r12
  have h21_rsi : s21.regValue .rsi = 0xffffffffffffffff := (g21.read (n := 64) (r := 6) (by simp)).trans h20_rsi
  have h21_rdi : s21.regValue .rdi = 0 := (g21.read (n := 64) (r := 7) (by simp)).trans h20_rdi
  have scratch21 : memLoad s21.external (stackPtr s21 + 8) 8 = 0 := by
    rw [show stackPtr s21 = stackPtr s20 by rw [f21.rsp, f20.rsp], g21.external (by simp [Component.Covers])]
    exact scratch20
  obtain ⟨s22, a22, ready22, e22⟩ :=
    (and_r32_r32_effect_step 0x10743d 0xf9 rfl).advances
      (readyToStep f21.machine f21.bindingsSupported)
      (programText_slice (programLoaded_codeIn f21.loaded) 0x743d _
        (by decide +kernel) (by decide +kernel)) e21.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x743f (by decide)))
  have g22 : AgreesExcept [.reg 1, .flags, .rip] s21 s22 := e22.agrees
  have f22 := f21.after_registers ready22 g22 (by simp [Component.Covers]) (by simp)
  have h22_rcx : s22.regValue .rcx = 0 := by
    have h : s22.regValue .rcx = ((s21.regValue .rcx).setWidth 32 &&& (s21.regValue .rdi).setWidth 32).setWidth 64 := e22.writes
    rw [h21_rcx, h21_rdi] at h
    try simp only [ite_self] at h
    exact h
  have h22_rax : s22.regValue .rax = 0 := (g22.read (n := 64) (r := 0) (by simp)).trans h21_rax
  have h22_r15 : s22.regValue .r15 = orderAddress := (g22.read (n := 64) (r := 15) (by simp)).trans h21_r15
  have h22_rdx : s22.regValue .rdx = 0 := (g22.read (n := 64) (r := 2) (by simp)).trans h21_rdx
  have h22_r12 : s22.regValue .r12 = frameBase initial + 8 := (g22.read (n := 64) (r := 12) (by simp)).trans h21_r12
  have h22_rsi : s22.regValue .rsi = 0xffffffffffffffff := (g22.read (n := 64) (r := 6) (by simp)).trans h21_rsi
  have h22_rdi : s22.regValue .rdi = 0 := (g22.read (n := 64) (r := 7) (by simp)).trans h21_rdi
  have scratch22 : memLoad s22.external (stackPtr s22 + 8) 8 = 0 := by
    rw [show stackPtr s22 = stackPtr s21 by rw [f22.rsp, f21.rsp], g22.external (by simp [Component.Covers])]
    exact scratch21
  obtain ⟨s23, a23, ready23, e23⟩ :=
    (test_r64_r64_effect_step 0x10743f 0x48 0xf6 (by simp [RexWPrefix]) rfl).advances
      (readyToStep f22.machine f22.bindingsSupported)
      (programText_slice (programLoaded_codeIn f22.loaded) 0x743f _
        (by decide +kernel) (by decide +kernel)) e22.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7442 (by decide)))
  have g23 : AgreesExcept [.flags, .rip] s22 s23 := e23.agrees
  have f23 := f22.after_registers ready23 g23 (by simp [Component.Covers]) (by simp)
  have zf23 : (StatusFlags.ofRFLAGS s23.RFLAGS).ZF = false := by
    have h := e23.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS s23.RFLAGS).ZF = ((s22.regValue .rsi &&& s22.regValue .rsi) == 0) at h
    rw [h22_rsi] at h
    exact h
  have h23_rax : s23.regValue .rax = 0 := (g23.read (n := 64) (r := 0) (by simp)).trans h22_rax
  have h23_r15 : s23.regValue .r15 = orderAddress := (g23.read (n := 64) (r := 15) (by simp)).trans h22_r15
  have h23_rcx : s23.regValue .rcx = 0 := (g23.read (n := 64) (r := 1) (by simp)).trans h22_rcx
  have h23_rdx : s23.regValue .rdx = 0 := (g23.read (n := 64) (r := 2) (by simp)).trans h22_rdx
  have h23_r12 : s23.regValue .r12 = frameBase initial + 8 := (g23.read (n := 64) (r := 12) (by simp)).trans h22_r12
  have h23_rsi : s23.regValue .rsi = 0xffffffffffffffff := (g23.read (n := 64) (r := 6) (by simp)).trans h22_rsi
  have h23_rdi : s23.regValue .rdi = 0 := (g23.read (n := 64) (r := 7) (by simp)).trans h22_rdi
  have scratch23 : memLoad s23.external (stackPtr s23 + 8) 8 = 0 := by
    rw [show stackPtr s23 = stackPtr s22 by rw [f23.rsp, f22.rsp], g23.external (by simp [Component.Covers])]
    exact scratch22
  obtain ⟨s24, a24, ready24, e24⟩ :=
    (mov_r32_imm32_rex_effect_step 0x107442 0x41 0xb9 (by simp [RexNoWPrefix]) (by decide) 0).advances
      (readyToStep f23.machine f23.bindingsSupported)
      (programText_slice (programLoaded_codeIn f23.loaded) 0x7442 _
        (by decide +kernel) (by decide +kernel)) e23.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7448 (by decide)))
  have g24 : AgreesExcept [.reg 9, .rip] s23 s24 := e24.agrees
  have f24 := f23.after_registers ready24 g24 (by simp [Component.Covers]) (by simp)
  have h24_r9 : s24.regValue .r9 = 0 := by
    have h : s24.regValue .r9 = 0 := e24.writes
    try simp only [ite_self] at h
    exact h
  have h24_rax : s24.regValue .rax = 0 := (g24.read (n := 64) (r := 0) (by simp)).trans h23_rax
  have h24_r15 : s24.regValue .r15 = orderAddress := (g24.read (n := 64) (r := 15) (by simp)).trans h23_r15
  have h24_rcx : s24.regValue .rcx = 0 := (g24.read (n := 64) (r := 1) (by simp)).trans h23_rcx
  have h24_rdx : s24.regValue .rdx = 0 := (g24.read (n := 64) (r := 2) (by simp)).trans h23_rdx
  have h24_r12 : s24.regValue .r12 = frameBase initial + 8 := (g24.read (n := 64) (r := 12) (by simp)).trans h23_r12
  have h24_rsi : s24.regValue .rsi = 0xffffffffffffffff := (g24.read (n := 64) (r := 6) (by simp)).trans h23_rsi
  have h24_rdi : s24.regValue .rdi = 0 := (g24.read (n := 64) (r := 7) (by simp)).trans h23_rdi
  have scratch24 : memLoad s24.external (stackPtr s24 + 8) 8 = 0 := by
    rw [show stackPtr s24 = stackPtr s23 by rw [f24.rsp, f23.rsp], g24.external (by simp [Component.Covers])]
    exact scratch23
  have zf24 : (StatusFlags.ofRFLAGS s24.RFLAGS).ZF = false := by
    rw [g24.rflags (by simp) (by simp)]
    exact zf23
  obtain ⟨s25, a25, ready25, e25⟩ :=
    (cmovne_r32_r32_rex_effect_step 0x107448 0x41 0xd1 (by simp [RexNoWPrefix]) rfl).advances
      (readyToStep f24.machine f24.bindingsSupported)
      (programText_slice (programLoaded_codeIn f24.loaded) 0x7448 _
        (by decide +kernel) (by decide +kernel)) e24.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x744c (by decide)))
  have g25 : AgreesExcept [.reg 2, .rip] s24 s25 := e25.agrees
  have f25 := f24.after_registers ready25 g25 (by simp [Component.Covers]) (by simp)
  have h25_rdx : s25.regValue .rdx = 0 := by
    have h : s25.regValue .rdx = ((if condHolds 5 (StatusFlags.ofRFLAGS s24.RFLAGS) then (s24.regValue .r9).setWidth 32 else (s24.regValue .rdx).setWidth 32).setWidth 64) := e25.writes
    rw [h24_rdx, h24_r9] at h
    try simp only [ite_self] at h
    exact h
  have h25_rax : s25.regValue .rax = 0 := (g25.read (n := 64) (r := 0) (by simp)).trans h24_rax
  have h25_r15 : s25.regValue .r15 = orderAddress := (g25.read (n := 64) (r := 15) (by simp)).trans h24_r15
  have h25_rcx : s25.regValue .rcx = 0 := (g25.read (n := 64) (r := 1) (by simp)).trans h24_rcx
  have h25_r12 : s25.regValue .r12 = frameBase initial + 8 := (g25.read (n := 64) (r := 12) (by simp)).trans h24_r12
  have h25_rsi : s25.regValue .rsi = 0xffffffffffffffff := (g25.read (n := 64) (r := 6) (by simp)).trans h24_rsi
  have h25_rdi : s25.regValue .rdi = 0 := (g25.read (n := 64) (r := 7) (by simp)).trans h24_rdi
  have h25_r9 : s25.regValue .r9 = 0 := (g25.read (n := 64) (r := 9) (by simp)).trans h24_r9
  have scratch25 : memLoad s25.external (stackPtr s25 + 8) 8 = 0 := by
    rw [show stackPtr s25 = stackPtr s24 by rw [f25.rsp, f24.rsp], g25.external (by simp [Component.Covers])]
    exact scratch24
  have zf25 : (StatusFlags.ofRFLAGS s25.RFLAGS).ZF = false := by
    rw [g25.rflags (by simp) (by simp)]
    exact zf24
  obtain ⟨s26, a26, ready26, e26⟩ :=
    (mov_r64_m64_effect_step 0x10744c 0x49 (by simp [RexWPrefix]) 6 (.base 15 (.d8 8)) (by decide +kernel) rfl rfl).advances
      (readyToStep f25.machine f25.bindingsSupported)
      (programText_slice (programLoaded_codeIn f25.loaded) 0x744c _
        (by decide +kernel) (by decide +kernel)) ⟨e25.rip, by
        change MemReadable s25 (s25.regValue .r15 + 8) 8
        exact by
          rw [h25_r15]
          exact f25.order_readable pre (offset := 8) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7450 (by decide)))
  have g26 : AgreesExcept [.reg 6, .rip] s25 s26 := e26.agrees
  have f26 := f25.after_registers ready26 g26 (by simp [Component.Covers]) (by simp)
  have h26_rsi : s26.regValue .rsi = 0xbce6faada7179e84 := by
    have h : s26.regValue .rsi = memLoad s25.external (s25.regValue .r15 + 8) 64 := e26.writes
    rw [h25_r15] at h
    exact h.trans ((f25.generator.2.1.memLoad_limb 1 (by decide)).trans (by decide +kernel))
  have h26_rax : s26.regValue .rax = 0 := (g26.read (n := 64) (r := 0) (by simp)).trans h25_rax
  have h26_r15 : s26.regValue .r15 = orderAddress := (g26.read (n := 64) (r := 15) (by simp)).trans h25_r15
  have h26_rcx : s26.regValue .rcx = 0 := (g26.read (n := 64) (r := 1) (by simp)).trans h25_rcx
  have h26_rdx : s26.regValue .rdx = 0 := (g26.read (n := 64) (r := 2) (by simp)).trans h25_rdx
  have h26_r12 : s26.regValue .r12 = frameBase initial + 8 := (g26.read (n := 64) (r := 12) (by simp)).trans h25_r12
  have h26_rdi : s26.regValue .rdi = 0 := (g26.read (n := 64) (r := 7) (by simp)).trans h25_rdi
  have h26_r9 : s26.regValue .r9 = 0 := (g26.read (n := 64) (r := 9) (by simp)).trans h25_r9
  have scratch26 : memLoad s26.external (stackPtr s26 + 8) 8 = 0 := by
    rw [show stackPtr s26 = stackPtr s25 by rw [f26.rsp, f25.rsp], g26.external (by simp [Component.Covers])]
    exact scratch25
  have zf26 : (StatusFlags.ofRFLAGS s26.RFLAGS).ZF = false := by
    rw [g26.rflags (by simp) (by simp)]
    exact zf25
  obtain ⟨s27, a27, ready27, e27⟩ :=
    (mov_r32_imm32_effect_step 0x107450 0xbf (by decide) 127).advances
      (readyToStep f26.machine f26.bindingsSupported)
      (programText_slice (programLoaded_codeIn f26.loaded) 0x7450 _
        (by decide +kernel) (by decide +kernel)) e26.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7455 (by decide)))
  have g27 : AgreesExcept [.reg 7, .rip] s26 s27 := e27.agrees
  have f27 := f26.after_registers ready27 g27 (by simp [Component.Covers]) (by simp)
  have h27_rdi : s27.regValue .rdi = 127 := by
    have h : s27.regValue .rdi = 127 := e27.writes
    try simp only [ite_self] at h
    exact h
  have h27_rax : s27.regValue .rax = 0 := (g27.read (n := 64) (r := 0) (by simp)).trans h26_rax
  have h27_r15 : s27.regValue .r15 = orderAddress := (g27.read (n := 64) (r := 15) (by simp)).trans h26_r15
  have h27_rcx : s27.regValue .rcx = 0 := (g27.read (n := 64) (r := 1) (by simp)).trans h26_rcx
  have h27_rdx : s27.regValue .rdx = 0 := (g27.read (n := 64) (r := 2) (by simp)).trans h26_rdx
  have h27_r12 : s27.regValue .r12 = frameBase initial + 8 := (g27.read (n := 64) (r := 12) (by simp)).trans h26_r12
  have h27_rsi : s27.regValue .rsi = 0xbce6faada7179e84 := (g27.read (n := 64) (r := 6) (by simp)).trans h26_rsi
  have h27_r9 : s27.regValue .r9 = 0 := (g27.read (n := 64) (r := 9) (by simp)).trans h26_r9
  have scratch27 : memLoad s27.external (stackPtr s27 + 8) 8 = 0 := by
    rw [show stackPtr s27 = stackPtr s26 by rw [f27.rsp, f26.rsp], g27.external (by simp [Component.Covers])]
    exact scratch26
  have zf27 : (StatusFlags.ofRFLAGS s27.RFLAGS).ZF = false := by
    rw [g27.rflags (by simp) (by simp)]
    exact zf26
  obtain ⟨s28, a28, ready28, e28⟩ :=
    (bsr_r64_r64_effect_step 0x107455 0x48 0xfe (by simp [RexWPrefix]) rfl).advances
      (readyToStep f27.machine f27.bindingsSupported)
      (programText_slice (programLoaded_codeIn f27.loaded) 0x7455 _
        (by decide +kernel) (by decide +kernel)) e27.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7459 (by decide)))
  have g28 : AgreesExcept [.reg 7, .flags, .rip] s27 s28 := e28.agrees
  have f28 := f27.after_registers ready28 g28 (by simp [Component.Covers]) (by simp)
  have h28_rdi : s28.regValue .rdi = 63 := by
    have h : s28.regValue .rdi = (bsrSpec64 (s27.regValue .rdi) (s27.regValue .rsi)).1 := e28.writes
    rw [h27_rsi, h27_rdi] at h
    exact h.trans (by decide +kernel)
  have h28_rax : s28.regValue .rax = 0 := (g28.read (n := 64) (r := 0) (by simp)).trans h27_rax
  have h28_r15 : s28.regValue .r15 = orderAddress := (g28.read (n := 64) (r := 15) (by simp)).trans h27_r15
  have h28_rcx : s28.regValue .rcx = 0 := (g28.read (n := 64) (r := 1) (by simp)).trans h27_rcx
  have h28_rdx : s28.regValue .rdx = 0 := (g28.read (n := 64) (r := 2) (by simp)).trans h27_rdx
  have h28_r12 : s28.regValue .r12 = frameBase initial + 8 := (g28.read (n := 64) (r := 12) (by simp)).trans h27_r12
  have h28_rsi : s28.regValue .rsi = 0xbce6faada7179e84 := (g28.read (n := 64) (r := 6) (by simp)).trans h27_rsi
  have h28_r9 : s28.regValue .r9 = 0 := (g28.read (n := 64) (r := 9) (by simp)).trans h27_r9
  have scratch28 : memLoad s28.external (stackPtr s28 + 8) 8 = 0 := by
    rw [show stackPtr s28 = stackPtr s27 by rw [f28.rsp, f27.rsp], g28.external (by simp [Component.Covers])]
    exact scratch27
  obtain ⟨s29, a29, ready29, e29⟩ :=
    (xor_r32_imm8_effect_step 0x107459 0xf7 63 rfl rfl).advances
      (readyToStep f28.machine f28.bindingsSupported)
      (programText_slice (programLoaded_codeIn f28.loaded) 0x7459 _
        (by decide +kernel) (by decide +kernel)) e28.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x745c (by decide)))
  have g29 : AgreesExcept [.reg 7, .flags, .rip] s28 s29 := e29.agrees
  have f29 := f28.after_registers ready29 g29 (by simp [Component.Covers]) (by simp)
  have h29_rdi : s29.regValue .rdi = 0 := by
    have h : s29.regValue .rdi = ((s28.regValue .rdi).setWidth 32 ^^^ 63).setWidth 64 := e29.writes
    rw [h28_rdi] at h
    try simp only [ite_self] at h
    exact h
  have h29_rax : s29.regValue .rax = 0 := (g29.read (n := 64) (r := 0) (by simp)).trans h28_rax
  have h29_r15 : s29.regValue .r15 = orderAddress := (g29.read (n := 64) (r := 15) (by simp)).trans h28_r15
  have h29_rcx : s29.regValue .rcx = 0 := (g29.read (n := 64) (r := 1) (by simp)).trans h28_rcx
  have h29_rdx : s29.regValue .rdx = 0 := (g29.read (n := 64) (r := 2) (by simp)).trans h28_rdx
  have h29_r12 : s29.regValue .r12 = frameBase initial + 8 := (g29.read (n := 64) (r := 12) (by simp)).trans h28_r12
  have h29_rsi : s29.regValue .rsi = 0xbce6faada7179e84 := (g29.read (n := 64) (r := 6) (by simp)).trans h28_rsi
  have h29_r9 : s29.regValue .r9 = 0 := (g29.read (n := 64) (r := 9) (by simp)).trans h28_r9
  have scratch29 : memLoad s29.external (stackPtr s29 + 8) 8 = 0 := by
    rw [show stackPtr s29 = stackPtr s28 by rw [f29.rsp, f28.rsp], g29.external (by simp [Component.Covers])]
    exact scratch28
  obtain ⟨s30, a30, ready30, e30⟩ :=
    (mov_m8_r8_legacy_effect_step 0x10745c 2 (by decide) (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl).advances
      (readyToStep f29.machine f29.bindingsSupported)
      (programText_slice (programLoaded_codeIn f29.loaded) 0x745c _
        (by decide +kernel) (by decide +kernel)) ⟨e29.rip, by
        change MemWritable s29 (stackPtr s29 + 8) 1
        exact f29.stack_writable1 pre, by
        exact Fill.stack_code pre f29.toFrame (offset := 8) (len := 1) (codeOffset := 0x745c) (codeLen := 4) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7460 (by decide)))
  have g30 : AgreesExcept [.mem (stackPtr s29 + 8) 1, .rip] s29 s30 := by simpa [movM8Imm8Effect_components, setccM8Effect_components, storeEffect_components, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e30.agrees
  have f30 := f29.after_store pre ready30 g30 (by decide) (by
    intro slot hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> unfold OffsetsApart <;> decide +kernel)
  have scratch30 : memLoad s30.external (stackPtr s30 + 8) 8 = 0 := by
    have h : memLoad s30.external (stackPtr s29 + 8) 8 = (s29.regValue .rdx).setWidth 8 := e30.writes
    rw [h29_rdx] at h
    rwa [show stackPtr s29 = stackPtr s30 by rw [f29.rsp, f30.rsp]] at h
  have h30_rax : s30.regValue .rax = 0 := (g30.read (n := 64) (r := 0) (by simp)).trans h29_rax
  have h30_r15 : s30.regValue .r15 = orderAddress := (g30.read (n := 64) (r := 15) (by simp)).trans h29_r15
  have h30_rcx : s30.regValue .rcx = 0 := (g30.read (n := 64) (r := 1) (by simp)).trans h29_rcx
  have h30_rdx : s30.regValue .rdx = 0 := (g30.read (n := 64) (r := 2) (by simp)).trans h29_rdx
  have h30_r12 : s30.regValue .r12 = frameBase initial + 8 := (g30.read (n := 64) (r := 12) (by simp)).trans h29_r12
  have h30_rsi : s30.regValue .rsi = 0xbce6faada7179e84 := (g30.read (n := 64) (r := 6) (by simp)).trans h29_rsi
  have h30_rdi : s30.regValue .rdi = 0 := (g30.read (n := 64) (r := 7) (by simp)).trans h29_rdi
  have h30_r9 : s30.regValue .r9 = 0 := (g30.read (n := 64) (r := 9) (by simp)).trans h29_r9
  obtain ⟨s31, a31, ready31, e31⟩ :=
    (movzx_r_m8_rex_effect_step 0x107460 0x44 (by simp [RexPrefix]) 32 (by simp) (by intro seg; rfl) 0 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl).advances
      (readyToStep f30.machine f30.bindingsSupported)
      (programText_slice (programLoaded_codeIn f30.loaded) 0x7460 _
        (by decide +kernel) (by decide +kernel)) ⟨e30.rip, by
        change MemReadable s30 (stackPtr s30 + 8) 1
        exact Fill.stack_readable pre f30.toFrame (offset := 8) (len := 1) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7466 (by decide)))
  have g31 : AgreesExcept [.reg 8, .rip] s30 s31 := e31.agrees
  have f31 := f30.after_registers ready31 g31 (by simp [Component.Covers]) (by simp)
  have h31_r8 : s31.regValue .r8 = 0 := by
    have h : s31.regValue .r8 = (memLoad s30.external (stackPtr s30 + 8) 8).setWidth 64 := e31.writes
    rw [scratch30] at h
    try simp only [ite_self] at h
    exact h
  have h31_rax : s31.regValue .rax = 0 := (g31.read (n := 64) (r := 0) (by simp)).trans h30_rax
  have h31_r15 : s31.regValue .r15 = orderAddress := (g31.read (n := 64) (r := 15) (by simp)).trans h30_r15
  have h31_rcx : s31.regValue .rcx = 0 := (g31.read (n := 64) (r := 1) (by simp)).trans h30_rcx
  have h31_rdx : s31.regValue .rdx = 0 := (g31.read (n := 64) (r := 2) (by simp)).trans h30_rdx
  have h31_r12 : s31.regValue .r12 = frameBase initial + 8 := (g31.read (n := 64) (r := 12) (by simp)).trans h30_r12
  have h31_rsi : s31.regValue .rsi = 0xbce6faada7179e84 := (g31.read (n := 64) (r := 6) (by simp)).trans h30_rsi
  have h31_rdi : s31.regValue .rdi = 0 := (g31.read (n := 64) (r := 7) (by simp)).trans h30_rdi
  have h31_r9 : s31.regValue .r9 = 0 := (g31.read (n := 64) (r := 9) (by simp)).trans h30_r9
  have scratch31 : memLoad s31.external (stackPtr s31 + 8) 8 = 0 := by
    rw [show stackPtr s31 = stackPtr s30 by rw [f31.rsp, f30.rsp], g31.external (by simp [Component.Covers])]
    exact scratch30
  obtain ⟨s32, a32, ready32, e32⟩ :=
    (neg_r32_rex_effect_step 0x107466 0x41 0xd8 (by simp [RexNoWPrefix]) rfl rfl).advances
      (readyToStep f31.machine f31.bindingsSupported)
      (programText_slice (programLoaded_codeIn f31.loaded) 0x7466 _
        (by decide +kernel) (by decide +kernel)) e31.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7469 (by decide)))
  have g32 : AgreesExcept [.reg 8, .flags, .rip] s31 s32 := e32.agrees
  have f32 := f31.after_registers ready32 g32 (by simp [Component.Covers]) (by simp)
  have h32_r8 : s32.regValue .r8 = 0 := by
    have h : s32.regValue .r8 = (-(s31.regValue .r8).setWidth 32).setWidth 64 := e32.writes
    rw [h31_r8] at h
    try simp only [ite_self] at h
    exact h
  have h32_rax : s32.regValue .rax = 0 := (g32.read (n := 64) (r := 0) (by simp)).trans h31_rax
  have h32_r15 : s32.regValue .r15 = orderAddress := (g32.read (n := 64) (r := 15) (by simp)).trans h31_r15
  have h32_rcx : s32.regValue .rcx = 0 := (g32.read (n := 64) (r := 1) (by simp)).trans h31_rcx
  have h32_rdx : s32.regValue .rdx = 0 := (g32.read (n := 64) (r := 2) (by simp)).trans h31_rdx
  have h32_r12 : s32.regValue .r12 = frameBase initial + 8 := (g32.read (n := 64) (r := 12) (by simp)).trans h31_r12
  have h32_rsi : s32.regValue .rsi = 0xbce6faada7179e84 := (g32.read (n := 64) (r := 6) (by simp)).trans h31_rsi
  have h32_rdi : s32.regValue .rdi = 0 := (g32.read (n := 64) (r := 7) (by simp)).trans h31_rdi
  have h32_r9 : s32.regValue .r9 = 0 := (g32.read (n := 64) (r := 9) (by simp)).trans h31_r9
  have scratch32 : memLoad s32.external (stackPtr s32 + 8) 8 = 0 := by
    rw [show stackPtr s32 = stackPtr s31 by rw [f32.rsp, f31.rsp], g32.external (by simp [Component.Covers])]
    exact scratch31
  obtain ⟨s33, a33, ready33, e33⟩ :=
    (and_r32_r32_rex_effect_step 0x107469 0x41 0xf8 (by simp [RexNoWPrefix]) rfl).advances
      (readyToStep f32.machine f32.bindingsSupported)
      (programText_slice (programLoaded_codeIn f32.loaded) 0x7469 _
        (by decide +kernel) (by decide +kernel)) e32.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x746c (by decide)))
  have g33 : AgreesExcept [.reg 8, .flags, .rip] s32 s33 := e33.agrees
  have f33 := f32.after_registers ready33 g33 (by simp [Component.Covers]) (by simp)
  have h33_r8 : s33.regValue .r8 = 0 := by
    have h : s33.regValue .r8 = ((s32.regValue .r8).setWidth 32 &&& (s32.regValue .rdi).setWidth 32).setWidth 64 := e33.writes
    rw [h32_rdi, h32_r8] at h
    try simp only [ite_self] at h
    exact h
  have h33_rax : s33.regValue .rax = 0 := (g33.read (n := 64) (r := 0) (by simp)).trans h32_rax
  have h33_r15 : s33.regValue .r15 = orderAddress := (g33.read (n := 64) (r := 15) (by simp)).trans h32_r15
  have h33_rcx : s33.regValue .rcx = 0 := (g33.read (n := 64) (r := 1) (by simp)).trans h32_rcx
  have h33_rdx : s33.regValue .rdx = 0 := (g33.read (n := 64) (r := 2) (by simp)).trans h32_rdx
  have h33_r12 : s33.regValue .r12 = frameBase initial + 8 := (g33.read (n := 64) (r := 12) (by simp)).trans h32_r12
  have h33_rsi : s33.regValue .rsi = 0xbce6faada7179e84 := (g33.read (n := 64) (r := 6) (by simp)).trans h32_rsi
  have h33_rdi : s33.regValue .rdi = 0 := (g33.read (n := 64) (r := 7) (by simp)).trans h32_rdi
  have h33_r9 : s33.regValue .r9 = 0 := (g33.read (n := 64) (r := 9) (by simp)).trans h32_r9
  have scratch33 : memLoad s33.external (stackPtr s33 + 8) 8 = 0 := by
    rw [show stackPtr s33 = stackPtr s32 by rw [f33.rsp, f32.rsp], g33.external (by simp [Component.Covers])]
    exact scratch32
  obtain ⟨s34, a34, ready34, e34⟩ :=
    (test_r64_r64_effect_step 0x10746c 0x48 0xf6 (by simp [RexWPrefix]) rfl).advances
      (readyToStep f33.machine f33.bindingsSupported)
      (programText_slice (programLoaded_codeIn f33.loaded) 0x746c _
        (by decide +kernel) (by decide +kernel)) e33.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x746f (by decide)))
  have g34 : AgreesExcept [.flags, .rip] s33 s34 := e34.agrees
  have f34 := f33.after_registers ready34 g34 (by simp [Component.Covers]) (by simp)
  have zf34 : (StatusFlags.ofRFLAGS s34.RFLAGS).ZF = false := by
    have h := e34.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS s34.RFLAGS).ZF = ((s33.regValue .rsi &&& s33.regValue .rsi) == 0) at h
    rw [h33_rsi] at h
    exact h
  have h34_rax : s34.regValue .rax = 0 := (g34.read (n := 64) (r := 0) (by simp)).trans h33_rax
  have h34_r15 : s34.regValue .r15 = orderAddress := (g34.read (n := 64) (r := 15) (by simp)).trans h33_r15
  have h34_rcx : s34.regValue .rcx = 0 := (g34.read (n := 64) (r := 1) (by simp)).trans h33_rcx
  have h34_rdx : s34.regValue .rdx = 0 := (g34.read (n := 64) (r := 2) (by simp)).trans h33_rdx
  have h34_r12 : s34.regValue .r12 = frameBase initial + 8 := (g34.read (n := 64) (r := 12) (by simp)).trans h33_r12
  have h34_rsi : s34.regValue .rsi = 0xbce6faada7179e84 := (g34.read (n := 64) (r := 6) (by simp)).trans h33_rsi
  have h34_rdi : s34.regValue .rdi = 0 := (g34.read (n := 64) (r := 7) (by simp)).trans h33_rdi
  have h34_r9 : s34.regValue .r9 = 0 := (g34.read (n := 64) (r := 9) (by simp)).trans h33_r9
  have h34_r8 : s34.regValue .r8 = 0 := (g34.read (n := 64) (r := 8) (by simp)).trans h33_r8
  have scratch34 : memLoad s34.external (stackPtr s34 + 8) 8 = 0 := by
    rw [show stackPtr s34 = stackPtr s33 by rw [f34.rsp, f33.rsp], g34.external (by simp [Component.Covers])]
    exact scratch33
  obtain ⟨s35, a35, ready35, e35⟩ :=
    (cmovne_r32_r32_rex_effect_step 0x10746f 0x41 0xd1 (by simp [RexNoWPrefix]) rfl).advances
      (readyToStep f34.machine f34.bindingsSupported)
      (programText_slice (programLoaded_codeIn f34.loaded) 0x746f _
        (by decide +kernel) (by decide +kernel)) e34.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7473 (by decide)))
  have g35 : AgreesExcept [.reg 2, .rip] s34 s35 := e35.agrees
  have f35 := f34.after_registers ready35 g35 (by simp [Component.Covers]) (by simp)
  have h35_rdx : s35.regValue .rdx = 0 := by
    have h : s35.regValue .rdx = ((if condHolds 5 (StatusFlags.ofRFLAGS s34.RFLAGS) then (s34.regValue .r9).setWidth 32 else (s34.regValue .rdx).setWidth 32).setWidth 64) := e35.writes
    rw [h34_rdx, h34_r9] at h
    try simp only [ite_self] at h
    exact h
  have h35_rax : s35.regValue .rax = 0 := (g35.read (n := 64) (r := 0) (by simp)).trans h34_rax
  have h35_r15 : s35.regValue .r15 = orderAddress := (g35.read (n := 64) (r := 15) (by simp)).trans h34_r15
  have h35_rcx : s35.regValue .rcx = 0 := (g35.read (n := 64) (r := 1) (by simp)).trans h34_rcx
  have h35_r12 : s35.regValue .r12 = frameBase initial + 8 := (g35.read (n := 64) (r := 12) (by simp)).trans h34_r12
  have h35_rsi : s35.regValue .rsi = 0xbce6faada7179e84 := (g35.read (n := 64) (r := 6) (by simp)).trans h34_rsi
  have h35_rdi : s35.regValue .rdi = 0 := (g35.read (n := 64) (r := 7) (by simp)).trans h34_rdi
  have h35_r9 : s35.regValue .r9 = 0 := (g35.read (n := 64) (r := 9) (by simp)).trans h34_r9
  have h35_r8 : s35.regValue .r8 = 0 := (g35.read (n := 64) (r := 8) (by simp)).trans h34_r8
  have scratch35 : memLoad s35.external (stackPtr s35 + 8) 8 = 0 := by
    rw [show stackPtr s35 = stackPtr s34 by rw [f35.rsp, f34.rsp], g35.external (by simp [Component.Covers])]
    exact scratch34
  have zf35 : (StatusFlags.ofRFLAGS s35.RFLAGS).ZF = false := by
    rw [g35.rflags (by simp) (by simp)]
    exact zf34
  exact ⟨s35, ((((((((((((((((((((((((a0.trans a12).trans a13).trans a14).trans a15).trans a16).trans a17).trans a18).trans a19).trans a20).trans a21).trans a22).trans a23).trans a24).trans a25).trans a26).trans a27).trans a28).trans a29).trans a30).trans a31).trans a32).trans a33).trans a34).trans a35), f35, e35.rip, h35_r15, h35_rcx, h35_rdx, h35_rax, h35_r12, h35_r8, h35_r9⟩

end P256.Proofs.Nonce.Fill.Tail.Decode.Scan
