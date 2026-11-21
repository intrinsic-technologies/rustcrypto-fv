import P256.Proofs.Common.Encoding.Parser.ByteStore
import P256.Proofs.Nonce.Fill.Tail.Decode.Scan.Prefix
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

import P256.Proofs.Nonce.Initialize.Conversions.Bsr.Memory
import P256.Proofs.HashToCurve.Expand.Fill.Count.Instructions
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

theorem count [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} {original state : Nonce.State}
    (pre : Pre initial boundary orderAddress original)
    (input : Updated initial s orderAddress state) :
    ∃ t, Advances boundary 54 s t ∧ ScanState initial t orderAddress state ∧
      t.RIP = 0x1074b4 ∧
      t.regValue .r15 = orderAddress ∧
      t.regValue .r12 = frameBase initial + 8 ∧
      t.regValue .r14 = 0 ∧
      t.regValue .r8 = 256 ∧ (StatusFlags.ofRFLAGS t.RFLAGS).ZF = true := by
  obtain ⟨s35, a0, f35, rip35, h35_r15, h35_rcx, h35_rdx, h35_rax, h35_r12, h35_r8, h35_r9⟩ := scan_prefix pre input
  obtain ⟨s36, a36, ready36, e36⟩ :=
    (mov_r32_imm32_effect_step 0x107473 0xbe (by decide) 127).advances
      (readyToStep f35.machine f35.bindingsSupported)
      (programText_slice (programLoaded_codeIn f35.loaded) 0x7473 _
        (by decide +kernel) (by decide +kernel)) rip35
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7478 (by decide)))
  have g36 : AgreesExcept [.reg 6, .rip] s35 s36 := e36.agrees
  have f36 := f35.after_registers ready36 g36 (by simp [Component.Covers]) (by simp)
  have h36_rsi : s36.regValue .rsi = 127 := by
    have h : s36.regValue .rsi = 127 := e36.writes
    try simp only [ite_self] at h
    exact h
  have h36_rax : s36.regValue .rax = 0 := (g36.read (n := 64) (r := 0) (by simp)).trans h35_rax
  have h36_r15 : s36.regValue .r15 = orderAddress := (g36.read (n := 64) (r := 15) (by simp)).trans h35_r15
  have h36_rcx : s36.regValue .rcx = 0 := (g36.read (n := 64) (r := 1) (by simp)).trans h35_rcx
  have h36_rdx : s36.regValue .rdx = 0 := (g36.read (n := 64) (r := 2) (by simp)).trans h35_rdx
  have h36_r12 : s36.regValue .r12 = frameBase initial + 8 := (g36.read (n := 64) (r := 12) (by simp)).trans h35_r12
  have h36_r9 : s36.regValue .r9 = 0 := (g36.read (n := 64) (r := 9) (by simp)).trans h35_r9
  have h36_r8 : s36.regValue .r8 = 0 := (g36.read (n := 64) (r := 8) (by simp)).trans h35_r8
  obtain ⟨s37, a37, ready37, e37⟩ :=
    (bsr_r64_m64_effect_step 0x107478 0x49 (by simp [RexWPrefix]) 6 (.base 15 .none) (by decide +kernel) rfl rfl).advances
      (readyToStep f36.machine f36.bindingsSupported)
      (programText_slice (programLoaded_codeIn f36.loaded) 0x7478 _
        (by decide +kernel) (by decide +kernel)) ⟨e36.rip, by
        change MemReadable s36 (s36.regValue .r15 + 0) 8
        exact by
          rw [h36_r15]
          exact f36.order_readable pre (offset := 0) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x747c (by decide)))
  have g37 : AgreesExcept [.reg 6, .flags, .rip] s36 s37 := e37.agrees
  have f37 := f36.after_registers ready37 g37 (by simp [Component.Covers]) (by simp)
  have h37_rsi : s37.regValue .rsi = 63 := by
    have h : s37.regValue .rsi = (bsrSpec64 (s36.regValue .rsi) (memLoad s36.external (s36.regValue .r15 + 0) 64)).1 := e37.writes
    have limb : memLoad s36.external (orderAddress + 0) 64 = 0xf3b9cac2fc632551 := (f36.generator.2.1.memLoad_limb 0 (by decide)).trans (by decide +kernel)
    rw [h36_r15, h36_rsi, limb] at h
    exact h.trans (by decide +kernel)
  have h37_rax : s37.regValue .rax = 0 := (g37.read (n := 64) (r := 0) (by simp)).trans h36_rax
  have h37_r15 : s37.regValue .r15 = orderAddress := (g37.read (n := 64) (r := 15) (by simp)).trans h36_r15
  have h37_rcx : s37.regValue .rcx = 0 := (g37.read (n := 64) (r := 1) (by simp)).trans h36_rcx
  have h37_rdx : s37.regValue .rdx = 0 := (g37.read (n := 64) (r := 2) (by simp)).trans h36_rdx
  have h37_r12 : s37.regValue .r12 = frameBase initial + 8 := (g37.read (n := 64) (r := 12) (by simp)).trans h36_r12
  have h37_r9 : s37.regValue .r9 = 0 := (g37.read (n := 64) (r := 9) (by simp)).trans h36_r9
  have h37_r8 : s37.regValue .r8 = 0 := (g37.read (n := 64) (r := 8) (by simp)).trans h36_r8
  obtain ⟨s38, a38, ready38, e38⟩ :=
    (xor_r32_imm8_effect_step 0x10747c 0xf6 63 rfl rfl).advances
      (readyToStep f37.machine f37.bindingsSupported)
      (programText_slice (programLoaded_codeIn f37.loaded) 0x747c _
        (by decide +kernel) (by decide +kernel)) e37.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x747f (by decide)))
  have g38 : AgreesExcept [.reg 6, .flags, .rip] s37 s38 := e38.agrees
  have f38 := f37.after_registers ready38 g38 (by simp [Component.Covers]) (by simp)
  have h38_rsi : s38.regValue .rsi = 0 := by
    have h : s38.regValue .rsi = ((s37.regValue .rsi).setWidth 32 ^^^ 63).setWidth 64 := e38.writes
    rw [h37_rsi] at h
    try simp only [ite_self] at h
    exact h
  have h38_rax : s38.regValue .rax = 0 := (g38.read (n := 64) (r := 0) (by simp)).trans h37_rax
  have h38_r15 : s38.regValue .r15 = orderAddress := (g38.read (n := 64) (r := 15) (by simp)).trans h37_r15
  have h38_rcx : s38.regValue .rcx = 0 := (g38.read (n := 64) (r := 1) (by simp)).trans h37_rcx
  have h38_rdx : s38.regValue .rdx = 0 := (g38.read (n := 64) (r := 2) (by simp)).trans h37_rdx
  have h38_r12 : s38.regValue .r12 = frameBase initial + 8 := (g38.read (n := 64) (r := 12) (by simp)).trans h37_r12
  have h38_r9 : s38.regValue .r9 = 0 := (g38.read (n := 64) (r := 9) (by simp)).trans h37_r9
  have h38_r8 : s38.regValue .r8 = 0 := (g38.read (n := 64) (r := 8) (by simp)).trans h37_r8
  obtain ⟨s39, a39, ready39, e39⟩ :=
    (mov_m8_r8_legacy_effect_step 0x10747f 2 (by decide) (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl).advances
      (readyToStep f38.machine f38.bindingsSupported)
      (programText_slice (programLoaded_codeIn f38.loaded) 0x747f _
        (by decide +kernel) (by decide +kernel)) ⟨e38.rip, by
        change MemWritable s38 (stackPtr s38 + 8) 1
        exact f38.stack_writable1 pre, by
        exact Fill.stack_code pre f38.toFrame (offset := 8) (len := 1) (codeOffset := 0x747f) (codeLen := 4) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7483 (by decide)))
  have g39 : AgreesExcept [.mem (stackPtr s38 + 8) 1, .rip] s38 s39 := by simpa [movM8Imm8Effect_components, setccM8Effect_components, storeEffect_components, storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr] using e39.agrees
  have f39 := f38.after_store pre ready39 g39 (by decide) (by
    intro slot hs
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl <;> unfold OffsetsApart <;> decide +kernel)
  have scratch39 : memLoad s39.external (stackPtr s39 + 8) 8 = 0 := by
    have h : memLoad s39.external (stackPtr s38 + 8) 8 = (s38.regValue .rdx).setWidth 8 := e39.writes
    rw [h38_rdx] at h
    rwa [show stackPtr s38 = stackPtr s39 by rw [f38.rsp, f39.rsp]] at h
  have h39_rax : s39.regValue .rax = 0 := (g39.read (n := 64) (r := 0) (by simp)).trans h38_rax
  have h39_r15 : s39.regValue .r15 = orderAddress := (g39.read (n := 64) (r := 15) (by simp)).trans h38_r15
  have h39_rcx : s39.regValue .rcx = 0 := (g39.read (n := 64) (r := 1) (by simp)).trans h38_rcx
  have h39_rdx : s39.regValue .rdx = 0 := (g39.read (n := 64) (r := 2) (by simp)).trans h38_rdx
  have h39_r12 : s39.regValue .r12 = frameBase initial + 8 := (g39.read (n := 64) (r := 12) (by simp)).trans h38_r12
  have h39_rsi : s39.regValue .rsi = 0 := (g39.read (n := 64) (r := 6) (by simp)).trans h38_rsi
  have h39_r9 : s39.regValue .r9 = 0 := (g39.read (n := 64) (r := 9) (by simp)).trans h38_r9
  have h39_r8 : s39.regValue .r8 = 0 := (g39.read (n := 64) (r := 8) (by simp)).trans h38_r8
  obtain ⟨s40, a40, ready40, e40⟩ :=
    (movzx_r32_m8_effect_step 0x107483 2 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl).advances
      (readyToStep f39.machine f39.bindingsSupported)
      (programText_slice (programLoaded_codeIn f39.loaded) 0x7483 _
        (by decide +kernel) (by decide +kernel)) ⟨e39.rip, by
        change MemReadable s39 (stackPtr s39 + 8) 1
        exact Fill.stack_readable pre f39.toFrame (offset := 8) (len := 1) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7488 (by decide)))
  have g40 : AgreesExcept [.reg 2, .rip] s39 s40 := e40.agrees
  have f40 := f39.after_registers ready40 g40 (by simp [Component.Covers]) (by simp)
  have h40_rdx : s40.regValue .rdx = 0 := by
    have h : s40.regValue .rdx = (memLoad s39.external (stackPtr s39 + 8) 8).setWidth 64 := e40.writes
    rw [scratch39] at h
    try simp only [ite_self] at h
    exact h
  have h40_rax : s40.regValue .rax = 0 := (g40.read (n := 64) (r := 0) (by simp)).trans h39_rax
  have h40_r15 : s40.regValue .r15 = orderAddress := (g40.read (n := 64) (r := 15) (by simp)).trans h39_r15
  have h40_rcx : s40.regValue .rcx = 0 := (g40.read (n := 64) (r := 1) (by simp)).trans h39_rcx
  have h40_r12 : s40.regValue .r12 = frameBase initial + 8 := (g40.read (n := 64) (r := 12) (by simp)).trans h39_r12
  have h40_rsi : s40.regValue .rsi = 0 := (g40.read (n := 64) (r := 6) (by simp)).trans h39_rsi
  have h40_r9 : s40.regValue .r9 = 0 := (g40.read (n := 64) (r := 9) (by simp)).trans h39_r9
  have h40_r8 : s40.regValue .r8 = 0 := (g40.read (n := 64) (r := 8) (by simp)).trans h39_r8
  have scratch40 : memLoad s40.external (stackPtr s40 + 8) 8 = 0 := by
    rw [show stackPtr s40 = stackPtr s39 by rw [f40.rsp, f39.rsp], g40.external (by simp [Component.Covers])]
    exact scratch39
  obtain ⟨s41, a41, ready41, e41⟩ :=
    (neg_r32_effect_step 0x107488 0xda rfl rfl).advances
      (readyToStep f40.machine f40.bindingsSupported)
      (programText_slice (programLoaded_codeIn f40.loaded) 0x7488 _
        (by decide +kernel) (by decide +kernel)) e40.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x748a (by decide)))
  have g41 : AgreesExcept [.reg 2, .flags, .rip] s40 s41 := e41.agrees
  have f41 := f40.after_registers ready41 g41 (by simp [Component.Covers]) (by simp)
  have h41_rdx : s41.regValue .rdx = 0 := by
    have h : s41.regValue .rdx = (-(s40.regValue .rdx).setWidth 32).setWidth 64 := e41.writes
    rw [h40_rdx] at h
    try simp only [ite_self] at h
    exact h
  have h41_rax : s41.regValue .rax = 0 := (g41.read (n := 64) (r := 0) (by simp)).trans h40_rax
  have h41_r15 : s41.regValue .r15 = orderAddress := (g41.read (n := 64) (r := 15) (by simp)).trans h40_r15
  have h41_rcx : s41.regValue .rcx = 0 := (g41.read (n := 64) (r := 1) (by simp)).trans h40_rcx
  have h41_r12 : s41.regValue .r12 = frameBase initial + 8 := (g41.read (n := 64) (r := 12) (by simp)).trans h40_r12
  have h41_rsi : s41.regValue .rsi = 0 := (g41.read (n := 64) (r := 6) (by simp)).trans h40_rsi
  have h41_r9 : s41.regValue .r9 = 0 := (g41.read (n := 64) (r := 9) (by simp)).trans h40_r9
  have h41_r8 : s41.regValue .r8 = 0 := (g41.read (n := 64) (r := 8) (by simp)).trans h40_r8
  have scratch41 : memLoad s41.external (stackPtr s41 + 8) 8 = 0 := by
    rw [show stackPtr s41 = stackPtr s40 by rw [f41.rsp, f40.rsp], g41.external (by simp [Component.Covers])]
    exact scratch40
  obtain ⟨s42, a42, ready42, e42⟩ :=
    (and_r32_r32_effect_step 0x10748a 0xf2 rfl).advances
      (readyToStep f41.machine f41.bindingsSupported)
      (programText_slice (programLoaded_codeIn f41.loaded) 0x748a _
        (by decide +kernel) (by decide +kernel)) e41.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x748c (by decide)))
  have g42 : AgreesExcept [.reg 2, .flags, .rip] s41 s42 := e42.agrees
  have f42 := f41.after_registers ready42 g42 (by simp [Component.Covers]) (by simp)
  have h42_rdx : s42.regValue .rdx = 0 := by
    have h : s42.regValue .rdx = ((s41.regValue .rdx).setWidth 32 &&& (s41.regValue .rsi).setWidth 32).setWidth 64 := e42.writes
    rw [h41_rdx, h41_rsi] at h
    try simp only [ite_self] at h
    exact h
  have h42_rax : s42.regValue .rax = 0 := (g42.read (n := 64) (r := 0) (by simp)).trans h41_rax
  have h42_r15 : s42.regValue .r15 = orderAddress := (g42.read (n := 64) (r := 15) (by simp)).trans h41_r15
  have h42_rcx : s42.regValue .rcx = 0 := (g42.read (n := 64) (r := 1) (by simp)).trans h41_rcx
  have h42_r12 : s42.regValue .r12 = frameBase initial + 8 := (g42.read (n := 64) (r := 12) (by simp)).trans h41_r12
  have h42_rsi : s42.regValue .rsi = 0 := (g42.read (n := 64) (r := 6) (by simp)).trans h41_rsi
  have h42_r9 : s42.regValue .r9 = 0 := (g42.read (n := 64) (r := 9) (by simp)).trans h41_r9
  have h42_r8 : s42.regValue .r8 = 0 := (g42.read (n := 64) (r := 8) (by simp)).trans h41_r8
  have scratch42 : memLoad s42.external (stackPtr s42 + 8) 8 = 0 := by
    rw [show stackPtr s42 = stackPtr s41 by rw [f42.rsp, f41.rsp], g42.external (by simp [Component.Covers])]
    exact scratch41
  obtain ⟨s43, a43, ready43, e43⟩ :=
    (add_r32_r32_effect_step 0x10748c 0xc1 rfl).advances
      (readyToStep f42.machine f42.bindingsSupported)
      (programText_slice (programLoaded_codeIn f42.loaded) 0x748c _
        (by decide +kernel) (by decide +kernel)) e42.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x748e (by decide)))
  have g43 : AgreesExcept [.reg 1, .flags, .rip] s42 s43 := e43.agrees
  have f43 := f42.after_registers ready43 g43 (by simp [Component.Covers]) (by simp)
  have h43_rcx : s43.regValue .rcx = 0 := by
    have h : s43.regValue .rcx = ((s42.regValue .rcx).setWidth 32 + (s42.regValue .rax).setWidth 32).setWidth 64 := e43.writes
    rw [h42_rax, h42_rcx] at h
    try simp only [ite_self] at h
    exact h
  have h43_rax : s43.regValue .rax = 0 := (g43.read (n := 64) (r := 0) (by simp)).trans h42_rax
  have h43_r15 : s43.regValue .r15 = orderAddress := (g43.read (n := 64) (r := 15) (by simp)).trans h42_r15
  have h43_rdx : s43.regValue .rdx = 0 := (g43.read (n := 64) (r := 2) (by simp)).trans h42_rdx
  have h43_r12 : s43.regValue .r12 = frameBase initial + 8 := (g43.read (n := 64) (r := 12) (by simp)).trans h42_r12
  have h43_rsi : s43.regValue .rsi = 0 := (g43.read (n := 64) (r := 6) (by simp)).trans h42_rsi
  have h43_r9 : s43.regValue .r9 = 0 := (g43.read (n := 64) (r := 9) (by simp)).trans h42_r9
  have h43_r8 : s43.regValue .r8 = 0 := (g43.read (n := 64) (r := 8) (by simp)).trans h42_r8
  have scratch43 : memLoad s43.external (stackPtr s43 + 8) 8 = 0 := by
    rw [show stackPtr s43 = stackPtr s42 by rw [f43.rsp, f42.rsp], g43.external (by simp [Component.Covers])]
    exact scratch42
  obtain ⟨s44, a44, ready44, e44⟩ :=
    (add_r32_r32_rex_effect_step 0x10748e 0x44 0xc2 (by simp [RexNoWPrefix]) rfl).advances
      (readyToStep f43.machine f43.bindingsSupported)
      (programText_slice (programLoaded_codeIn f43.loaded) 0x748e _
        (by decide +kernel) (by decide +kernel)) e43.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7491 (by decide)))
  have g44 : AgreesExcept [.reg 2, .flags, .rip] s43 s44 := e44.agrees
  have f44 := f43.after_registers ready44 g44 (by simp [Component.Covers]) (by simp)
  have h44_rdx : s44.regValue .rdx = 0 := by
    have h : s44.regValue .rdx = ((s43.regValue .rdx).setWidth 32 + (s43.regValue .r8).setWidth 32).setWidth 64 := e44.writes
    rw [h43_rdx, h43_r8] at h
    try simp only [ite_self] at h
    exact h
  have h44_rax : s44.regValue .rax = 0 := (g44.read (n := 64) (r := 0) (by simp)).trans h43_rax
  have h44_r15 : s44.regValue .r15 = orderAddress := (g44.read (n := 64) (r := 15) (by simp)).trans h43_r15
  have h44_rcx : s44.regValue .rcx = 0 := (g44.read (n := 64) (r := 1) (by simp)).trans h43_rcx
  have h44_r12 : s44.regValue .r12 = frameBase initial + 8 := (g44.read (n := 64) (r := 12) (by simp)).trans h43_r12
  have h44_rsi : s44.regValue .rsi = 0 := (g44.read (n := 64) (r := 6) (by simp)).trans h43_rsi
  have h44_r9 : s44.regValue .r9 = 0 := (g44.read (n := 64) (r := 9) (by simp)).trans h43_r9
  have h44_r8 : s44.regValue .r8 = 0 := (g44.read (n := 64) (r := 8) (by simp)).trans h43_r8
  have scratch44 : memLoad s44.external (stackPtr s44 + 8) 8 = 0 := by
    rw [show stackPtr s44 = stackPtr s43 by rw [f44.rsp, f43.rsp], g44.external (by simp [Component.Covers])]
    exact scratch43
  obtain ⟨s45, a45, ready45, e45⟩ :=
    (add_r32_r32_effect_step 0x107491 0xca rfl).advances
      (readyToStep f44.machine f44.bindingsSupported)
      (programText_slice (programLoaded_codeIn f44.loaded) 0x7491 _
        (by decide +kernel) (by decide +kernel)) e44.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7493 (by decide)))
  have g45 : AgreesExcept [.reg 2, .flags, .rip] s44 s45 := e45.agrees
  have f45 := f44.after_registers ready45 g45 (by simp [Component.Covers]) (by simp)
  have h45_rdx : s45.regValue .rdx = 0 := by
    have h : s45.regValue .rdx = ((s44.regValue .rdx).setWidth 32 + (s44.regValue .rcx).setWidth 32).setWidth 64 := e45.writes
    rw [h44_rcx, h44_rdx] at h
    try simp only [ite_self] at h
    exact h
  have h45_rax : s45.regValue .rax = 0 := (g45.read (n := 64) (r := 0) (by simp)).trans h44_rax
  have h45_r15 : s45.regValue .r15 = orderAddress := (g45.read (n := 64) (r := 15) (by simp)).trans h44_r15
  have h45_rcx : s45.regValue .rcx = 0 := (g45.read (n := 64) (r := 1) (by simp)).trans h44_rcx
  have h45_r12 : s45.regValue .r12 = frameBase initial + 8 := (g45.read (n := 64) (r := 12) (by simp)).trans h44_r12
  have h45_rsi : s45.regValue .rsi = 0 := (g45.read (n := 64) (r := 6) (by simp)).trans h44_rsi
  have h45_r9 : s45.regValue .r9 = 0 := (g45.read (n := 64) (r := 9) (by simp)).trans h44_r9
  have h45_r8 : s45.regValue .r8 = 0 := (g45.read (n := 64) (r := 8) (by simp)).trans h44_r8
  have scratch45 : memLoad s45.external (stackPtr s45 + 8) 8 = 0 := by
    rw [show stackPtr s45 = stackPtr s44 by rw [f45.rsp, f44.rsp], g45.external (by simp [Component.Covers])]
    exact scratch44
  obtain ⟨s46, a46, ready46, e46⟩ :=
    (mov_r32_imm32_effect_step 0x107493 0xb8 (by decide) 256).advances
      (readyToStep f45.machine f45.bindingsSupported)
      (programText_slice (programLoaded_codeIn f45.loaded) 0x7493 _
        (by decide +kernel) (by decide +kernel)) e45.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x7498 (by decide)))
  have g46 : AgreesExcept [.reg 0, .rip] s45 s46 := e46.agrees
  have f46 := f45.after_registers ready46 g46 (by simp [Component.Covers]) (by simp)
  have h46_rax : s46.regValue .rax = 256 := by
    have h : s46.regValue .rax = 256 := e46.writes
    try simp only [ite_self] at h
    exact h
  have h46_r15 : s46.regValue .r15 = orderAddress := (g46.read (n := 64) (r := 15) (by simp)).trans h45_r15
  have h46_rcx : s46.regValue .rcx = 0 := (g46.read (n := 64) (r := 1) (by simp)).trans h45_rcx
  have h46_rdx : s46.regValue .rdx = 0 := (g46.read (n := 64) (r := 2) (by simp)).trans h45_rdx
  have h46_r12 : s46.regValue .r12 = frameBase initial + 8 := (g46.read (n := 64) (r := 12) (by simp)).trans h45_r12
  have h46_rsi : s46.regValue .rsi = 0 := (g46.read (n := 64) (r := 6) (by simp)).trans h45_rsi
  have h46_r9 : s46.regValue .r9 = 0 := (g46.read (n := 64) (r := 9) (by simp)).trans h45_r9
  have h46_r8 : s46.regValue .r8 = 0 := (g46.read (n := 64) (r := 8) (by simp)).trans h45_r8
  have scratch46 : memLoad s46.external (stackPtr s46 + 8) 8 = 0 := by
    rw [show stackPtr s46 = stackPtr s45 by rw [f46.rsp, f45.rsp], g46.external (by simp [Component.Covers])]
    exact scratch45
  obtain ⟨s47, a47, ready47, e47⟩ :=
    (sub_r32_r32_effect_step 0x107498 0xd0 rfl).advances
      (readyToStep f46.machine f46.bindingsSupported)
      (programText_slice (programLoaded_codeIn f46.loaded) 0x7498 _
        (by decide +kernel) (by decide +kernel)) e46.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x749a (by decide)))
  have g47 : AgreesExcept [.reg 0, .flags, .rip] s46 s47 := e47.agrees
  have f47 := f46.after_registers ready47 g47 (by simp [Component.Covers]) (by simp)
  have h47_rax : s47.regValue .rax = 256 := by
    have h : s47.regValue .rax = ((s46.regValue .rax).setWidth 32 - (s46.regValue .rdx).setWidth 32).setWidth 64 := e47.writes
    rw [h46_rax, h46_rdx] at h
    try simp only [ite_self] at h
    exact h
  have h47_r15 : s47.regValue .r15 = orderAddress := (g47.read (n := 64) (r := 15) (by simp)).trans h46_r15
  have h47_rcx : s47.regValue .rcx = 0 := (g47.read (n := 64) (r := 1) (by simp)).trans h46_rcx
  have h47_rdx : s47.regValue .rdx = 0 := (g47.read (n := 64) (r := 2) (by simp)).trans h46_rdx
  have h47_r12 : s47.regValue .r12 = frameBase initial + 8 := (g47.read (n := 64) (r := 12) (by simp)).trans h46_r12
  have h47_rsi : s47.regValue .rsi = 0 := (g47.read (n := 64) (r := 6) (by simp)).trans h46_rsi
  have h47_r9 : s47.regValue .r9 = 0 := (g47.read (n := 64) (r := 9) (by simp)).trans h46_r9
  have h47_r8 : s47.regValue .r8 = 0 := (g47.read (n := 64) (r := 8) (by simp)).trans h46_r8
  have scratch47 : memLoad s47.external (stackPtr s47 + 8) 8 = 0 := by
    rw [show stackPtr s47 = stackPtr s46 by rw [f47.rsp, f46.rsp], g47.external (by simp [Component.Covers])]
    exact scratch46
  obtain ⟨s48, a48, ready48, e48⟩ :=
    (mov_r32_m32_effect_step 0x10749a 0x44 (by simp [RexNoWPrefix]) 0 (.sib 4 none 0 (.d8 56)) (by decide +kernel) rfl rfl).advances
      (readyToStep f47.machine f47.bindingsSupported)
      (programText_slice (programLoaded_codeIn f47.loaded) 0x749a _
        (by decide +kernel) (by decide +kernel)) ⟨e47.rip, by
        change MemReadable s47 (stackPtr s47 + 56) 4
        exact Fill.stack_readable pre f47.toFrame (offset := 56) (len := 4) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x749f (by decide)))
  have g48 : AgreesExcept [.reg 8, .rip] s47 s48 := e48.agrees
  have f48 := f47.after_registers ready48 g48 (by simp [Component.Covers]) (by simp)
  have h48_r8 : s48.regValue .r8 = 256 := by
    have h : s48.regValue .r8 = (memLoad s47.external (stackPtr s47 + 56) 32).setWidth 64 := e48.writes
    rw [f47.rsp, f47.bitsSlot] at h
    try simp only [ite_self] at h
    exact h
  have h48_rax : s48.regValue .rax = 256 := (g48.read (n := 64) (r := 0) (by simp)).trans h47_rax
  have h48_r15 : s48.regValue .r15 = orderAddress := (g48.read (n := 64) (r := 15) (by simp)).trans h47_r15
  have h48_rcx : s48.regValue .rcx = 0 := (g48.read (n := 64) (r := 1) (by simp)).trans h47_rcx
  have h48_rdx : s48.regValue .rdx = 0 := (g48.read (n := 64) (r := 2) (by simp)).trans h47_rdx
  have h48_r12 : s48.regValue .r12 = frameBase initial + 8 := (g48.read (n := 64) (r := 12) (by simp)).trans h47_r12
  have h48_rsi : s48.regValue .rsi = 0 := (g48.read (n := 64) (r := 6) (by simp)).trans h47_rsi
  have h48_r9 : s48.regValue .r9 = 0 := (g48.read (n := 64) (r := 9) (by simp)).trans h47_r9
  have scratch48 : memLoad s48.external (stackPtr s48 + 8) 8 = 0 := by
    rw [show stackPtr s48 = stackPtr s47 by rw [f48.rsp, f47.rsp], g48.external (by simp [Component.Covers])]
    exact scratch47
  obtain ⟨s49, a49, ready49, e49⟩ :=
    (mov_r32_r32_rex_effect_step 0x10749f 0x45 0xc6 (by simp [RexNoWPrefix]) rfl).advances
      (readyToStep f48.machine f48.bindingsSupported)
      (programText_slice (programLoaded_codeIn f48.loaded) 0x749f _
        (by decide +kernel) (by decide +kernel)) e48.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x74a2 (by decide)))
  have g49 : AgreesExcept [.reg 14, .rip] s48 s49 := e49.agrees
  have f49 := f48.after_registers ready49 g49 (by simp [Component.Covers]) (by simp)
  have h49_r14 : s49.regValue .r14 = 256 := by
    have h : s49.regValue .r14 = ((s48.regValue .r8).setWidth 32).setWidth 64 := e49.writes
    rw [h48_r8] at h
    try simp only [ite_self] at h
    exact h
  have h49_rax : s49.regValue .rax = 256 := (g49.read (n := 64) (r := 0) (by simp)).trans h48_rax
  have h49_r15 : s49.regValue .r15 = orderAddress := (g49.read (n := 64) (r := 15) (by simp)).trans h48_r15
  have h49_rcx : s49.regValue .rcx = 0 := (g49.read (n := 64) (r := 1) (by simp)).trans h48_rcx
  have h49_rdx : s49.regValue .rdx = 0 := (g49.read (n := 64) (r := 2) (by simp)).trans h48_rdx
  have h49_r12 : s49.regValue .r12 = frameBase initial + 8 := (g49.read (n := 64) (r := 12) (by simp)).trans h48_r12
  have h49_rsi : s49.regValue .rsi = 0 := (g49.read (n := 64) (r := 6) (by simp)).trans h48_rsi
  have h49_r9 : s49.regValue .r9 = 0 := (g49.read (n := 64) (r := 9) (by simp)).trans h48_r9
  have h49_r8 : s49.regValue .r8 = 256 := (g49.read (n := 64) (r := 8) (by simp)).trans h48_r8
  have scratch49 : memLoad s49.external (stackPtr s49 + 8) 8 = 0 := by
    rw [show stackPtr s49 = stackPtr s48 by rw [f49.rsp, f48.rsp], g49.external (by simp [Component.Covers])]
    exact scratch48
  obtain ⟨s50, a50, ready50, e50⟩ :=
    (sub_r32_r32_rex_effect_step 0x1074a2 0x41 0xc6 (by simp [RexNoWPrefix]) rfl).advances
      (readyToStep f49.machine f49.bindingsSupported)
      (programText_slice (programLoaded_codeIn f49.loaded) 0x74a2 _
        (by decide +kernel) (by decide +kernel)) e49.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x74a5 (by decide)))
  have g50 : AgreesExcept [.reg 14, .flags, .rip] s49 s50 := e50.agrees
  have f50 := f49.after_registers ready50 g50 (by simp [Component.Covers]) (by simp)
  have h50_r14 : s50.regValue .r14 = 0 := by
    have h : s50.regValue .r14 = ((s49.regValue .r14).setWidth 32 - (s49.regValue .rax).setWidth 32).setWidth 64 := e50.writes
    rw [h49_rax, h49_r14] at h
    try simp only [ite_self] at h
    exact h
  have h50_rax : s50.regValue .rax = 256 := (g50.read (n := 64) (r := 0) (by simp)).trans h49_rax
  have h50_r15 : s50.regValue .r15 = orderAddress := (g50.read (n := 64) (r := 15) (by simp)).trans h49_r15
  have h50_rcx : s50.regValue .rcx = 0 := (g50.read (n := 64) (r := 1) (by simp)).trans h49_rcx
  have h50_rdx : s50.regValue .rdx = 0 := (g50.read (n := 64) (r := 2) (by simp)).trans h49_rdx
  have h50_r12 : s50.regValue .r12 = frameBase initial + 8 := (g50.read (n := 64) (r := 12) (by simp)).trans h49_r12
  have h50_rsi : s50.regValue .rsi = 0 := (g50.read (n := 64) (r := 6) (by simp)).trans h49_rsi
  have h50_r9 : s50.regValue .r9 = 0 := (g50.read (n := 64) (r := 9) (by simp)).trans h49_r9
  have h50_r8 : s50.regValue .r8 = 256 := (g50.read (n := 64) (r := 8) (by simp)).trans h49_r8
  have scratch50 : memLoad s50.external (stackPtr s50 + 8) 8 = 0 := by
    rw [show stackPtr s50 = stackPtr s49 by rw [f50.rsp, f49.rsp], g50.external (by simp [Component.Covers])]
    exact scratch49
  obtain ⟨s51, a51, ready51, e51⟩ :=
    (mov_r32_imm32_effect_step 0x1074a5 0xba (by decide) 0).advances
      (readyToStep f50.machine f50.bindingsSupported)
      (programText_slice (programLoaded_codeIn f50.loaded) 0x74a5 _
        (by decide +kernel) (by decide +kernel)) e50.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x74aa (by decide)))
  have g51 : AgreesExcept [.reg 2, .rip] s50 s51 := e51.agrees
  have f51 := f50.after_registers ready51 g51 (by simp [Component.Covers]) (by simp)
  have h51_rdx : s51.regValue .rdx = 0 := by
    have h : s51.regValue .rdx = 0 := e51.writes
    try simp only [ite_self] at h
    exact h
  have h51_rax : s51.regValue .rax = 256 := (g51.read (n := 64) (r := 0) (by simp)).trans h50_rax
  have h51_r15 : s51.regValue .r15 = orderAddress := (g51.read (n := 64) (r := 15) (by simp)).trans h50_r15
  have h51_rcx : s51.regValue .rcx = 0 := (g51.read (n := 64) (r := 1) (by simp)).trans h50_rcx
  have h51_r12 : s51.regValue .r12 = frameBase initial + 8 := (g51.read (n := 64) (r := 12) (by simp)).trans h50_r12
  have h51_rsi : s51.regValue .rsi = 0 := (g51.read (n := 64) (r := 6) (by simp)).trans h50_rsi
  have h51_r9 : s51.regValue .r9 = 0 := (g51.read (n := 64) (r := 9) (by simp)).trans h50_r9
  have h51_r8 : s51.regValue .r8 = 256 := (g51.read (n := 64) (r := 8) (by simp)).trans h50_r8
  have h51_r14 : s51.regValue .r14 = 0 := (g51.read (n := 64) (r := 14) (by simp)).trans h50_r14
  have scratch51 : memLoad s51.external (stackPtr s51 + 8) 8 = 0 := by
    rw [show stackPtr s51 = stackPtr s50 by rw [f51.rsp, f50.rsp], g51.external (by simp [Component.Covers])]
    exact scratch50
  obtain ⟨s52, a52, ready52, e52⟩ :=
    (P256.Proofs.HashToCurve.Expand.Fill.Count.cmovb_r32_r32_rex_effect_step 0x1074aa 0x45 0xf1 (by simp [RexNoWPrefix]) rfl).advances
      (readyToStep f51.machine f51.bindingsSupported)
      (programText_slice (programLoaded_codeIn f51.loaded) 0x74aa _
        (by decide +kernel) (by decide +kernel)) e51.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x74ae (by decide)))
  have g52 : AgreesExcept [.reg 14, .rip] s51 s52 := e52.agrees
  have f52 := f51.after_registers ready52 g52 (by simp [Component.Covers]) (by simp)
  have h52_r14 : s52.regValue .r14 = 0 := by
    have h : s52.regValue .r14 = ((if condHolds 2 (StatusFlags.ofRFLAGS s51.RFLAGS) then (s51.regValue .r9).setWidth 32 else (s51.regValue .r14).setWidth 32).setWidth 64) := e52.writes
    rw [h51_r9, h51_r14] at h
    try simp only [ite_self] at h
    exact h
  have h52_rax : s52.regValue .rax = 256 := (g52.read (n := 64) (r := 0) (by simp)).trans h51_rax
  have h52_r15 : s52.regValue .r15 = orderAddress := (g52.read (n := 64) (r := 15) (by simp)).trans h51_r15
  have h52_rcx : s52.regValue .rcx = 0 := (g52.read (n := 64) (r := 1) (by simp)).trans h51_rcx
  have h52_rdx : s52.regValue .rdx = 0 := (g52.read (n := 64) (r := 2) (by simp)).trans h51_rdx
  have h52_r12 : s52.regValue .r12 = frameBase initial + 8 := (g52.read (n := 64) (r := 12) (by simp)).trans h51_r12
  have h52_rsi : s52.regValue .rsi = 0 := (g52.read (n := 64) (r := 6) (by simp)).trans h51_rsi
  have h52_r9 : s52.regValue .r9 = 0 := (g52.read (n := 64) (r := 9) (by simp)).trans h51_r9
  have h52_r8 : s52.regValue .r8 = 256 := (g52.read (n := 64) (r := 8) (by simp)).trans h51_r8
  have scratch52 : memLoad s52.external (stackPtr s52 + 8) 8 = 0 := by
    rw [show stackPtr s52 = stackPtr s51 by rw [f52.rsp, f51.rsp], g52.external (by simp [Component.Covers])]
    exact scratch51
  obtain ⟨s53, a53, ready53, e53⟩ :=
    (mov_r32_r32_rex_effect_step 0x1074ae 0x44 0xf1 (by simp [RexNoWPrefix]) rfl).advances
      (readyToStep f52.machine f52.bindingsSupported)
      (programText_slice (programLoaded_codeIn f52.loaded) 0x74ae _
        (by decide +kernel) (by decide +kernel)) e52.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x74b1 (by decide)))
  have g53 : AgreesExcept [.reg 1, .rip] s52 s53 := e53.agrees
  have f53 := f52.after_registers ready53 g53 (by simp [Component.Covers]) (by simp)
  have h53_rcx : s53.regValue .rcx = 0 := by
    have h : s53.regValue .rcx = ((s52.regValue .r14).setWidth 32).setWidth 64 := e53.writes
    rw [h52_r14] at h
    try simp only [ite_self] at h
    exact h
  have h53_rax : s53.regValue .rax = 256 := (g53.read (n := 64) (r := 0) (by simp)).trans h52_rax
  have h53_r15 : s53.regValue .r15 = orderAddress := (g53.read (n := 64) (r := 15) (by simp)).trans h52_r15
  have h53_rdx : s53.regValue .rdx = 0 := (g53.read (n := 64) (r := 2) (by simp)).trans h52_rdx
  have h53_r12 : s53.regValue .r12 = frameBase initial + 8 := (g53.read (n := 64) (r := 12) (by simp)).trans h52_r12
  have h53_rsi : s53.regValue .rsi = 0 := (g53.read (n := 64) (r := 6) (by simp)).trans h52_rsi
  have h53_r9 : s53.regValue .r9 = 0 := (g53.read (n := 64) (r := 9) (by simp)).trans h52_r9
  have h53_r8 : s53.regValue .r8 = 256 := (g53.read (n := 64) (r := 8) (by simp)).trans h52_r8
  have h53_r14 : s53.regValue .r14 = 0 := (g53.read (n := 64) (r := 14) (by simp)).trans h52_r14
  have scratch53 : memLoad s53.external (stackPtr s53 + 8) 8 = 0 := by
    rw [show stackPtr s53 = stackPtr s52 by rw [f53.rsp, f52.rsp], g53.external (by simp [Component.Covers])]
    exact scratch52
  obtain ⟨s54, a54, ready54, e54⟩ :=
    (shr_r32_imm8_effect_step 0x1074b1 0xe9 3 rfl rfl).advances
      (readyToStep f53.machine f53.bindingsSupported)
      (programText_slice (programLoaded_codeIn f53.loaded) 0x74b1 _
        (by decide +kernel) (by decide +kernel)) e53.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x74b4 (by decide)))
  have g54 : AgreesExcept [.reg 1, .flags, .rip] s53 s54 := e54.agrees
  have f54 := f53.after_registers ready54 g54 (by simp [Component.Covers]) (by simp)
  have h54_rcx : s54.regValue .rcx = 0 := by
    have h : s54.regValue .rcx = ((s53.regValue .rcx).setWidth 32 >>> (3 : Nat)).setWidth 64 := e54.writes
    rw [h53_rcx] at h
    try simp only [ite_self] at h
    exact h
  have h54_rax : s54.regValue .rax = 256 := (g54.read (n := 64) (r := 0) (by simp)).trans h53_rax
  have h54_r15 : s54.regValue .r15 = orderAddress := (g54.read (n := 64) (r := 15) (by simp)).trans h53_r15
  have h54_rdx : s54.regValue .rdx = 0 := (g54.read (n := 64) (r := 2) (by simp)).trans h53_rdx
  have h54_r12 : s54.regValue .r12 = frameBase initial + 8 := (g54.read (n := 64) (r := 12) (by simp)).trans h53_r12
  have h54_rsi : s54.regValue .rsi = 0 := (g54.read (n := 64) (r := 6) (by simp)).trans h53_rsi
  have h54_r9 : s54.regValue .r9 = 0 := (g54.read (n := 64) (r := 9) (by simp)).trans h53_r9
  have h54_r8 : s54.regValue .r8 = 256 := (g54.read (n := 64) (r := 8) (by simp)).trans h53_r8
  have h54_r14 : s54.regValue .r14 = 0 := (g54.read (n := 64) (r := 14) (by simp)).trans h53_r14
  have scratch54 : memLoad s54.external (stackPtr s54 + 8) 8 = 0 := by
    rw [show stackPtr s54 = stackPtr s53 by rw [f54.rsp, f53.rsp], g54.external (by simp [Component.Covers])]
    exact scratch53
  have finalZF : (StatusFlags.ofRFLAGS s54.RFLAGS).ZF = true := by
    have h := e54.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS s54.RFLAGS).ZF = (((s53.regValue .rcx).setWidth 32 >>> (3 : Nat)) == 0) at h
    rw [h53_rcx] at h
    exact h
  exact ⟨s54, (((((((((((((((((((a0.trans a36).trans a37).trans a38).trans a39).trans a40).trans a41).trans a42).trans a43).trans a44).trans a45).trans a46).trans a47).trans a48).trans a49).trans a50).trans a51).trans a52).trans a53).trans a54), f54, e54.rip, h54_r15, h54_r12, h54_r14, h54_r8, finalZF⟩

end P256.Proofs.Nonce.Fill.Tail.Decode.Scan
