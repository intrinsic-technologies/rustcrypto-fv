import P256.Proofs.Verifying.Combination.Naf.Iterator.InitializePrefix
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.EffectCompose.Conditions
import X86Proofs.Instructions.Movs.RepTriple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Instructions.And.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple
import X86Proofs.Instructions.Not.Generated.R.Triple
import X86Proofs.Instructions.Rol.Generated.R.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Xor.Generated.RM.Triple
import X86Proofs.Instructions.Xor.Generated.MR.Triple
import X86Proofs.Instructions.Sub.Generated.RR.Triple
import X86Proofs.Instructions.Shr.Generated.R.Triple
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Movs.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.And.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Iterator

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

structure InitializeReadPre (s : RamState) : Prop where
  rip : s.RIP = 0x1182e7
  length : s.regValue .rdx = 32
  input : MemReadable s (s.regValue .rsi) 16

def initializeReadBytes : List UInt8 :=
  Extracted.textBytes.toListFrom 0x182e7 79

def initializeReadEffect (s : RamState) : Effect :=
  { rip := 0x1182c5
    writes := [⟨(Operand.reg 0 : Operand 64), s.regValue .rsi + 8⟩,
      ⟨(Operand.reg 14 : Operand 64), memLoad s.external (s.regValue .rsi) 64⟩,
      ⟨(Operand.reg 1 : Operand 64), memLoad s.external (s.regValue .rsi + 8) 64⟩,
      ⟨(Operand.reg 2 : Operand 64), 16⟩,
      ⟨(Operand.reg 6 : Operand 64), s.regValue .rsi + 16⟩]
    flags := some ⟨none,none,none,none,none,none⟩ }

theorem readable_subrange {s : RamState} {addr : BitVec 64} {len : Nat}
    (h : MemReadable s addr len) (offset count : Nat) (bound : offset + count ≤ len) :
    MemReadable s (addr + BitVec.ofNat 64 offset) count := by
  have low := h.low
  constructor
  · rw [toNat_add_ofNat _ _ (by omega)]
    omega
  · intro i hi
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact h.mem (offset + i) (by omega)

theorem initialize_read [Bindings] (boundary : ReturnBoundary) (hout : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary InitializeReadPre (codeRange 0x1182e7 initializeReadBytes)
      (Effect.post initializeReadEffect) := by
  intro s ready code pre
  obtain ⟨s1, run1, ready1, e1⟩ :=
    (lea_r64_effect_step 0x1182e7 0x48 (by simp [RexWPrefix]) 0
      (.base 6 (.d8 8)) (by decide +kernel) rfl rfl).advances ready
      (code.mono (codeRange_slice_subset 0x1182e7 initializeReadBytes 0 4)) pre.rip
      (boundary_ne_program hout (inProgram_of_textOffset 0x182eb (by decide)))
  change (leaR64Effect 0x1182e7 0 (.base 6 (.d8 8)) s).Holds s s1 at e1
  have code1 := e1.codeIn (Effect.Avoids.of_noMem (by simp [Component.Covers]) _) code
  obtain ⟨s2, run2, ready2, e2⟩ :=
    (mov_r64_r64_effect_step 0x1182eb 0x48 0xd1 (by simp [RexWPrefix]) rfl).advances ready1
      (code1.mono (codeRange_slice_subset 0x1182e7 initializeReadBytes 4 3)) e1.rip
      (boundary_ne_program hout (inProgram_of_textOffset 0x182ee (by decide)))
  change (movR64R64Effect 0x1182eb 1 2 s1).Holds s1 s2 at e2
  have code2 := e2.codeIn (Effect.Avoids.of_noMem (by simp [Component.Covers]) _) code1
  have ag2 := e1.agrees.trans e2.agrees
  have rsi2 : s2.regValue .rsi = s.regValue .rsi := ag2.read (n := 64) (r := 6) (by simp)
  have rcx2 : s2.regValue .rcx = 32 := e2.writes.trans
    ((e1.agrees.read (n := 64) (r := 2) (by simp)).trans pre.length)
  obtain ⟨s3, run3, ready3, e3⟩ :=
    (mov_r64_m64_effect_step 0x1182ee 0x4c (by simp [RexWPrefix]) 6
      (.base 6 .none) (by decide +kernel) rfl rfl).advances ready2
      (code2.mono (codeRange_slice_subset 0x1182e7 initializeReadBytes 7 3))
      ⟨e2.rip, by
        change MemReadable s2 (s2.regValue .rsi + 0#64) 8
        rw [rsi2]
        exact (readable_subrange pre.input 0 8 (by decide)).of_external_eq
          (ag2.external (by simp [Component.Covers]))⟩
      (boundary_ne_program hout (inProgram_of_textOffset 0x182f1 (by decide)))
  change (movR64M64Effect 0x1182ee 14 (.base 6 .none) s2).Holds s2 s3 at e3
  have code3 := e3.codeIn (Effect.Avoids.of_noMem (by simp [Component.Covers]) _) code2
  have rcx3 : s3.regValue .rcx = 32 := (e3.agrees.read (n := 64) (r := 1) (by simp)).trans rcx2
  obtain ⟨s4, run4, ready4, e4⟩ :=
    (add_r64_imm8_effect_step 0x1182f1 0x48 0xc1 0xf8 (by simp [RexWPrefix]) rfl rfl).advances ready3
      (code3.mono (codeRange_slice_subset 0x1182e7 initializeReadBytes 10 4)) e3.rip
      (boundary_ne_program hout (inProgram_of_textOffset 0x182f5 (by decide)))
  change (addR64Imm8Effect 0x1182f1 1 0xf8 s3).Holds s3 s4 at e4
  have code4 := e4.codeIn (Effect.Avoids.of_noMem (by simp [Component.Covers]) _) code3
  have zf4 : (StatusFlags.ofRFLAGS s4.RFLAGS).ZF = false := by
    have h := e4.flags.2.2.2.1
    change _ = ((s3.regValue .rcx + (0xf8#8).signExtend 64) == 0#64) at h
    simpa [rcx3] using h
  have next4 : (jccEffect 0x1182f5 2 4 ((0x28 : BitVec 8).signExtend 64) s4).rip = 0x1182f7 := by
    simp [jccEffect, branchEffect, condHolds, zf4]
  obtain ⟨s5, run5, ready5, e5⟩ := (jcc_rel8_effect_step 0x1182f5 4 0x28).advances ready4
    (code4.mono (codeRange_slice_subset 0x1182e7 initializeReadBytes 14 2))
    ⟨e4.rip, by intro _; decide +kernel⟩
    (by rw [next4]; exact boundary_ne_program hout (inProgram_of_textOffset 0x182f7 (by decide)))
  have code5 := e5.codeIn (Effect.Avoids.of_noMem (by simp [jccEffect, Component.Covers]) _) code4
  have ag5 := ((ag2.trans e3.agrees).trans e4.agrees).trans e5.agrees
  have rdx5 : s5.regValue .rdx = 32 := (ag5.read (n := 64) (r := 2) (by simp [jccEffect])).trans pre.length
  obtain ⟨s6, run6, ready6, e6⟩ :=
    (cmp_r64_imm8_effect_step 0x1182f7 0x48 0xfa 15 (by simp [RexWPrefix]) rfl rfl).advances ready5
      (code5.mono (codeRange_slice_subset 0x1182e7 initializeReadBytes 16 4)) (e5.rip.trans next4)
      (boundary_ne_program hout (inProgram_of_textOffset 0x182fb (by decide)))
  change (cmpR64Imm8Effect 0x1182f7 2 15 s5).Holds s5 s6 at e6
  have code6 := e6.codeIn (Effect.Avoids.of_noMem (by simp [Component.Covers]) _) code5
  have cf6 : (StatusFlags.ofRFLAGS s6.RFLAGS).CF = false := by
    have h := e6.flags.1
    change _ = (s5.regValue .rdx).ult ((15#8).signExtend 64) at h
    simpa [rdx5] using h
  have zf6 : (StatusFlags.ofRFLAGS s6.RFLAGS).ZF = false := by
    have h := e6.flags.2.2.2.1
    change _ = ((s5.regValue .rdx - (15#8).signExtend 64) == 0#64) at h
    simpa [rdx5] using h
  have next6 : (jccEffect 0x1182fb 2 7 ((0x2b : BitVec 8).signExtend 64) s6).rip = 0x118328 := by
    simp [jccEffect, branchEffect, condHolds, cf6, zf6, branchTarget]
  obtain ⟨s7, run7, ready7, e7⟩ := (jcc_rel8_effect_step 0x1182fb 7 0x2b).advances ready6
    (code6.mono (codeRange_slice_subset 0x1182e7 initializeReadBytes 20 2))
    ⟨e6.rip, by intro _; decide +kernel⟩
    (by rw [next6]; exact boundary_ne_program hout (inProgram_of_textOffset 0x18328 (by decide)))
  have code7 := e7.codeIn (Effect.Avoids.of_noMem (by simp [jccEffect, Component.Covers]) _) code6
  obtain ⟨s8, run8, ready8, e8⟩ :=
    (add_r64_imm8_effect_step 0x118328 0x48 0xc2 0xf0 (by simp [RexWPrefix]) rfl rfl).advances ready7
      (code7.mono (codeRange_slice_subset 0x1182e7 initializeReadBytes 65 4)) (e7.rip.trans next6)
      (boundary_ne_program hout (inProgram_of_textOffset 0x1832c (by decide)))
  change (addR64Imm8Effect 0x118328 2 0xf0 s7).Holds s7 s8 at e8
  have code8 := e8.codeIn (Effect.Avoids.of_noMem (by simp [Component.Covers]) _) code7
  have ag8 := ((ag5.trans e6.agrees).trans e7.agrees).trans e8.agrees
  have rsi8 : s8.regValue .rsi = s.regValue .rsi := ag8.read (n := 64) (r := 6) (by simp [jccEffect])
  have mem8 : s8.external = s.external := ag8.external (by simp [jccEffect, Component.Covers])
  obtain ⟨s9, run9, ready9, e9⟩ :=
    (mov_r64_m64_effect_step 0x11832c 0x48 (by simp [RexWPrefix]) 1
      (.base 6 (.d8 8)) (by decide +kernel) rfl rfl).advances ready8
      (code8.mono (codeRange_slice_subset 0x1182e7 initializeReadBytes 69 4))
      ⟨e8.rip, by
        change MemReadable s8 (s8.regValue .rsi + 8) 8
        rw [rsi8]
        exact (readable_subrange pre.input 8 8 (by decide)).of_external_eq mem8⟩
      (boundary_ne_program hout (inProgram_of_textOffset 0x18330 (by decide)))
  change (movR64M64Effect 0x11832c 1 (.base 6 (.d8 8)) s8).Holds s8 s9 at e9
  have code9 := e9.codeIn (Effect.Avoids.of_noMem (by simp [Component.Covers]) _) code8
  obtain ⟨s10, run10, ready10, e10⟩ :=
    (add_r64_imm8_effect_step 0x118330 0x48 0xc6 16 (by simp [RexWPrefix]) rfl rfl).advances ready9
      (code9.mono (codeRange_slice_subset 0x1182e7 initializeReadBytes 73 4)) e9.rip
      (boundary_ne_program hout (inProgram_of_textOffset 0x18334 (by decide)))
  change (addR64Imm8Effect 0x118330 6 16 s9).Holds s9 s10 at e10
  have code10 := e10.codeIn (Effect.Avoids.of_noMem (by simp [Component.Covers]) _) code9
  obtain ⟨s11, run11, ready11, e11⟩ := (jmp_rel8_effect_step 0x118334 0x8f (by decide +kernel)).advances ready10
    (code10.mono (codeRange_slice_subset 0x1182e7 initializeReadBytes 77 2)) e10.rip
    (boundary_ne_program hout (inProgram_of_textOffset 0x182c5 (by decide)))
  have code11 := e11.codeIn (Effect.Avoids.of_noMem (by simp [Component.Covers]) _) code10
  have run := (((((((((run1.trans run2).trans run3).trans run4).trans run5).trans run6).trans run7).trans run8).trans run9).trans run10).trans run11
  refine ⟨11, s11, run, ready11, code11, e11.rip, ?_, ?_, ?_⟩
  · change s11.regValue .rax = s.regValue .rsi + 8 ∧
      s11.regValue .r14 = memLoad s.external (s.regValue .rsi) 64 ∧
      s11.regValue .rcx = memLoad s.external (s.regValue .rsi + 8) 64 ∧
      s11.regValue .rdx = 16 ∧ s11.regValue .rsi = s.regValue .rsi + 16
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · exact ((((((((((e2.agrees.trans e3.agrees).trans e4.agrees).trans e5.agrees).trans e6.agrees).trans e7.agrees).trans e8.agrees).trans e9.agrees).trans e10.agrees).trans e11.agrees).read (n := 64) (r := 0)
        (by simp [jccEffect])).trans e1.writes
    · have h := e3.writes
      change s3.regValue .r14 = memLoad s2.external (s2.regValue .rsi + 0#64) 64 at h
      rw [BitVec.add_zero, rsi2, ag2.external (by simp [Component.Covers])] at h
      exact ((((((((e4.agrees.trans e5.agrees).trans e6.agrees).trans e7.agrees).trans e8.agrees).trans e9.agrees).trans e10.agrees).trans e11.agrees).read (n := 64) (r := 14)
        (by simp [jccEffect])).trans h
    · have h := e9.writes
      change s9.regValue .rcx = memLoad s8.external (s8.regValue .rsi + 8) 64 at h
      rw [rsi8, mem8] at h
      exact ((e10.agrees.trans e11.agrees).read (n := 64) (r := 1) (by simp)).trans h
    · have h := e8.writes
      change s8.regValue .rdx = s7.regValue .rdx + (0xf0#8).signExtend 64 at h
      have h7 : s7.regValue .rdx = 32 :=
        ((e6.agrees.trans e7.agrees).read (n := 64) (r := 2) (by simp [jccEffect])).trans rdx5
      rw [h7] at h
      exact (((e9.agrees.trans e10.agrees).trans e11.agrees).read (n := 64) (r := 2) (by simp)).trans h
    · have h := e10.writes
      change s10.regValue .rsi = s9.regValue .rsi + 16 at h
      have h9 : s9.regValue .rsi = s.regValue .rsi := (e9.agrees.read (n := 64) (r := 6) (by simp)).trans rsi8
      rw [h9] at h
      exact (e11.agrees.read (n := 64) (r := 6) (by simp)).trans h
  · trivial
  · apply (((ag8.trans e9.agrees).trans e10.agrees).trans e11.agrees).mono
    simp [initializeReadEffect, jccEffect, branchEffect, Effect.components, jmpEffect, leaR64Effect, movR64R64Effect,
      movR64M64Effect, addR64Imm8Effect, cmpR64Imm8Effect, Effect.components]

end P256.Proofs.Verifying.Combination.Naf.Iterator
