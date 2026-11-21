import P256.Proofs.Common.Instructions.Setcc
import P256.Proofs.Nonce.Initialize.Conversions.ShiftZero.Select.Masks
import P256.Proofs.Nonce.Initialize.Conversions.Neg32
import P256.Proofs.Common.Instructions.Setb.Memory.Triple
import P256.Proofs.Common.Instructions.Setb.Triple
import P256.Proofs.Nonce.Initialize.Conversions.XorImmediate
import X86Proofs.Instructions.And.Generated.Imm8.Triple
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import X86Proofs.Instructions.Branch.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Conversions.ShiftZero

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Field
open P256.Proofs.SecretKeyFromBytes.Scalar

open P256.Proofs.Common.Instructions P256.Proofs.Common.Instructions.Setb
open P256.Proofs.Nonce.Initialize.Conversions.XorImmediate
open P256.Proofs.Nonce.Initialize.Conversions.Neg32
open P256.Proofs.Common.Instructions.Setcc
open P256.Proofs.Common.Instructions.ByteOps.ByteOps (mergeGPR_low8)

set_option maxHeartbeats 1000000 in
theorem selected_of_masked [Bindings] {s t : RamState} {boundary : ReturnBoundary} {a : Limbs}
    (pre : CalleePre s boundary 0x109530 32 32 128)
    (state : MaskedState s t boundary a) :
    ∃ u, SelectedState s u boundary a := by
  have st0 := state.toStage
  have ready0 := state.ready
  have saved0 := state.outputSaved
  have count0 : (Operand.reg 2 : Operand 64).read t = 0 := state.rdx
  obtain ⟨t1, run1, ready1, e1⟩ :=
    (and_r32_imm8_effect_step 0x1095c0 0xe2 63 rfl rfl).advances ready0
      (programText_slice (programLoaded_codeIn st0.loaded) 0x95c0 _
        (by decide) (by decide +kernel))
      state.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x95c3 (by decide)))
  have f1 : AgreesExcept [.reg 2, .flags, .rip] t t1 := e1.agrees
  have st1 := st0.of_effect pre run1 ready1 e1
    (by change ∀ c ∈ [.reg 2, .flags, .rip], BodyComponent (rspOf t) c
        simp [BodyComponent])
    (by change Component.reg 4 ∉ [.reg 2, .flags, .rip]; simp)
  have mem1 : t1.external = t.external := f1.external (by simp [Component.Covers])
  have saved1 : memLoad t1.external (stackPtr s - 56#64) 64 = s.regValue .rdi := by
    rw [mem1]
    exact saved0
  have v1 : (Operand.reg 2 : Operand 64).read t1 = 0 := by
    have h : (Operand.reg 2 : Operand 64).read t1 =
      (((Operand.reg 2 : Operand 64).read t).setWidth 32 &&& 63).setWidth 64 := e1.writes
    rw [count0] at h
    exact h
  have zf1 : (StatusFlags.ofRFLAGS t1.RFLAGS).ZF = true := by
    have h := e1.flag .ZF
    change (StatusFlags.ofRFLAGS t1.RFLAGS).ZF =
      (((Operand.reg 2 : Operand 64).read t).setWidth 32 &&& 63 == 0) at h
    rw [count0] at h
    exact h
  obtain ⟨t2, run2, ready2, e2⟩ :=
    (setccExtra_m8_effect_step 0x1095c3 0x95 (Or.inr rfl) 0 (.sib 4 none 0 (.d8 14)) (by decide) rfl rfl).advances ready1
      (programText_slice (programLoaded_codeIn st1.loaded) 0x95c3 _
        (by decide) (by decide +kernel))
      ⟨e1.rip, st1.scratch_byte_writable pre (offset := 14) (by decide),
        st1.scratch_code_apart pre (offset := 14) (codeOffset := 0x95c3) (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x95c8 (by decide)))
  have ce2 : (setccM8Effect 0x1095c3 5 (.sib 4 none 0 (.d8 14)) 5 t1).components =
      [.mem (rspOf t1 + 14#64) 1, .rip] := by
    simp [setccM8Effect_components, storeAddrAt, AddrMode.addr, AddrMode.reg64,
      Disp.value, rspOf, Operand.read]
  have f2 : AgreesExcept [.mem (rspOf t1 + 14#64) 1, .rip] t1 t2 := by
    have h := e2.agrees
    change AgreesExcept (setccM8Effect 0x1095c3 5 (.sib 4 none 0 (.d8 14)) 5 t1).components t1 t2 at h
    rw [ce2] at h
    exact h
  have st2 := st1.of_effect pre run2 ready2 e2
    (by change ∀ c ∈ (setccM8Effect 0x1095c3 5 (.sib 4 none 0 (.d8 14)) 5 t1).components, BodyComponent (rspOf t1) c
        rw [ce2]
        intro c hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl
        · exact ⟨14, rfl, by decide⟩
        · trivial)
    (by simp [setccM8Effect_components])
  have saved2 := (Store.byte_store_saved_pointer st1 (by decide) f2).trans saved1
  have choice1 : setccValue 5 t1 = 0 := by
    change (if !(StatusFlags.ofRFLAGS t1.RFLAGS).ZF then (1 : BitVec 8) else 0) = 0
    rw [zf1]
    rfl
  have zero2 : memLoad t2.external (stackPtr s - 58#64) 8 = 0 := by
    have h : memLoad t2.external (rspOf t1 + 14#64) 8 = setccValue 5 t1 := e2.writes
    rw [st1.scratch_address (offset := 14) (by decide), choice1] at h
    exact h
  have zf2 : (StatusFlags.ofRFLAGS t2.RFLAGS).ZF = true := by
    have h := e2.flag .ZF
    change (StatusFlags.ofRFLAGS t2.RFLAGS).ZF = (StatusFlags.ofRFLAGS t1.RFLAGS).ZF at h
    exact h.trans zf1
  obtain ⟨t3, run3, ready3, e3⟩ :=
    (setccExtra_r8_rex_effect_step 0x1095c8 0x40 0x95 0xc7 (by simp [RexPrefix]) (Or.inr rfl) rfl).advances ready2
      (programText_slice (programLoaded_codeIn st2.loaded) 0x95c8 _
        (by decide) (by decide +kernel))
      e2.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x95cc (by decide)))
  have f3 : AgreesExcept [.reg 7, .rip] t2 t3 := e3.agrees
  have st3 := st2.of_effect pre run3 ready3 e3
    (by change ∀ c ∈ [.reg 7, .rip], BodyComponent (rspOf t2) c
        simp [BodyComponent])
    (by change Component.reg 4 ∉ [.reg 7, .rip]; simp)
  have mem3 : t3.external = t2.external := f3.external (by simp [Component.Covers])
  have saved3 : memLoad t3.external (stackPtr s - 56#64) 64 = s.regValue .rdi := by
    rw [mem3]
    exact saved2
  have choice2 : setccValue 5 t2 = 0 := by
    change (if !(StatusFlags.ofRFLAGS t2.RFLAGS).ZF then (1 : BitVec 8) else 0) = 0
    rw [zf2]
    rfl
  have dil3 : (Operand.reg 7 : Operand 8).read t3 = 0 := by
    have h := congrArg (fun x : BitVec 64 => x.setWidth 8) e3.writes
    change ((Operand.reg 7 : Operand 64).read t3).setWidth 8 =
      (mergeGPR 8 (setccValue 5 t2) t2.GPR[gprIndex 7]).setWidth 8 at h
    rw [mergeGPR_low8, choice2] at h
    exact h
  obtain ⟨t4, run4, ready4, e4⟩ :=
    (lea_r64_effect_step 0x1095cc 0x48 (by simp [RexWPrefix]) 1 (.sib 4 none 0 (.d8 14)) (by decide) rfl rfl).advances ready3
      (programText_slice (programLoaded_codeIn st3.loaded) 0x95cc _
        (by decide) (by decide +kernel))
      e3.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x95d1 (by decide)))
  have f4 : AgreesExcept [.reg 1, .rip] t3 t4 := e4.agrees
  have st4 := st3.of_effect pre run4 ready4 e4
    (by change ∀ c ∈ [.reg 1, .rip], BodyComponent (rspOf t3) c
        simp [BodyComponent])
    (by change Component.reg 4 ∉ [.reg 1, .rip]; simp)
  have mem4 : t4.external = t3.external := f4.external (by simp [Component.Covers])
  have saved4 : memLoad t4.external (stackPtr s - 56#64) 64 = s.regValue .rdi := by
    rw [mem4]
    exact saved3
  obtain ⟨t5, run5, ready5, e5⟩ :=
    (movzx_r32_m8_effect_step 0x1095d1 1 (.sib 4 none 0 (.d8 14)) (by decide) rfl rfl).advances ready4
      (programText_slice (programLoaded_codeIn st4.loaded) 0x95d1 _
        (by decide) (by decide +kernel))
      ⟨e4.rip, st4.scratch_readable pre (offset := 14) (len := 1) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x95d6 (by decide)))
  have f5 : AgreesExcept [.reg 1, .rip] t4 t5 := e5.agrees
  have st5 := st4.of_effect pre run5 ready5 e5
    (by change ∀ c ∈ [.reg 1, .rip], BodyComponent (rspOf t4) c
        simp [BodyComponent])
    (by change Component.reg 4 ∉ [.reg 1, .rip]; simp)
  have mem5 : t5.external = t4.external := f5.external (by simp [Component.Covers])
  have saved5 : memLoad t5.external (stackPtr s - 56#64) 64 = s.regValue .rdi := by
    rw [mem5]
    exact saved4
  have v5 : (Operand.reg 1 : Operand 64).read t5 = 0 := by
    have h : (Operand.reg 1 : Operand 64).read t5 =
      (memLoad t4.external (rspOf t4 + 14#64) 8).setWidth 64 := e5.writes
    rw [st4.scratch_address (offset := 14) (by decide), mem4, mem3, zero2] at h
    exact h
  obtain ⟨t6, run6, ready6, e6⟩ :=
    (neg_r32_effect_step 0x1095d6 0xd9 rfl rfl).advances ready5
      (programText_slice (programLoaded_codeIn st5.loaded) 0x95d6 _
        (by decide) (by decide +kernel))
      e5.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x95d8 (by decide)))
  have f6 : AgreesExcept [.reg 1, .flags, .rip] t5 t6 := e6.agrees
  have st6 := st5.of_effect pre run6 ready6 e6
    (by change ∀ c ∈ [.reg 1, .flags, .rip], BodyComponent (rspOf t5) c
        simp [BodyComponent])
    (by change Component.reg 4 ∉ [.reg 1, .flags, .rip]; simp)
  have mem6 : t6.external = t5.external := f6.external (by simp [Component.Covers])
  have saved6 : memLoad t6.external (stackPtr s - 56#64) 64 = s.regValue .rdi := by
    rw [mem6]
    exact saved5
  have v6 : (Operand.reg 1 : Operand 64).read t6 = 0 := by
    have h : (Operand.reg 1 : Operand 64).read t6 =
      (-((Operand.reg 1 : Operand 64).read t5).setWidth 32).setWidth 64 := e6.writes
    rw [v5] at h
    exact h
  obtain ⟨t7, run7, ready7, e7⟩ :=
    (xor_r32_imm8_effect_step 0x1095d8 0xf2 1 rfl rfl).advances ready6
      (programText_slice (programLoaded_codeIn st6.loaded) 0x95d8 _
        (by decide) (by decide +kernel))
      e6.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x95db (by decide)))
  have f7 : AgreesExcept [.reg 2, .flags, .rip] t6 t7 := e7.agrees
  have st7 := st6.of_effect pre run7 ready7 e7
    (by change ∀ c ∈ [.reg 2, .flags, .rip], BodyComponent (rspOf t6) c
        simp [BodyComponent])
    (by change Component.reg 4 ∉ [.reg 2, .flags, .rip]; simp)
  have mem7 : t7.external = t6.external := f7.external (by simp [Component.Covers])
  have saved7 : memLoad t7.external (stackPtr s - 56#64) 64 = s.regValue .rdi := by
    rw [mem7]
    exact saved6
  have count6 : (Operand.reg 2 : Operand 64).read t6 = 0 := by
    rw [f6.read (by simp), f5.read (by simp), f4.read (by simp), f3.read (by simp), f2.read (by simp)]
    exact v1
  have v7 : (Operand.reg 2 : Operand 64).read t7 = 1 := by
    have h : (Operand.reg 2 : Operand 64).read t7 =
      (((Operand.reg 2 : Operand 64).read t6).setWidth 32 ^^^ 1).setWidth 64 := e7.writes
    rw [count6] at h
    exact h
  obtain ⟨t8, run8, ready8, e8⟩ :=
    (and_r32_r32_effect_step 0x1095db 0xca rfl).advances ready7
      (programText_slice (programLoaded_codeIn st7.loaded) 0x95db _
        (by decide) (by decide +kernel))
      e7.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x95dd (by decide)))
  have f8 : AgreesExcept [.reg 2, .flags, .rip] t7 t8 := e8.agrees
  have st8 := st7.of_effect pre run8 ready8 e8
    (by change ∀ c ∈ [.reg 2, .flags, .rip], BodyComponent (rspOf t7) c
        simp [BodyComponent])
    (by change Component.reg 4 ∉ [.reg 2, .flags, .rip]; simp)
  have mem8 : t8.external = t7.external := f8.external (by simp [Component.Covers])
  have saved8 : memLoad t8.external (stackPtr s - 56#64) 64 = s.regValue .rdi := by
    rw [mem8]
    exact saved7
  have count7 : (Operand.reg 1 : Operand 64).read t7 = 0 := by
    rw [f7.read (by simp)]
    exact v6
  have v8 : (Operand.reg 2 : Operand 64).read t8 = 0 := by
    have h : (Operand.reg 2 : Operand 64).read t8 =
      (((Operand.reg 2 : Operand 64).read t7).setWidth 32 &&&
        ((Operand.reg 1 : Operand 64).read t7).setWidth 32).setWidth 64 := e8.writes
    rw [v7, count7] at h
    exact h
  obtain ⟨t9, run9, ready9, e9⟩ :=
    (cmp_r32_imm8_effect_step 0x1095dd 0xfa 1 rfl rfl).advances ready8
      (programText_slice (programLoaded_codeIn st8.loaded) 0x95dd _
        (by decide) (by decide +kernel))
      e8.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x95e0 (by decide)))
  have f9 : AgreesExcept [.flags, .rip] t8 t9 := e9.agrees
  have st9 := st8.of_effect pre run9 ready9 e9
    (by change ∀ c ∈ [.flags, .rip], BodyComponent (rspOf t8) c
        simp [BodyComponent])
    (by change Component.reg 4 ∉ [.flags, .rip]; simp)
  have mem9 : t9.external = t8.external := f9.external (by simp [Component.Covers])
  have saved9 : memLoad t9.external (stackPtr s - 56#64) 64 = s.regValue .rdi := by
    rw [mem9]
    exact saved8
  have zf9 : (StatusFlags.ofRFLAGS t9.RFLAGS).ZF = false := by
    have h := e9.flag .ZF
    change (StatusFlags.ofRFLAGS t9.RFLAGS).ZF =
      ((((Operand.reg 2 : Operand 64).read t8).setWidth 32 - 1) == 0) at h
    rw [v8] at h
    exact h
  have next : (jccEffect 0x1095e0 6 4 ((0x115 : BitVec 32).signExtend 64) t9).rip = 0x1095e6 := by
    change (if (StatusFlags.ofRFLAGS t9.RFLAGS).ZF then (0x1096fb : BitVec 64) else 0x1095e6) = _
    rw [zf9]
    rfl
  obtain ⟨t10, run10, ready10, e10⟩ :=
    (jcc_rel32_effect_step 0x1095e0 4 0x115).advances ready9
      (programText_slice (programLoaded_codeIn st9.loaded) 0x95e0 _
        (by decide) (by decide +kernel))
      ⟨e9.rip, fun _ => by decide⟩
      (by
        rw [next]
        exact boundary_ne_program pre.outerBoundary
          (inProgram_of_textOffset 0x95e6 (by decide)))
  have f10 : AgreesExcept [.rip] t9 t10 := e10.agrees
  have st10 := st9.of_effect pre run10 ready10 e10
    (by intro c hc; change c ∈ [.rip] at hc; simp only [List.mem_singleton] at hc; subst c; trivial)
    (by change Component.reg 4 ∉ [.rip]; simp)
  have mem10 : t10.external = t9.external := f10.external (by simp [Component.Covers])
  refine ⟨t10, st10, e10.rip.trans next, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [mem10]
    exact saved9
  · change (Operand.reg 7 : Operand 8).read t10 = _
    rw [f10.read (r := 7) (n := 8) (by simp), f9.read (r := 7) (n := 8) (by simp), f8.read (r := 7) (n := 8) (by simp), f7.read (r := 7) (n := 8) (by simp), f6.read (r := 7) (n := 8) (by simp), f5.read (r := 7) (n := 8) (by simp), f4.read (r := 7) (n := 8) (by simp)]
    exact dil3
  · change (Operand.reg 2 : Operand 64).read t10 = _
    rw [f10.read (by simp), f9.read (by simp)]
    exact v8
  · change (Operand.reg 13 : Operand 64).read t10 = _
    rw [f10.read (r := 13) (n := 64) (by simp), f9.read (r := 13) (n := 64) (by simp), f8.read (r := 13) (n := 64) (by simp), f7.read (r := 13) (n := 64) (by simp), f6.read (r := 13) (n := 64) (by simp), f5.read (r := 13) (n := 64) (by simp), f4.read (r := 13) (n := 64) (by simp), f3.read (r := 13) (n := 64) (by simp), f2.read (r := 13) (n := 64) (by simp), f1.read (r := 13) (n := 64) (by simp)]
    exact state.r13
  · change (Operand.reg 15 : Operand 64).read t10 = _
    rw [f10.read (r := 15) (n := 64) (by simp), f9.read (r := 15) (n := 64) (by simp), f8.read (r := 15) (n := 64) (by simp), f7.read (r := 15) (n := 64) (by simp), f6.read (r := 15) (n := 64) (by simp), f5.read (r := 15) (n := 64) (by simp), f4.read (r := 15) (n := 64) (by simp), f3.read (r := 15) (n := 64) (by simp), f2.read (r := 15) (n := 64) (by simp), f1.read (r := 15) (n := 64) (by simp)]
    exact state.r15
  · change (Operand.reg 10 : Operand 64).read t10 = _
    rw [f10.read (r := 10) (n := 64) (by simp), f9.read (r := 10) (n := 64) (by simp), f8.read (r := 10) (n := 64) (by simp), f7.read (r := 10) (n := 64) (by simp), f6.read (r := 10) (n := 64) (by simp), f5.read (r := 10) (n := 64) (by simp), f4.read (r := 10) (n := 64) (by simp), f3.read (r := 10) (n := 64) (by simp), f2.read (r := 10) (n := 64) (by simp), f1.read (r := 10) (n := 64) (by simp)]
    exact state.r10
  · change (Operand.reg 14 : Operand 64).read t10 = _
    rw [f10.read (r := 14) (n := 64) (by simp), f9.read (r := 14) (n := 64) (by simp), f8.read (r := 14) (n := 64) (by simp), f7.read (r := 14) (n := 64) (by simp), f6.read (r := 14) (n := 64) (by simp), f5.read (r := 14) (n := 64) (by simp), f4.read (r := 14) (n := 64) (by simp), f3.read (r := 14) (n := 64) (by simp), f2.read (r := 14) (n := 64) (by simp), f1.read (r := 14) (n := 64) (by simp)]
    exact state.r14
  · change (Operand.reg 9 : Operand 64).read t10 = _
    rw [f10.read (r := 9) (n := 64) (by simp), f9.read (r := 9) (n := 64) (by simp), f8.read (r := 9) (n := 64) (by simp), f7.read (r := 9) (n := 64) (by simp), f6.read (r := 9) (n := 64) (by simp), f5.read (r := 9) (n := 64) (by simp), f4.read (r := 9) (n := 64) (by simp), f3.read (r := 9) (n := 64) (by simp), f2.read (r := 9) (n := 64) (by simp), f1.read (r := 9) (n := 64) (by simp)]
    exact state.r9
  · change (Operand.reg 12 : Operand 64).read t10 = _
    rw [f10.read (r := 12) (n := 64) (by simp), f9.read (r := 12) (n := 64) (by simp), f8.read (r := 12) (n := 64) (by simp), f7.read (r := 12) (n := 64) (by simp), f6.read (r := 12) (n := 64) (by simp), f5.read (r := 12) (n := 64) (by simp), f4.read (r := 12) (n := 64) (by simp), f3.read (r := 12) (n := 64) (by simp), f2.read (r := 12) (n := 64) (by simp), f1.read (r := 12) (n := 64) (by simp)]
    exact state.r12
  · change (Operand.reg 11 : Operand 64).read t10 = _
    rw [f10.read (r := 11) (n := 64) (by simp), f9.read (r := 11) (n := 64) (by simp), f8.read (r := 11) (n := 64) (by simp), f7.read (r := 11) (n := 64) (by simp), f6.read (r := 11) (n := 64) (by simp), f5.read (r := 11) (n := 64) (by simp), f4.read (r := 11) (n := 64) (by simp), f3.read (r := 11) (n := 64) (by simp), f2.read (r := 11) (n := 64) (by simp), f1.read (r := 11) (n := 64) (by simp)]
    exact state.r11
  · change (Operand.reg 5 : Operand 64).read t10 = _
    rw [f10.read (r := 5) (n := 64) (by simp), f9.read (r := 5) (n := 64) (by simp), f8.read (r := 5) (n := 64) (by simp), f7.read (r := 5) (n := 64) (by simp), f6.read (r := 5) (n := 64) (by simp), f5.read (r := 5) (n := 64) (by simp), f4.read (r := 5) (n := 64) (by simp), f3.read (r := 5) (n := 64) (by simp), f2.read (r := 5) (n := 64) (by simp), f1.read (r := 5) (n := 64) (by simp)]
    exact state.rbp
  · change (Operand.reg 0 : Operand 64).read t10 = _
    rw [f10.read (r := 0) (n := 64) (by simp), f9.read (r := 0) (n := 64) (by simp), f8.read (r := 0) (n := 64) (by simp), f7.read (r := 0) (n := 64) (by simp), f6.read (r := 0) (n := 64) (by simp), f5.read (r := 0) (n := 64) (by simp), f4.read (r := 0) (n := 64) (by simp), f3.read (r := 0) (n := 64) (by simp), f2.read (r := 0) (n := 64) (by simp), f1.read (r := 0) (n := 64) (by simp)]
    exact state.rax
  · change (Operand.reg 6 : Operand 64).read t10 = _
    rw [f10.read (r := 6) (n := 64) (by simp), f9.read (r := 6) (n := 64) (by simp), f8.read (r := 6) (n := 64) (by simp), f7.read (r := 6) (n := 64) (by simp), f6.read (r := 6) (n := 64) (by simp), f5.read (r := 6) (n := 64) (by simp), f4.read (r := 6) (n := 64) (by simp), f3.read (r := 6) (n := 64) (by simp), f2.read (r := 6) (n := 64) (by simp), f1.read (r := 6) (n := 64) (by simp)]
    exact state.rsi
  · change (Operand.reg 8 : Operand 64).read t10 = _
    rw [f10.read (r := 8) (n := 64) (by simp), f9.read (r := 8) (n := 64) (by simp), f8.read (r := 8) (n := 64) (by simp), f7.read (r := 8) (n := 64) (by simp), f6.read (r := 8) (n := 64) (by simp), f5.read (r := 8) (n := 64) (by simp), f4.read (r := 8) (n := 64) (by simp), f3.read (r := 8) (n := 64) (by simp), f2.read (r := 8) (n := 64) (by simp), f1.read (r := 8) (n := 64) (by simp)]
    exact state.r8
  · change (Operand.reg 3 : Operand 64).read t10 = _
    rw [f10.read (r := 3) (n := 64) (by simp), f9.read (r := 3) (n := 64) (by simp), f8.read (r := 3) (n := 64) (by simp), f7.read (r := 3) (n := 64) (by simp), f6.read (r := 3) (n := 64) (by simp), f5.read (r := 3) (n := 64) (by simp), f4.read (r := 3) (n := 64) (by simp), f3.read (r := 3) (n := 64) (by simp), f2.read (r := 3) (n := 64) (by simp), f1.read (r := 3) (n := 64) (by simp)]
    exact state.rbx

end P256.Proofs.Nonce.Initialize.Conversions.ShiftZero
