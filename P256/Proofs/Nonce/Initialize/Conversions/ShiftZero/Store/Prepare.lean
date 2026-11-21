import P256.Proofs.Nonce.Initialize.Conversions.ShiftZero.Store.Memory
import P256.Proofs.Nonce.Initialize.Conversions.ShiftZero.Instructions.Shrd
import P256.Proofs.Common.Encoding.Parser.ByteStore
import P256.Proofs.Common.Instructions.Neg64
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
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Conversions.ShiftZero.Store

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Field
open P256.Proofs.SecretKeyFromBytes.Scalar

open P256.Proofs.Common.Instructions (mov_m8_r8_effect_step)
open P256.Proofs.Common.Instructions.Neg64
open P256.Proofs.Nonce.Initialize.Conversions.ShiftZero.Instructions.Shrd

set_option maxHeartbeats 1600000 in
theorem prepare_output [Bindings] {s t : RamState} {boundary : ReturnBoundary} {a : Limbs}
    (pre : CalleePre s boundary 0x109530 32 32 128)
    (state : MixedState s t boundary a) :
    ∃ u, OutputState s u boundary a := by
  have st0 := state.toStage
  have ready0 := state.ready
  have saved0 := state.outputSaved
  have h0r7 : (Operand.reg 7 : Operand 8).read t = 0 := by
    exact state.dil
  obtain ⟨t1, run1, ready1, e1⟩ :=
    (mov_m8_r8_effect_step 0x10963f 0x40 (by simp [RexPrefix]) 7 (.sib 4 none 0 (.d8 12)) (by decide) rfl rfl).advances ready0
      (programText_slice (programLoaded_codeIn st0.loaded) 0x963f _
        (by decide) (by decide +kernel))
      ⟨state.rip, st0.scratch_byte_writable pre (offset := 12) (by decide),
        st0.scratch_code_apart pre (offset := 12) (codeOffset := 0x963f)
          (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x9644 (by decide)))
  have ce1 : (storeEffect 0x10963f (3 + ((.sib 4 none 0 (.d8 12)) : AddrMode).tail.length)
      (storeAddrAt 0x10963f (.sib 4 none 0 (.d8 12)) (3 + ((.sib 4 none 0 (.d8 12)) : AddrMode).tail.length))
      (fun t => (Operand.reg (gprNumber 0 (rexR (0x40 : UInt8).toBitVec) 7) : Operand 8).read t)
      t).components = [.mem (rspOf t + 12#64) 1, .rip] := by
    simp [storeEffect_components, storeAddrAt, AddrMode.addr, AddrMode.reg64,
      Disp.value, rspOf, Operand.read]
  have f1 : AgreesExcept [.mem (rspOf t + 12#64) 1, .rip] t t1 := by
    have h := e1.agrees
    rw [ce1] at h
    exact h
  have st1 := st0.of_effect pre run1 ready1 e1
    (by rw [ce1]; change ∀ c ∈ [.mem (rspOf t + 12#64) 1, .rip], BodyComponent (rspOf t) c
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        intro c hc; rcases hc with rfl | rfl
        · exact ⟨12, rfl, by decide⟩
        · trivial)
    (by rw [ce1]; change Component.reg 4 ∉ [.mem (rspOf t + 12#64) 1, .rip]; simp)
  have saved1 := (byte_store_saved_pointer st0 (by decide) f1).trans saved0
  have zero1 : memLoad t1.external (stackPtr s - 60#64) 8 = 0 := by
    have h : memLoad t1.external (rspOf t + 12#64) 8 = (Operand.reg 7 : Operand 8).read t := e1.writes
    rw [st0.scratch_address (offset := 12) (by decide), h0r7] at h
    exact h
  obtain ⟨t2, run2, ready2, e2⟩ :=
    (lea_r64_effect_step 0x109644 0x4c (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d8 12)) (by decide) rfl rfl).advances ready1
      (programText_slice (programLoaded_codeIn st1.loaded) 0x9644 _
        (by decide) (by decide +kernel))
      e1.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x9649 (by decide)))
  have f2 : AgreesExcept [.reg 11, .rip] t1 t2 := e2.agrees
  have st2 := st1.of_effect pre run2 ready2 e2
    (by change ∀ c ∈ [.reg 11, .rip], BodyComponent (rspOf t1) c
        simp [BodyComponent])
    (by change Component.reg 4 ∉ [.reg 11, .rip]; simp)
  have mem2 : t2.external = t1.external := f2.external (by simp [Component.Covers])
  have saved2 : memLoad t2.external (stackPtr s - 56#64) 64 = s.regValue .rdi := by
    rw [mem2]; exact saved1
  have zero2 : memLoad t2.external (stackPtr s - 60#64) 8 = 0 := by
    rw [mem2]; exact zero1
  obtain ⟨t3, run3, ready3, e3⟩ :=
    (movzx_r32_m8_effect_step 0x109649 1 (.sib 4 none 0 (.d8 12)) (by decide) rfl rfl).advances ready2
      (programText_slice (programLoaded_codeIn st2.loaded) 0x9649 _
        (by decide) (by decide +kernel))
      ⟨e2.rip, st2.scratch_readable pre (offset := 12) (len := 1) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x964e (by decide)))
  have f3 : AgreesExcept [.reg 1, .rip] t2 t3 := e3.agrees
  have st3 := st2.of_effect pre run3 ready3 e3
    (by change ∀ c ∈ [.reg 1, .rip], BodyComponent (rspOf t2) c
        simp [BodyComponent])
    (by change Component.reg 4 ∉ [.reg 1, .rip]; simp)
  have mem3 : t3.external = t2.external := f3.external (by simp [Component.Covers])
  have saved3 : memLoad t3.external (stackPtr s - 56#64) 64 = s.regValue .rdi := by
    rw [mem3]; exact saved2
  have zero3 : memLoad t3.external (stackPtr s - 60#64) 8 = 0 := by
    rw [mem3]; exact zero2
  have v3 : (Operand.reg 1 : Operand 64).read t3 = 0 := by
    have h : (Operand.reg 1 : Operand 64).read t3 =
      (memLoad t2.external (rspOf t2 + 12#64) 8).setWidth 64 := e3.writes
    rw [show rspOf t2 + 12#64 = stackPtr s - 60#64 from st2.scratch_address (offset := 12) (by decide)] at h
    rw [zero2] at h
    exact h
  have h3r1 : (Operand.reg 1 : Operand 64).read t3 = 0 := by
    exact v3
  obtain ⟨t4, run4, ready4, e4⟩ :=
    (neg_r64_effect_step 0x10964e 0x48 0xd9 (by simp [RexWPrefix]) rfl rfl).advances ready3
      (programText_slice (programLoaded_codeIn st3.loaded) 0x964e _
        (by decide) (by decide +kernel))
      e3.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x9651 (by decide)))
  have f4 : AgreesExcept [.reg 1, .flags, .rip] t3 t4 := e4.agrees
  have st4 := st3.of_effect pre run4 ready4 e4
    (by change ∀ c ∈ [.reg 1, .flags, .rip], BodyComponent (rspOf t3) c
        simp [BodyComponent])
    (by change Component.reg 4 ∉ [.reg 1, .flags, .rip]; simp)
  have mem4 : t4.external = t3.external := f4.external (by simp [Component.Covers])
  have saved4 : memLoad t4.external (stackPtr s - 56#64) 64 = s.regValue .rdi := by
    rw [mem4]; exact saved3
  have zero4 : memLoad t4.external (stackPtr s - 60#64) 8 = 0 := by
    rw [mem4]; exact zero3
  have v4 : (Operand.reg 1 : Operand 64).read t4 = 0 := by
    have h : (Operand.reg 1 : Operand 64).read t4 = -(Operand.reg 1 : Operand 64).read t3 := e4.writes
    rw [h3r1] at h
    exact h
  obtain ⟨t5, run5, ready5, e5⟩ :=
    (xor_r64_r64_effect_step 0x109651 0x49 0xda (by simp [RexWPrefix]) rfl).advances ready4
      (programText_slice (programLoaded_codeIn st4.loaded) 0x9651 _
        (by decide) (by decide +kernel))
      e4.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x9654 (by decide)))
  have f5 : AgreesExcept [.reg 10, .flags, .rip] t4 t5 := e5.agrees
  have st5 := st4.of_effect pre run5 ready5 e5
    (by change ∀ c ∈ [.reg 10, .flags, .rip], BodyComponent (rspOf t4) c
        simp [BodyComponent])
    (by change Component.reg 4 ∉ [.reg 10, .flags, .rip]; simp)
  have mem5 : t5.external = t4.external := f5.external (by simp [Component.Covers])
  have saved5 : memLoad t5.external (stackPtr s - 56#64) 64 = s.regValue .rdi := by
    rw [mem5]; exact saved4
  have zero5 : memLoad t5.external (stackPtr s - 60#64) 8 = 0 := by
    rw [mem5]; exact zero4
  have h5r1 : (Operand.reg 1 : Operand 64).read t5 = 0 := by
    rw [f5.read (r := 1) (n := 64) (by simp)]
    exact v4
  obtain ⟨t6, run6, ready6, e6⟩ :=
    (and_r64_r64_effect_step 0x109654 0x49 0xca (by simp [RexWPrefix]) rfl).advances ready5
      (programText_slice (programLoaded_codeIn st5.loaded) 0x9654 _
        (by decide) (by decide +kernel))
      e5.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x9657 (by decide)))
  have f6 : AgreesExcept [.reg 10, .flags, .rip] t5 t6 := e6.agrees
  have st6 := st5.of_effect pre run6 ready6 e6
    (by change ∀ c ∈ [.reg 10, .flags, .rip], BodyComponent (rspOf t5) c
        simp [BodyComponent])
    (by change Component.reg 4 ∉ [.reg 10, .flags, .rip]; simp)
  have mem6 : t6.external = t5.external := f6.external (by simp [Component.Covers])
  have saved6 : memLoad t6.external (stackPtr s - 56#64) 64 = s.regValue .rdi := by
    rw [mem6]; exact saved5
  have zero6 : memLoad t6.external (stackPtr s - 60#64) 8 = 0 := by
    rw [mem6]; exact zero5
  have v6 : (Operand.reg 10 : Operand 64).read t6 = 0 := by
    have h : (Operand.reg 10 : Operand 64).read t6 =
      (Operand.reg 10 : Operand 64).read t5 &&& (Operand.reg 1 : Operand 64).read t5 := e6.writes
    rw [h5r1] at h
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.and_zero] using h
  have h6r10 : (Operand.reg 10 : Operand 64).read t6 = 0 := by
    exact v6
  have h6r3 : (Operand.reg 3 : Operand 64).read t6 = a.l3 := by
    rw [f6.read (r := 3) (n := 64) (by simp), f5.read (r := 3) (n := 64) (by simp), f4.read (r := 3) (n := 64) (by simp), f3.read (r := 3) (n := 64) (by simp), f2.read (r := 3) (n := 64) (by simp), f1.read (r := 3) (n := 64) (by simp)]
    exact state.rbx
  obtain ⟨t7, run7, ready7, e7⟩ :=
    (xor_r64_r64_effect_step 0x109657 0x49 0xda (by simp [RexWPrefix]) rfl).advances ready6
      (programText_slice (programLoaded_codeIn st6.loaded) 0x9657 _
        (by decide) (by decide +kernel))
      e6.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x965a (by decide)))
  have f7 : AgreesExcept [.reg 10, .flags, .rip] t6 t7 := e7.agrees
  have st7 := st6.of_effect pre run7 ready7 e7
    (by change ∀ c ∈ [.reg 10, .flags, .rip], BodyComponent (rspOf t6) c
        simp [BodyComponent])
    (by change Component.reg 4 ∉ [.reg 10, .flags, .rip]; simp)
  have mem7 : t7.external = t6.external := f7.external (by simp [Component.Covers])
  have saved7 : memLoad t7.external (stackPtr s - 56#64) 64 = s.regValue .rdi := by
    rw [mem7]; exact saved6
  have zero7 : memLoad t7.external (stackPtr s - 60#64) 8 = 0 := by
    rw [mem7]; exact zero6
  have v7 : (Operand.reg 10 : Operand 64).read t7 = a.l3 := by
    have h : (Operand.reg 10 : Operand 64).read t7 =
      (Operand.reg 10 : Operand 64).read t6 ^^^ (Operand.reg 3 : Operand 64).read t6 := e7.writes
    rw [h6r10, h6r3] at h
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.zero_xor] using h
  have h7r8 : (Operand.reg 8 : Operand 64).read t7 = a.l2 := by
    rw [f7.read (r := 8) (n := 64) (by simp), f6.read (r := 8) (n := 64) (by simp), f5.read (r := 8) (n := 64) (by simp), f4.read (r := 8) (n := 64) (by simp), f3.read (r := 8) (n := 64) (by simp), f2.read (r := 8) (n := 64) (by simp), f1.read (r := 8) (n := 64) (by simp)]
    exact state.r8
  obtain ⟨t8, run8, ready8, e8⟩ :=
    (mov_r64_r64_effect_step 0x10965a 0x4d 0xc1 (by simp [RexWPrefix]) rfl).advances ready7
      (programText_slice (programLoaded_codeIn st7.loaded) 0x965a _
        (by decide) (by decide +kernel))
      e7.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x965d (by decide)))
  have f8 : AgreesExcept [.reg 9, .rip] t7 t8 := e8.agrees
  have st8 := st7.of_effect pre run8 ready8 e8
    (by change ∀ c ∈ [.reg 9, .rip], BodyComponent (rspOf t7) c
        simp [BodyComponent])
    (by change Component.reg 4 ∉ [.reg 9, .rip]; simp)
  have mem8 : t8.external = t7.external := f8.external (by simp [Component.Covers])
  have saved8 : memLoad t8.external (stackPtr s - 56#64) 64 = s.regValue .rdi := by
    rw [mem8]; exact saved7
  have zero8 : memLoad t8.external (stackPtr s - 60#64) 8 = 0 := by
    rw [mem8]; exact zero7
  have v8 : (Operand.reg 9 : Operand 64).read t8 = a.l2 := by
    have h : (Operand.reg 9 : Operand 64).read t8 = (Operand.reg 8 : Operand 64).read t7 := e8.writes
    rw [h7r8] at h
    exact h
  have h8r2 : (Operand.reg 2 : Operand 64).read t8 = 1 := by
    rw [f8.read (r := 2) (n := 64) (by simp), f7.read (r := 2) (n := 64) (by simp), f6.read (r := 2) (n := 64) (by simp), f5.read (r := 2) (n := 64) (by simp), f4.read (r := 2) (n := 64) (by simp), f3.read (r := 2) (n := 64) (by simp), f2.read (r := 2) (n := 64) (by simp), f1.read (r := 2) (n := 64) (by simp)]
    exact state.rdx
  obtain ⟨t9, run9, ready9, e9⟩ :=
    (mov_r32_r32_effect_step 0x10965d 0xd1 rfl).advances ready8
      (programText_slice (programLoaded_codeIn st8.loaded) 0x965d _
        (by decide) (by decide +kernel))
      e8.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x965f (by decide)))
  have f9 : AgreesExcept [.reg 1, .rip] t8 t9 := e9.agrees
  have st9 := st8.of_effect pre run9 ready9 e9
    (by change ∀ c ∈ [.reg 1, .rip], BodyComponent (rspOf t8) c
        simp [BodyComponent])
    (by change Component.reg 4 ∉ [.reg 1, .rip]; simp)
  have mem9 : t9.external = t8.external := f9.external (by simp [Component.Covers])
  have saved9 : memLoad t9.external (stackPtr s - 56#64) 64 = s.regValue .rdi := by
    rw [mem9]; exact saved8
  have zero9 : memLoad t9.external (stackPtr s - 60#64) 8 = 0 := by
    rw [mem9]; exact zero8
  have v9 : (Operand.reg 1 : Operand 64).read t9 = 1 := by
    have h : (Operand.reg 1 : Operand 64).read t9 = (((Operand.reg 2 : Operand 64).read t8).setWidth 32).setWidth 64 := e9.writes
    rw [h8r2] at h
    exact h
  have h9r1 : (Operand.reg 1 : Operand 64).read t9 = 1 := by
    exact v9
  obtain ⟨t10, run10, ready10, e10⟩ :=
    (shrd_r64_r64_cl_one_effect_step 0x10965f 0x49 0xd9 (by simp [RexWPrefix]) rfl).advances ready9
      (programText_slice (programLoaded_codeIn st9.loaded) 0x965f _
        (by decide) (by decide +kernel))
      ⟨e9.rip, by change ((Operand.reg 1 : Operand 64).read t9).setWidth 8 = 1; rw [h9r1]; rfl⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x9663 (by decide)))
  have f10 : AgreesExcept [.reg 9, .flags, .rip] t9 t10 := e10.agrees
  have st10 := st9.of_effect pre run10 ready10 e10
    (by change ∀ c ∈ [.reg 9, .flags, .rip], BodyComponent (rspOf t9) c
        simp [BodyComponent])
    (by change Component.reg 4 ∉ [.reg 9, .flags, .rip]; simp)
  have mem10 : t10.external = t9.external := f10.external (by simp [Component.Covers])
  have saved10 : memLoad t10.external (stackPtr s - 56#64) 64 = s.regValue .rdi := by
    rw [mem10]; exact saved9
  have zero10 : memLoad t10.external (stackPtr s - 60#64) 8 = 0 := by
    rw [mem10]; exact zero9
  have h10r7 : (Operand.reg 7 : Operand 8).read t10 = 0 := by
    rw [f10.read (r := 7) (n := 8) (by simp), f9.read (r := 7) (n := 8) (by simp), f8.read (r := 7) (n := 8) (by simp), f7.read (r := 7) (n := 8) (by simp), f6.read (r := 7) (n := 8) (by simp), f5.read (r := 7) (n := 8) (by simp), f4.read (r := 7) (n := 8) (by simp), f3.read (r := 7) (n := 8) (by simp), f2.read (r := 7) (n := 8) (by simp), f1.read (r := 7) (n := 8) (by simp)]
    exact state.dil
  obtain ⟨t11, run11, ready11, e11⟩ :=
    (mov_m8_r8_effect_step 0x109663 0x40 (by simp [RexPrefix]) 7 (.sib 4 none 0 (.d8 12)) (by decide) rfl rfl).advances ready10
      (programText_slice (programLoaded_codeIn st10.loaded) 0x9663 _
        (by decide) (by decide +kernel))
      ⟨e10.rip, st10.scratch_byte_writable pre (offset := 12) (by decide),
        st10.scratch_code_apart pre (offset := 12) (codeOffset := 0x9663)
          (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x9668 (by decide)))
  have ce11 : (storeEffect 0x109663 (3 + ((.sib 4 none 0 (.d8 12)) : AddrMode).tail.length)
      (storeAddrAt 0x109663 (.sib 4 none 0 (.d8 12)) (3 + ((.sib 4 none 0 (.d8 12)) : AddrMode).tail.length))
      (fun t => (Operand.reg (gprNumber 0 (rexR (0x40 : UInt8).toBitVec) 7) : Operand 8).read t)
      t10).components = [.mem (rspOf t10 + 12#64) 1, .rip] := by
    simp [storeEffect_components, storeAddrAt, AddrMode.addr, AddrMode.reg64,
      Disp.value, rspOf, Operand.read]
  have f11 : AgreesExcept [.mem (rspOf t10 + 12#64) 1, .rip] t10 t11 := by
    have h := e11.agrees
    rw [ce11] at h
    exact h
  have st11 := st10.of_effect pre run11 ready11 e11
    (by rw [ce11]; change ∀ c ∈ [.mem (rspOf t10 + 12#64) 1, .rip], BodyComponent (rspOf t10) c
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        intro c hc; rcases hc with rfl | rfl
        · exact ⟨12, rfl, by decide⟩
        · trivial)
    (by rw [ce11]; change Component.reg 4 ∉ [.mem (rspOf t10 + 12#64) 1, .rip]; simp)
  have saved11 := (byte_store_saved_pointer st10 (by decide) f11).trans saved10
  have zero11 : memLoad t11.external (stackPtr s - 60#64) 8 = 0 := by
    have h : memLoad t11.external (rspOf t10 + 12#64) 8 = (Operand.reg 7 : Operand 8).read t10 := e11.writes
    rw [st10.scratch_address (offset := 12) (by decide), h10r7] at h
    exact h
  obtain ⟨t12, run12, ready12, e12⟩ :=
    (movzx_r32_m8_effect_step 0x109668 1 (.sib 4 none 0 (.d8 12)) (by decide) rfl rfl).advances ready11
      (programText_slice (programLoaded_codeIn st11.loaded) 0x9668 _
        (by decide) (by decide +kernel))
      ⟨e11.rip, st11.scratch_readable pre (offset := 12) (len := 1) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x966d (by decide)))
  have f12 : AgreesExcept [.reg 1, .rip] t11 t12 := e12.agrees
  have st12 := st11.of_effect pre run12 ready12 e12
    (by change ∀ c ∈ [.reg 1, .rip], BodyComponent (rspOf t11) c
        simp [BodyComponent])
    (by change Component.reg 4 ∉ [.reg 1, .rip]; simp)
  have mem12 : t12.external = t11.external := f12.external (by simp [Component.Covers])
  have saved12 : memLoad t12.external (stackPtr s - 56#64) 64 = s.regValue .rdi := by
    rw [mem12]; exact saved11
  have zero12 : memLoad t12.external (stackPtr s - 60#64) 8 = 0 := by
    rw [mem12]; exact zero11
  have v12 : (Operand.reg 1 : Operand 64).read t12 = 0 := by
    have h : (Operand.reg 1 : Operand 64).read t12 =
      (memLoad t11.external (rspOf t11 + 12#64) 8).setWidth 64 := e12.writes
    rw [show rspOf t11 + 12#64 = stackPtr s - 60#64 from st11.scratch_address (offset := 12) (by decide)] at h
    rw [zero11] at h
    exact h
  have h12r1 : (Operand.reg 1 : Operand 64).read t12 = 0 := by
    exact v12
  obtain ⟨t13, run13, ready13, e13⟩ :=
    (neg_r64_effect_step 0x10966d 0x48 0xd9 (by simp [RexWPrefix]) rfl rfl).advances ready12
      (programText_slice (programLoaded_codeIn st12.loaded) 0x966d _
        (by decide) (by decide +kernel))
      e12.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x9670 (by decide)))
  have f13 : AgreesExcept [.reg 1, .flags, .rip] t12 t13 := e13.agrees
  have st13 := st12.of_effect pre run13 ready13 e13
    (by change ∀ c ∈ [.reg 1, .flags, .rip], BodyComponent (rspOf t12) c
        simp [BodyComponent])
    (by change Component.reg 4 ∉ [.reg 1, .flags, .rip]; simp)
  have mem13 : t13.external = t12.external := f13.external (by simp [Component.Covers])
  have saved13 : memLoad t13.external (stackPtr s - 56#64) 64 = s.regValue .rdi := by
    rw [mem13]; exact saved12
  have zero13 : memLoad t13.external (stackPtr s - 60#64) 8 = 0 := by
    rw [mem13]; exact zero12
  have v13 : (Operand.reg 1 : Operand 64).read t13 = 0 := by
    have h : (Operand.reg 1 : Operand 64).read t13 = -(Operand.reg 1 : Operand 64).read t12 := e13.writes
    rw [h12r1] at h
    exact h
  obtain ⟨t14, run14, ready14, e14⟩ :=
    (xor_r64_r64_effect_step 0x109670 0x4d 0xc1 (by simp [RexWPrefix]) rfl).advances ready13
      (programText_slice (programLoaded_codeIn st13.loaded) 0x9670 _
        (by decide) (by decide +kernel))
      e13.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x9673 (by decide)))
  have f14 : AgreesExcept [.reg 9, .flags, .rip] t13 t14 := e14.agrees
  have st14 := st13.of_effect pre run14 ready14 e14
    (by change ∀ c ∈ [.reg 9, .flags, .rip], BodyComponent (rspOf t13) c
        simp [BodyComponent])
    (by change Component.reg 4 ∉ [.reg 9, .flags, .rip]; simp)
  have mem14 : t14.external = t13.external := f14.external (by simp [Component.Covers])
  have saved14 : memLoad t14.external (stackPtr s - 56#64) 64 = s.regValue .rdi := by
    rw [mem14]; exact saved13
  have zero14 : memLoad t14.external (stackPtr s - 60#64) 8 = 0 := by
    rw [mem14]; exact zero13
  have h14r1 : (Operand.reg 1 : Operand 64).read t14 = 0 := by
    rw [f14.read (r := 1) (n := 64) (by simp)]
    exact v13
  obtain ⟨t15, run15, ready15, e15⟩ :=
    (and_r64_r64_effect_step 0x109673 0x49 0xc9 (by simp [RexWPrefix]) rfl).advances ready14
      (programText_slice (programLoaded_codeIn st14.loaded) 0x9673 _
        (by decide) (by decide +kernel))
      e14.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x9676 (by decide)))
  have f15 : AgreesExcept [.reg 9, .flags, .rip] t14 t15 := e15.agrees
  have st15 := st14.of_effect pre run15 ready15 e15
    (by change ∀ c ∈ [.reg 9, .flags, .rip], BodyComponent (rspOf t14) c
        simp [BodyComponent])
    (by change Component.reg 4 ∉ [.reg 9, .flags, .rip]; simp)
  have mem15 : t15.external = t14.external := f15.external (by simp [Component.Covers])
  have saved15 : memLoad t15.external (stackPtr s - 56#64) 64 = s.regValue .rdi := by
    rw [mem15]; exact saved14
  have zero15 : memLoad t15.external (stackPtr s - 60#64) 8 = 0 := by
    rw [mem15]; exact zero14
  have v15 : (Operand.reg 9 : Operand 64).read t15 = 0 := by
    have h : (Operand.reg 9 : Operand 64).read t15 =
      (Operand.reg 9 : Operand 64).read t14 &&& (Operand.reg 1 : Operand 64).read t14 := e15.writes
    rw [h14r1] at h
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.and_zero] using h
  have h15r6 : (Operand.reg 6 : Operand 64).read t15 = a.l1 := by
    rw [f15.read (r := 6) (n := 64) (by simp), f14.read (r := 6) (n := 64) (by simp), f13.read (r := 6) (n := 64) (by simp), f12.read (r := 6) (n := 64) (by simp), f11.read (r := 6) (n := 64) (by simp), f10.read (r := 6) (n := 64) (by simp), f9.read (r := 6) (n := 64) (by simp), f8.read (r := 6) (n := 64) (by simp), f7.read (r := 6) (n := 64) (by simp), f6.read (r := 6) (n := 64) (by simp), f5.read (r := 6) (n := 64) (by simp), f4.read (r := 6) (n := 64) (by simp), f3.read (r := 6) (n := 64) (by simp), f2.read (r := 6) (n := 64) (by simp), f1.read (r := 6) (n := 64) (by simp)]
    exact state.rsi
  obtain ⟨t16, run16, ready16, e16⟩ :=
    (mov_r64_r64_effect_step 0x109676 0x48 0xf3 (by simp [RexWPrefix]) rfl).advances ready15
      (programText_slice (programLoaded_codeIn st15.loaded) 0x9676 _
        (by decide) (by decide +kernel))
      e15.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x9679 (by decide)))
  have f16 : AgreesExcept [.reg 3, .rip] t15 t16 := e16.agrees
  have st16 := st15.of_effect pre run16 ready16 e16
    (by change ∀ c ∈ [.reg 3, .rip], BodyComponent (rspOf t15) c
        simp [BodyComponent])
    (by change Component.reg 4 ∉ [.reg 3, .rip]; simp)
  have mem16 : t16.external = t15.external := f16.external (by simp [Component.Covers])
  have saved16 : memLoad t16.external (stackPtr s - 56#64) 64 = s.regValue .rdi := by
    rw [mem16]; exact saved15
  have zero16 : memLoad t16.external (stackPtr s - 60#64) 8 = 0 := by
    rw [mem16]; exact zero15
  have v16 : (Operand.reg 3 : Operand 64).read t16 = a.l1 := by
    have h : (Operand.reg 3 : Operand 64).read t16 = (Operand.reg 6 : Operand 64).read t15 := e16.writes
    rw [h15r6] at h
    exact h
  have h16r2 : (Operand.reg 2 : Operand 64).read t16 = 1 := by
    rw [f16.read (r := 2) (n := 64) (by simp), f15.read (r := 2) (n := 64) (by simp), f14.read (r := 2) (n := 64) (by simp), f13.read (r := 2) (n := 64) (by simp), f12.read (r := 2) (n := 64) (by simp), f11.read (r := 2) (n := 64) (by simp), f10.read (r := 2) (n := 64) (by simp), f9.read (r := 2) (n := 64) (by simp), f8.read (r := 2) (n := 64) (by simp), f7.read (r := 2) (n := 64) (by simp), f6.read (r := 2) (n := 64) (by simp), f5.read (r := 2) (n := 64) (by simp), f4.read (r := 2) (n := 64) (by simp), f3.read (r := 2) (n := 64) (by simp), f2.read (r := 2) (n := 64) (by simp), f1.read (r := 2) (n := 64) (by simp)]
    exact state.rdx
  obtain ⟨t17, run17, ready17, e17⟩ :=
    (mov_r32_r32_effect_step 0x109679 0xd1 rfl).advances ready16
      (programText_slice (programLoaded_codeIn st16.loaded) 0x9679 _
        (by decide) (by decide +kernel))
      e16.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x967b (by decide)))
  have f17 : AgreesExcept [.reg 1, .rip] t16 t17 := e17.agrees
  have st17 := st16.of_effect pre run17 ready17 e17
    (by change ∀ c ∈ [.reg 1, .rip], BodyComponent (rspOf t16) c
        simp [BodyComponent])
    (by change Component.reg 4 ∉ [.reg 1, .rip]; simp)
  have mem17 : t17.external = t16.external := f17.external (by simp [Component.Covers])
  have saved17 : memLoad t17.external (stackPtr s - 56#64) 64 = s.regValue .rdi := by
    rw [mem17]; exact saved16
  have zero17 : memLoad t17.external (stackPtr s - 60#64) 8 = 0 := by
    rw [mem17]; exact zero16
  have v17 : (Operand.reg 1 : Operand 64).read t17 = 1 := by
    have h : (Operand.reg 1 : Operand 64).read t17 = (((Operand.reg 2 : Operand 64).read t16).setWidth 32).setWidth 64 := e17.writes
    rw [h16r2] at h
    exact h
  have h17r1 : (Operand.reg 1 : Operand 64).read t17 = 1 := by
    exact v17
  obtain ⟨t18, run18, ready18, e18⟩ :=
    (shrd_r64_r64_cl_one_effect_step 0x10967b 0x4c 0xc3 (by simp [RexWPrefix]) rfl).advances ready17
      (programText_slice (programLoaded_codeIn st17.loaded) 0x967b _
        (by decide) (by decide +kernel))
      ⟨e17.rip, by change ((Operand.reg 1 : Operand 64).read t17).setWidth 8 = 1; rw [h17r1]; rfl⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x967f (by decide)))
  have f18 : AgreesExcept [.reg 3, .flags, .rip] t17 t18 := e18.agrees
  have st18 := st17.of_effect pre run18 ready18 e18
    (by change ∀ c ∈ [.reg 3, .flags, .rip], BodyComponent (rspOf t17) c
        simp [BodyComponent])
    (by change Component.reg 4 ∉ [.reg 3, .flags, .rip]; simp)
  have mem18 : t18.external = t17.external := f18.external (by simp [Component.Covers])
  have saved18 : memLoad t18.external (stackPtr s - 56#64) 64 = s.regValue .rdi := by
    rw [mem18]; exact saved17
  have zero18 : memLoad t18.external (stackPtr s - 60#64) 8 = 0 := by
    rw [mem18]; exact zero17
  have h18r9 : (Operand.reg 9 : Operand 64).read t18 = 0 := by
    rw [f18.read (r := 9) (n := 64) (by simp), f17.read (r := 9) (n := 64) (by simp), f16.read (r := 9) (n := 64) (by simp)]
    exact v15
  have h18r8 : (Operand.reg 8 : Operand 64).read t18 = a.l2 := by
    rw [f18.read (r := 8) (n := 64) (by simp), f17.read (r := 8) (n := 64) (by simp), f16.read (r := 8) (n := 64) (by simp), f15.read (r := 8) (n := 64) (by simp), f14.read (r := 8) (n := 64) (by simp), f13.read (r := 8) (n := 64) (by simp), f12.read (r := 8) (n := 64) (by simp), f11.read (r := 8) (n := 64) (by simp), f10.read (r := 8) (n := 64) (by simp), f9.read (r := 8) (n := 64) (by simp), f8.read (r := 8) (n := 64) (by simp), f7.read (r := 8) (n := 64) (by simp), f6.read (r := 8) (n := 64) (by simp), f5.read (r := 8) (n := 64) (by simp), f4.read (r := 8) (n := 64) (by simp), f3.read (r := 8) (n := 64) (by simp), f2.read (r := 8) (n := 64) (by simp), f1.read (r := 8) (n := 64) (by simp)]
    exact state.r8
  obtain ⟨t19, run19, ready19, e19⟩ :=
    (xor_r64_r64_effect_step 0x10967f 0x4d 0xc1 (by simp [RexWPrefix]) rfl).advances ready18
      (programText_slice (programLoaded_codeIn st18.loaded) 0x967f _
        (by decide) (by decide +kernel))
      e18.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x9682 (by decide)))
  have f19 : AgreesExcept [.reg 9, .flags, .rip] t18 t19 := e19.agrees
  have st19 := st18.of_effect pre run19 ready19 e19
    (by change ∀ c ∈ [.reg 9, .flags, .rip], BodyComponent (rspOf t18) c
        simp [BodyComponent])
    (by change Component.reg 4 ∉ [.reg 9, .flags, .rip]; simp)
  have mem19 : t19.external = t18.external := f19.external (by simp [Component.Covers])
  have saved19 : memLoad t19.external (stackPtr s - 56#64) 64 = s.regValue .rdi := by
    rw [mem19]; exact saved18
  have zero19 : memLoad t19.external (stackPtr s - 60#64) 8 = 0 := by
    rw [mem19]; exact zero18
  have v19 : (Operand.reg 9 : Operand 64).read t19 = a.l2 := by
    have h : (Operand.reg 9 : Operand 64).read t19 =
      (Operand.reg 9 : Operand 64).read t18 ^^^ (Operand.reg 8 : Operand 64).read t18 := e19.writes
    rw [h18r9, h18r8] at h
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.zero_xor] using h
  have h19r7 : (Operand.reg 7 : Operand 8).read t19 = 0 := by
    rw [f19.read (r := 7) (n := 8) (by simp), f18.read (r := 7) (n := 8) (by simp), f17.read (r := 7) (n := 8) (by simp), f16.read (r := 7) (n := 8) (by simp), f15.read (r := 7) (n := 8) (by simp), f14.read (r := 7) (n := 8) (by simp), f13.read (r := 7) (n := 8) (by simp), f12.read (r := 7) (n := 8) (by simp), f11.read (r := 7) (n := 8) (by simp), f10.read (r := 7) (n := 8) (by simp), f9.read (r := 7) (n := 8) (by simp), f8.read (r := 7) (n := 8) (by simp), f7.read (r := 7) (n := 8) (by simp), f6.read (r := 7) (n := 8) (by simp), f5.read (r := 7) (n := 8) (by simp), f4.read (r := 7) (n := 8) (by simp), f3.read (r := 7) (n := 8) (by simp), f2.read (r := 7) (n := 8) (by simp), f1.read (r := 7) (n := 8) (by simp)]
    exact state.dil
  obtain ⟨t20, run20, ready20, e20⟩ :=
    (mov_m8_r8_effect_step 0x109682 0x40 (by simp [RexPrefix]) 7 (.sib 4 none 0 (.d8 12)) (by decide) rfl rfl).advances ready19
      (programText_slice (programLoaded_codeIn st19.loaded) 0x9682 _
        (by decide) (by decide +kernel))
      ⟨e19.rip, st19.scratch_byte_writable pre (offset := 12) (by decide),
        st19.scratch_code_apart pre (offset := 12) (codeOffset := 0x9682)
          (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x9687 (by decide)))
  have ce20 : (storeEffect 0x109682 (3 + ((.sib 4 none 0 (.d8 12)) : AddrMode).tail.length)
      (storeAddrAt 0x109682 (.sib 4 none 0 (.d8 12)) (3 + ((.sib 4 none 0 (.d8 12)) : AddrMode).tail.length))
      (fun t => (Operand.reg (gprNumber 0 (rexR (0x40 : UInt8).toBitVec) 7) : Operand 8).read t)
      t19).components = [.mem (rspOf t19 + 12#64) 1, .rip] := by
    simp [storeEffect_components, storeAddrAt, AddrMode.addr, AddrMode.reg64,
      Disp.value, rspOf, Operand.read]
  have f20 : AgreesExcept [.mem (rspOf t19 + 12#64) 1, .rip] t19 t20 := by
    have h := e20.agrees
    rw [ce20] at h
    exact h
  have st20 := st19.of_effect pre run20 ready20 e20
    (by rw [ce20]; change ∀ c ∈ [.mem (rspOf t19 + 12#64) 1, .rip], BodyComponent (rspOf t19) c
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        intro c hc; rcases hc with rfl | rfl
        · exact ⟨12, rfl, by decide⟩
        · trivial)
    (by rw [ce20]; change Component.reg 4 ∉ [.mem (rspOf t19 + 12#64) 1, .rip]; simp)
  have saved20 := (byte_store_saved_pointer st19 (by decide) f20).trans saved19
  have zero20 : memLoad t20.external (stackPtr s - 60#64) 8 = 0 := by
    have h : memLoad t20.external (rspOf t19 + 12#64) 8 = (Operand.reg 7 : Operand 8).read t19 := e20.writes
    rw [st19.scratch_address (offset := 12) (by decide), h19r7] at h
    exact h
  obtain ⟨t21, run21, ready21, e21⟩ :=
    (movzx_r_m8_rex_effect_step 0x109687 0x44 (by simp [RexPrefix]) 32 (.inr rfl) (by intro; rfl) 0 (.sib 4 none 0 (.d8 12)) (by decide) rfl rfl).advances ready20
      (programText_slice (programLoaded_codeIn st20.loaded) 0x9687 _
        (by decide) (by decide +kernel))
      ⟨e20.rip, st20.scratch_readable pre (offset := 12) (len := 1) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x968d (by decide)))
  have f21 : AgreesExcept [.reg 8, .rip] t20 t21 := e21.agrees
  have st21 := st20.of_effect pre run21 ready21 e21
    (by change ∀ c ∈ [.reg 8, .rip], BodyComponent (rspOf t20) c
        simp [BodyComponent])
    (by change Component.reg 4 ∉ [.reg 8, .rip]; simp)
  have mem21 : t21.external = t20.external := f21.external (by simp [Component.Covers])
  have saved21 : memLoad t21.external (stackPtr s - 56#64) 64 = s.regValue .rdi := by
    rw [mem21]; exact saved20
  have zero21 : memLoad t21.external (stackPtr s - 60#64) 8 = 0 := by
    rw [mem21]; exact zero20
  have v21 : (Operand.reg 8 : Operand 64).read t21 = 0 := by
    have h : (Operand.reg 8 : Operand 64).read t21 =
      (memLoad t20.external (rspOf t20 + 12#64) 8).setWidth 64 := e21.writes
    rw [show rspOf t20 + 12#64 = stackPtr s - 60#64 from st20.scratch_address (offset := 12) (by decide)] at h
    rw [zero20] at h
    exact h
  have h21r8 : (Operand.reg 8 : Operand 64).read t21 = 0 := by
    exact v21
  obtain ⟨t22, run22, ready22, e22⟩ :=
    (neg_r64_effect_step 0x10968d 0x49 0xd8 (by simp [RexWPrefix]) rfl rfl).advances ready21
      (programText_slice (programLoaded_codeIn st21.loaded) 0x968d _
        (by decide) (by decide +kernel))
      e21.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x9690 (by decide)))
  have f22 : AgreesExcept [.reg 8, .flags, .rip] t21 t22 := e22.agrees
  have st22 := st21.of_effect pre run22 ready22 e22
    (by change ∀ c ∈ [.reg 8, .flags, .rip], BodyComponent (rspOf t21) c
        simp [BodyComponent])
    (by change Component.reg 4 ∉ [.reg 8, .flags, .rip]; simp)
  have mem22 : t22.external = t21.external := f22.external (by simp [Component.Covers])
  have saved22 : memLoad t22.external (stackPtr s - 56#64) 64 = s.regValue .rdi := by
    rw [mem22]; exact saved21
  have zero22 : memLoad t22.external (stackPtr s - 60#64) 8 = 0 := by
    rw [mem22]; exact zero21
  have v22 : (Operand.reg 8 : Operand 64).read t22 = 0 := by
    have h : (Operand.reg 8 : Operand 64).read t22 = -(Operand.reg 8 : Operand 64).read t21 := e22.writes
    rw [h21r8] at h
    exact h
  obtain ⟨t23, run23, ready23, e23⟩ :=
    (xor_r64_r64_effect_step 0x109690 0x48 0xf3 (by simp [RexWPrefix]) rfl).advances ready22
      (programText_slice (programLoaded_codeIn st22.loaded) 0x9690 _
        (by decide) (by decide +kernel))
      e22.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x9693 (by decide)))
  have f23 : AgreesExcept [.reg 3, .flags, .rip] t22 t23 := e23.agrees
  have st23 := st22.of_effect pre run23 ready23 e23
    (by change ∀ c ∈ [.reg 3, .flags, .rip], BodyComponent (rspOf t22) c
        simp [BodyComponent])
    (by change Component.reg 4 ∉ [.reg 3, .flags, .rip]; simp)
  have mem23 : t23.external = t22.external := f23.external (by simp [Component.Covers])
  have saved23 : memLoad t23.external (stackPtr s - 56#64) 64 = s.regValue .rdi := by
    rw [mem23]; exact saved22
  have zero23 : memLoad t23.external (stackPtr s - 60#64) 8 = 0 := by
    rw [mem23]; exact zero22
  have h23r0 : (Operand.reg 0 : Operand 64).read t23 = a.l0 := by
    rw [f23.read (r := 0) (n := 64) (by simp), f22.read (r := 0) (n := 64) (by simp), f21.read (r := 0) (n := 64) (by simp), f20.read (r := 0) (n := 64) (by simp), f19.read (r := 0) (n := 64) (by simp), f18.read (r := 0) (n := 64) (by simp), f17.read (r := 0) (n := 64) (by simp), f16.read (r := 0) (n := 64) (by simp), f15.read (r := 0) (n := 64) (by simp), f14.read (r := 0) (n := 64) (by simp), f13.read (r := 0) (n := 64) (by simp), f12.read (r := 0) (n := 64) (by simp), f11.read (r := 0) (n := 64) (by simp), f10.read (r := 0) (n := 64) (by simp), f9.read (r := 0) (n := 64) (by simp), f8.read (r := 0) (n := 64) (by simp), f7.read (r := 0) (n := 64) (by simp), f6.read (r := 0) (n := 64) (by simp), f5.read (r := 0) (n := 64) (by simp), f4.read (r := 0) (n := 64) (by simp), f3.read (r := 0) (n := 64) (by simp), f2.read (r := 0) (n := 64) (by simp), f1.read (r := 0) (n := 64) (by simp)]
    exact state.rax
  obtain ⟨t24, run24, ready24, e24⟩ :=
    (mov_r64_r64_effect_step 0x109693 0x49 0xc6 (by simp [RexWPrefix]) rfl).advances ready23
      (programText_slice (programLoaded_codeIn st23.loaded) 0x9693 _
        (by decide) (by decide +kernel))
      e23.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x9696 (by decide)))
  have f24 : AgreesExcept [.reg 14, .rip] t23 t24 := e24.agrees
  have st24 := st23.of_effect pre run24 ready24 e24
    (by change ∀ c ∈ [.reg 14, .rip], BodyComponent (rspOf t23) c
        simp [BodyComponent])
    (by change Component.reg 4 ∉ [.reg 14, .rip]; simp)
  have mem24 : t24.external = t23.external := f24.external (by simp [Component.Covers])
  have saved24 : memLoad t24.external (stackPtr s - 56#64) 64 = s.regValue .rdi := by
    rw [mem24]; exact saved23
  have zero24 : memLoad t24.external (stackPtr s - 60#64) 8 = 0 := by
    rw [mem24]; exact zero23
  have v24 : (Operand.reg 14 : Operand 64).read t24 = a.l0 := by
    have h : (Operand.reg 14 : Operand 64).read t24 = (Operand.reg 0 : Operand 64).read t23 := e24.writes
    rw [h23r0] at h
    exact h
  have h24r1 : (Operand.reg 1 : Operand 64).read t24 = 1 := by
    rw [f24.read (r := 1) (n := 64) (by simp), f23.read (r := 1) (n := 64) (by simp), f22.read (r := 1) (n := 64) (by simp), f21.read (r := 1) (n := 64) (by simp), f20.read (r := 1) (n := 64) (by simp), f19.read (r := 1) (n := 64) (by simp), f18.read (r := 1) (n := 64) (by simp)]
    exact v17
  obtain ⟨t25, run25, ready25, e25⟩ :=
    (shrd_r64_r64_cl_one_effect_step 0x109696 0x49 0xf6 (by simp [RexWPrefix]) rfl).advances ready24
      (programText_slice (programLoaded_codeIn st24.loaded) 0x9696 _
        (by decide) (by decide +kernel))
      ⟨e24.rip, by change ((Operand.reg 1 : Operand 64).read t24).setWidth 8 = 1; rw [h24r1]; rfl⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x969a (by decide)))
  have f25 : AgreesExcept [.reg 14, .flags, .rip] t24 t25 := e25.agrees
  have st25 := st24.of_effect pre run25 ready25 e25
    (by change ∀ c ∈ [.reg 14, .flags, .rip], BodyComponent (rspOf t24) c
        simp [BodyComponent])
    (by change Component.reg 4 ∉ [.reg 14, .flags, .rip]; simp)
  have mem25 : t25.external = t24.external := f25.external (by simp [Component.Covers])
  have saved25 : memLoad t25.external (stackPtr s - 56#64) 64 = s.regValue .rdi := by
    rw [mem25]; exact saved24
  have zero25 : memLoad t25.external (stackPtr s - 60#64) 8 = 0 := by
    rw [mem25]; exact zero24
  have h25r8 : (Operand.reg 8 : Operand 64).read t25 = 0 := by
    rw [f25.read (r := 8) (n := 64) (by simp), f24.read (r := 8) (n := 64) (by simp), f23.read (r := 8) (n := 64) (by simp)]
    exact v22
  obtain ⟨t26, run26, ready26, e26⟩ :=
    (and_r64_r64_effect_step 0x10969a 0x4c 0xc3 (by simp [RexWPrefix]) rfl).advances ready25
      (programText_slice (programLoaded_codeIn st25.loaded) 0x969a _
        (by decide) (by decide +kernel))
      e25.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x969d (by decide)))
  have f26 : AgreesExcept [.reg 3, .flags, .rip] t25 t26 := e26.agrees
  have st26 := st25.of_effect pre run26 ready26 e26
    (by change ∀ c ∈ [.reg 3, .flags, .rip], BodyComponent (rspOf t25) c
        simp [BodyComponent])
    (by change Component.reg 4 ∉ [.reg 3, .flags, .rip]; simp)
  have mem26 : t26.external = t25.external := f26.external (by simp [Component.Covers])
  have saved26 : memLoad t26.external (stackPtr s - 56#64) 64 = s.regValue .rdi := by
    rw [mem26]; exact saved25
  have zero26 : memLoad t26.external (stackPtr s - 60#64) 8 = 0 := by
    rw [mem26]; exact zero25
  have v26 : (Operand.reg 3 : Operand 64).read t26 = 0 := by
    have h : (Operand.reg 3 : Operand 64).read t26 =
      (Operand.reg 3 : Operand 64).read t25 &&& (Operand.reg 8 : Operand 64).read t25 := e26.writes
    rw [h25r8] at h
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.and_zero] using h
  have h26r3 : (Operand.reg 3 : Operand 64).read t26 = 0 := by
    exact v26
  have h26r6 : (Operand.reg 6 : Operand 64).read t26 = a.l1 := by
    rw [f26.read (r := 6) (n := 64) (by simp), f25.read (r := 6) (n := 64) (by simp), f24.read (r := 6) (n := 64) (by simp), f23.read (r := 6) (n := 64) (by simp), f22.read (r := 6) (n := 64) (by simp), f21.read (r := 6) (n := 64) (by simp), f20.read (r := 6) (n := 64) (by simp), f19.read (r := 6) (n := 64) (by simp), f18.read (r := 6) (n := 64) (by simp), f17.read (r := 6) (n := 64) (by simp), f16.read (r := 6) (n := 64) (by simp), f15.read (r := 6) (n := 64) (by simp), f14.read (r := 6) (n := 64) (by simp), f13.read (r := 6) (n := 64) (by simp), f12.read (r := 6) (n := 64) (by simp), f11.read (r := 6) (n := 64) (by simp), f10.read (r := 6) (n := 64) (by simp), f9.read (r := 6) (n := 64) (by simp), f8.read (r := 6) (n := 64) (by simp), f7.read (r := 6) (n := 64) (by simp), f6.read (r := 6) (n := 64) (by simp), f5.read (r := 6) (n := 64) (by simp), f4.read (r := 6) (n := 64) (by simp), f3.read (r := 6) (n := 64) (by simp), f2.read (r := 6) (n := 64) (by simp), f1.read (r := 6) (n := 64) (by simp)]
    exact state.rsi
  obtain ⟨t27, run27, ready27, e27⟩ :=
    (xor_r64_r64_effect_step 0x10969d 0x48 0xf3 (by simp [RexWPrefix]) rfl).advances ready26
      (programText_slice (programLoaded_codeIn st26.loaded) 0x969d _
        (by decide) (by decide +kernel))
      e26.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x96a0 (by decide)))
  have f27 : AgreesExcept [.reg 3, .flags, .rip] t26 t27 := e27.agrees
  have st27 := st26.of_effect pre run27 ready27 e27
    (by change ∀ c ∈ [.reg 3, .flags, .rip], BodyComponent (rspOf t26) c
        simp [BodyComponent])
    (by change Component.reg 4 ∉ [.reg 3, .flags, .rip]; simp)
  have mem27 : t27.external = t26.external := f27.external (by simp [Component.Covers])
  have saved27 : memLoad t27.external (stackPtr s - 56#64) 64 = s.regValue .rdi := by
    rw [mem27]; exact saved26
  have zero27 : memLoad t27.external (stackPtr s - 60#64) 8 = 0 := by
    rw [mem27]; exact zero26
  have v27 : (Operand.reg 3 : Operand 64).read t27 = a.l1 := by
    have h : (Operand.reg 3 : Operand 64).read t27 =
      (Operand.reg 3 : Operand 64).read t26 ^^^ (Operand.reg 6 : Operand 64).read t26 := e27.writes
    rw [h26r3, h26r6] at h
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.zero_xor] using h
  have h27r7 : (Operand.reg 7 : Operand 8).read t27 = 0 := by
    rw [f27.read (r := 7) (n := 8) (by simp), f26.read (r := 7) (n := 8) (by simp), f25.read (r := 7) (n := 8) (by simp), f24.read (r := 7) (n := 8) (by simp), f23.read (r := 7) (n := 8) (by simp), f22.read (r := 7) (n := 8) (by simp), f21.read (r := 7) (n := 8) (by simp), f20.read (r := 7) (n := 8) (by simp), f19.read (r := 7) (n := 8) (by simp), f18.read (r := 7) (n := 8) (by simp), f17.read (r := 7) (n := 8) (by simp), f16.read (r := 7) (n := 8) (by simp), f15.read (r := 7) (n := 8) (by simp), f14.read (r := 7) (n := 8) (by simp), f13.read (r := 7) (n := 8) (by simp), f12.read (r := 7) (n := 8) (by simp), f11.read (r := 7) (n := 8) (by simp), f10.read (r := 7) (n := 8) (by simp), f9.read (r := 7) (n := 8) (by simp), f8.read (r := 7) (n := 8) (by simp), f7.read (r := 7) (n := 8) (by simp), f6.read (r := 7) (n := 8) (by simp), f5.read (r := 7) (n := 8) (by simp), f4.read (r := 7) (n := 8) (by simp), f3.read (r := 7) (n := 8) (by simp), f2.read (r := 7) (n := 8) (by simp), f1.read (r := 7) (n := 8) (by simp)]
    exact state.dil
  obtain ⟨t28, run28, ready28, e28⟩ :=
    (mov_m8_r8_effect_step 0x1096a0 0x40 (by simp [RexPrefix]) 7 (.sib 4 none 0 (.d8 12)) (by decide) rfl rfl).advances ready27
      (programText_slice (programLoaded_codeIn st27.loaded) 0x96a0 _
        (by decide) (by decide +kernel))
      ⟨e27.rip, st27.scratch_byte_writable pre (offset := 12) (by decide),
        st27.scratch_code_apart pre (offset := 12) (codeOffset := 0x96a0)
          (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x96a5 (by decide)))
  have ce28 : (storeEffect 0x1096a0 (3 + ((.sib 4 none 0 (.d8 12)) : AddrMode).tail.length)
      (storeAddrAt 0x1096a0 (.sib 4 none 0 (.d8 12)) (3 + ((.sib 4 none 0 (.d8 12)) : AddrMode).tail.length))
      (fun t => (Operand.reg (gprNumber 0 (rexR (0x40 : UInt8).toBitVec) 7) : Operand 8).read t)
      t27).components = [.mem (rspOf t27 + 12#64) 1, .rip] := by
    simp [storeEffect_components, storeAddrAt, AddrMode.addr, AddrMode.reg64,
      Disp.value, rspOf, Operand.read]
  have f28 : AgreesExcept [.mem (rspOf t27 + 12#64) 1, .rip] t27 t28 := by
    have h := e28.agrees
    rw [ce28] at h
    exact h
  have st28 := st27.of_effect pre run28 ready28 e28
    (by rw [ce28]; change ∀ c ∈ [.mem (rspOf t27 + 12#64) 1, .rip], BodyComponent (rspOf t27) c
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        intro c hc; rcases hc with rfl | rfl
        · exact ⟨12, rfl, by decide⟩
        · trivial)
    (by rw [ce28]; change Component.reg 4 ∉ [.mem (rspOf t27 + 12#64) 1, .rip]; simp)
  have saved28 := (byte_store_saved_pointer st27 (by decide) f28).trans saved27
  have zero28 : memLoad t28.external (stackPtr s - 60#64) 8 = 0 := by
    have h : memLoad t28.external (rspOf t27 + 12#64) 8 = (Operand.reg 7 : Operand 8).read t27 := e28.writes
    rw [st27.scratch_address (offset := 12) (by decide), h27r7] at h
    exact h
  obtain ⟨t29, run29, ready29, e29⟩ :=
    (movzx_r32_m8_effect_step 0x1096a5 1 (.sib 4 none 0 (.d8 12)) (by decide) rfl rfl).advances ready28
      (programText_slice (programLoaded_codeIn st28.loaded) 0x96a5 _
        (by decide) (by decide +kernel))
      ⟨e28.rip, st28.scratch_readable pre (offset := 12) (len := 1) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x96aa (by decide)))
  have f29 : AgreesExcept [.reg 1, .rip] t28 t29 := e29.agrees
  have st29 := st28.of_effect pre run29 ready29 e29
    (by change ∀ c ∈ [.reg 1, .rip], BodyComponent (rspOf t28) c
        simp [BodyComponent])
    (by change Component.reg 4 ∉ [.reg 1, .rip]; simp)
  have mem29 : t29.external = t28.external := f29.external (by simp [Component.Covers])
  have saved29 : memLoad t29.external (stackPtr s - 56#64) 64 = s.regValue .rdi := by
    rw [mem29]; exact saved28
  have zero29 : memLoad t29.external (stackPtr s - 60#64) 8 = 0 := by
    rw [mem29]; exact zero28
  have v29 : (Operand.reg 1 : Operand 64).read t29 = 0 := by
    have h : (Operand.reg 1 : Operand 64).read t29 =
      (memLoad t28.external (rspOf t28 + 12#64) 8).setWidth 64 := e29.writes
    rw [show rspOf t28 + 12#64 = stackPtr s - 60#64 from st28.scratch_address (offset := 12) (by decide)] at h
    rw [zero28] at h
    exact h
  have h29r1 : (Operand.reg 1 : Operand 64).read t29 = 0 := by
    exact v29
  obtain ⟨t30, run30, ready30, e30⟩ :=
    (neg_r64_effect_step 0x1096aa 0x48 0xd9 (by simp [RexWPrefix]) rfl rfl).advances ready29
      (programText_slice (programLoaded_codeIn st29.loaded) 0x96aa _
        (by decide) (by decide +kernel))
      e29.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x96ad (by decide)))
  have f30 : AgreesExcept [.reg 1, .flags, .rip] t29 t30 := e30.agrees
  have st30 := st29.of_effect pre run30 ready30 e30
    (by change ∀ c ∈ [.reg 1, .flags, .rip], BodyComponent (rspOf t29) c
        simp [BodyComponent])
    (by change Component.reg 4 ∉ [.reg 1, .flags, .rip]; simp)
  have mem30 : t30.external = t29.external := f30.external (by simp [Component.Covers])
  have saved30 : memLoad t30.external (stackPtr s - 56#64) 64 = s.regValue .rdi := by
    rw [mem30]; exact saved29
  have zero30 : memLoad t30.external (stackPtr s - 60#64) 8 = 0 := by
    rw [mem30]; exact zero29
  have v30 : (Operand.reg 1 : Operand 64).read t30 = 0 := by
    have h : (Operand.reg 1 : Operand 64).read t30 = -(Operand.reg 1 : Operand 64).read t29 := e30.writes
    rw [h29r1] at h
    exact h
  obtain ⟨t31, run31, ready31, e31⟩ :=
    (xor_r64_r64_effect_step 0x1096ad 0x49 0xc6 (by simp [RexWPrefix]) rfl).advances ready30
      (programText_slice (programLoaded_codeIn st30.loaded) 0x96ad _
        (by decide) (by decide +kernel))
      e30.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x96b0 (by decide)))
  have f31 : AgreesExcept [.reg 14, .flags, .rip] t30 t31 := e31.agrees
  have st31 := st30.of_effect pre run31 ready31 e31
    (by change ∀ c ∈ [.reg 14, .flags, .rip], BodyComponent (rspOf t30) c
        simp [BodyComponent])
    (by change Component.reg 4 ∉ [.reg 14, .flags, .rip]; simp)
  have mem31 : t31.external = t30.external := f31.external (by simp [Component.Covers])
  have saved31 : memLoad t31.external (stackPtr s - 56#64) 64 = s.regValue .rdi := by
    rw [mem31]; exact saved30
  have zero31 : memLoad t31.external (stackPtr s - 60#64) 8 = 0 := by
    rw [mem31]; exact zero30
  have h31r1 : (Operand.reg 1 : Operand 64).read t31 = 0 := by
    rw [f31.read (r := 1) (n := 64) (by simp)]
    exact v30
  obtain ⟨t32, run32, ready32, e32⟩ :=
    (and_r64_r64_effect_step 0x1096b0 0x49 0xce (by simp [RexWPrefix]) rfl).advances ready31
      (programText_slice (programLoaded_codeIn st31.loaded) 0x96b0 _
        (by decide) (by decide +kernel))
      e31.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x96b3 (by decide)))
  have f32 : AgreesExcept [.reg 14, .flags, .rip] t31 t32 := e32.agrees
  have st32 := st31.of_effect pre run32 ready32 e32
    (by change ∀ c ∈ [.reg 14, .flags, .rip], BodyComponent (rspOf t31) c
        simp [BodyComponent])
    (by change Component.reg 4 ∉ [.reg 14, .flags, .rip]; simp)
  have mem32 : t32.external = t31.external := f32.external (by simp [Component.Covers])
  have saved32 : memLoad t32.external (stackPtr s - 56#64) 64 = s.regValue .rdi := by
    rw [mem32]; exact saved31
  have zero32 : memLoad t32.external (stackPtr s - 60#64) 8 = 0 := by
    rw [mem32]; exact zero31
  have v32 : (Operand.reg 14 : Operand 64).read t32 = 0 := by
    have h : (Operand.reg 14 : Operand 64).read t32 =
      (Operand.reg 14 : Operand 64).read t31 &&& (Operand.reg 1 : Operand 64).read t31 := e32.writes
    rw [h31r1] at h
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.and_zero] using h
  have h32r14 : (Operand.reg 14 : Operand 64).read t32 = 0 := by
    exact v32
  have h32r0 : (Operand.reg 0 : Operand 64).read t32 = a.l0 := by
    rw [f32.read (r := 0) (n := 64) (by simp), f31.read (r := 0) (n := 64) (by simp), f30.read (r := 0) (n := 64) (by simp), f29.read (r := 0) (n := 64) (by simp), f28.read (r := 0) (n := 64) (by simp), f27.read (r := 0) (n := 64) (by simp), f26.read (r := 0) (n := 64) (by simp), f25.read (r := 0) (n := 64) (by simp), f24.read (r := 0) (n := 64) (by simp), f23.read (r := 0) (n := 64) (by simp), f22.read (r := 0) (n := 64) (by simp), f21.read (r := 0) (n := 64) (by simp), f20.read (r := 0) (n := 64) (by simp), f19.read (r := 0) (n := 64) (by simp), f18.read (r := 0) (n := 64) (by simp), f17.read (r := 0) (n := 64) (by simp), f16.read (r := 0) (n := 64) (by simp), f15.read (r := 0) (n := 64) (by simp), f14.read (r := 0) (n := 64) (by simp), f13.read (r := 0) (n := 64) (by simp), f12.read (r := 0) (n := 64) (by simp), f11.read (r := 0) (n := 64) (by simp), f10.read (r := 0) (n := 64) (by simp), f9.read (r := 0) (n := 64) (by simp), f8.read (r := 0) (n := 64) (by simp), f7.read (r := 0) (n := 64) (by simp), f6.read (r := 0) (n := 64) (by simp), f5.read (r := 0) (n := 64) (by simp), f4.read (r := 0) (n := 64) (by simp), f3.read (r := 0) (n := 64) (by simp), f2.read (r := 0) (n := 64) (by simp), f1.read (r := 0) (n := 64) (by simp)]
    exact state.rax
  obtain ⟨t33, run33, ready33, e33⟩ :=
    (xor_r64_r64_effect_step 0x1096b3 0x49 0xc6 (by simp [RexWPrefix]) rfl).advances ready32
      (programText_slice (programLoaded_codeIn st32.loaded) 0x96b3 _
        (by decide) (by decide +kernel))
      e32.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x96b6 (by decide)))
  have f33 : AgreesExcept [.reg 14, .flags, .rip] t32 t33 := e33.agrees
  have st33 := st32.of_effect pre run33 ready33 e33
    (by change ∀ c ∈ [.reg 14, .flags, .rip], BodyComponent (rspOf t32) c
        simp [BodyComponent])
    (by change Component.reg 4 ∉ [.reg 14, .flags, .rip]; simp)
  have mem33 : t33.external = t32.external := f33.external (by simp [Component.Covers])
  have saved33 : memLoad t33.external (stackPtr s - 56#64) 64 = s.regValue .rdi := by
    rw [mem33]; exact saved32
  have zero33 : memLoad t33.external (stackPtr s - 60#64) 8 = 0 := by
    rw [mem33]; exact zero32
  have v33 : (Operand.reg 14 : Operand 64).read t33 = a.l0 := by
    have h : (Operand.reg 14 : Operand 64).read t33 =
      (Operand.reg 14 : Operand 64).read t32 ^^^ (Operand.reg 0 : Operand 64).read t32 := e33.writes
    rw [h32r14, h32r0] at h
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.zero_xor] using h
  have h33r7 : (Operand.reg 7 : Operand 8).read t33 = 0 := by
    rw [f33.read (r := 7) (n := 8) (by simp), f32.read (r := 7) (n := 8) (by simp), f31.read (r := 7) (n := 8) (by simp), f30.read (r := 7) (n := 8) (by simp), f29.read (r := 7) (n := 8) (by simp), f28.read (r := 7) (n := 8) (by simp), f27.read (r := 7) (n := 8) (by simp), f26.read (r := 7) (n := 8) (by simp), f25.read (r := 7) (n := 8) (by simp), f24.read (r := 7) (n := 8) (by simp), f23.read (r := 7) (n := 8) (by simp), f22.read (r := 7) (n := 8) (by simp), f21.read (r := 7) (n := 8) (by simp), f20.read (r := 7) (n := 8) (by simp), f19.read (r := 7) (n := 8) (by simp), f18.read (r := 7) (n := 8) (by simp), f17.read (r := 7) (n := 8) (by simp), f16.read (r := 7) (n := 8) (by simp), f15.read (r := 7) (n := 8) (by simp), f14.read (r := 7) (n := 8) (by simp), f13.read (r := 7) (n := 8) (by simp), f12.read (r := 7) (n := 8) (by simp), f11.read (r := 7) (n := 8) (by simp), f10.read (r := 7) (n := 8) (by simp), f9.read (r := 7) (n := 8) (by simp), f8.read (r := 7) (n := 8) (by simp), f7.read (r := 7) (n := 8) (by simp), f6.read (r := 7) (n := 8) (by simp), f5.read (r := 7) (n := 8) (by simp), f4.read (r := 7) (n := 8) (by simp), f3.read (r := 7) (n := 8) (by simp), f2.read (r := 7) (n := 8) (by simp), f1.read (r := 7) (n := 8) (by simp)]
    exact state.dil
  obtain ⟨t34, run34, ready34, e34⟩ :=
    (mov_m8_r8_effect_step 0x1096b6 0x40 (by simp [RexPrefix]) 7 (.sib 4 none 0 (.d8 15)) (by decide) rfl rfl).advances ready33
      (programText_slice (programLoaded_codeIn st33.loaded) 0x96b6 _
        (by decide) (by decide +kernel))
      ⟨e33.rip, st33.scratch_byte_writable pre (offset := 15) (by decide),
        st33.scratch_code_apart pre (offset := 15) (codeOffset := 0x96b6)
          (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x96bb (by decide)))
  have ce34 : (storeEffect 0x1096b6 (3 + ((.sib 4 none 0 (.d8 15)) : AddrMode).tail.length)
      (storeAddrAt 0x1096b6 (.sib 4 none 0 (.d8 15)) (3 + ((.sib 4 none 0 (.d8 15)) : AddrMode).tail.length))
      (fun t => (Operand.reg (gprNumber 0 (rexR (0x40 : UInt8).toBitVec) 7) : Operand 8).read t)
      t33).components = [.mem (rspOf t33 + 15#64) 1, .rip] := by
    simp [storeEffect_components, storeAddrAt, AddrMode.addr, AddrMode.reg64,
      Disp.value, rspOf, Operand.read]
  have f34 : AgreesExcept [.mem (rspOf t33 + 15#64) 1, .rip] t33 t34 := by
    have h := e34.agrees
    rw [ce34] at h
    exact h
  have st34 := st33.of_effect pre run34 ready34 e34
    (by rw [ce34]; change ∀ c ∈ [.mem (rspOf t33 + 15#64) 1, .rip], BodyComponent (rspOf t33) c
        simp only [List.mem_cons, List.not_mem_nil, or_false]
        intro c hc; rcases hc with rfl | rfl
        · exact ⟨15, rfl, by decide⟩
        · trivial)
    (by rw [ce34]; change Component.reg 4 ∉ [.mem (rspOf t33 + 15#64) 1, .rip]; simp)
  have saved34 := (byte_store_saved_pointer st33 (by decide) f34).trans saved33
  obtain ⟨t35, run35, ready35, e35⟩ :=
    (lea_r64_effect_step 0x1096bb 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 15)) (by decide) rfl rfl).advances ready34
      (programText_slice (programLoaded_codeIn st34.loaded) 0x96bb _
        (by decide) (by decide +kernel))
      e34.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x96c0 (by decide)))
  have f35 : AgreesExcept [.reg 0, .rip] t34 t35 := e35.agrees
  have st35 := st34.of_effect pre run35 ready35 e35
    (by change ∀ c ∈ [.reg 0, .rip], BodyComponent (rspOf t34) c
        simp [BodyComponent])
    (by change Component.reg 4 ∉ [.reg 0, .rip]; simp)
  have mem35 : t35.external = t34.external := f35.external (by simp [Component.Covers])
  have saved35 : memLoad t35.external (stackPtr s - 56#64) 64 = s.regValue .rdi := by
    rw [mem35]; exact saved34
  obtain ⟨t36, run36, ready36, e36⟩ :=
    (mov_r64_m64_effect_step 0x1096c0 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d8 16)) (by decide) rfl rfl).advances ready35
      (programText_slice (programLoaded_codeIn st35.loaded) 0x96c0 _
        (by decide) (by decide +kernel))
      ⟨e35.rip, st35.scratch_readable pre (offset := 16) (len := 8) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x96c5 (by decide)))
  have f36 : AgreesExcept [.reg 0, .rip] t35 t36 := e36.agrees
  have st36 := st35.of_effect pre run36 ready36 e36
    (by change ∀ c ∈ [.reg 0, .rip], BodyComponent (rspOf t35) c
        simp [BodyComponent])
    (by change Component.reg 4 ∉ [.reg 0, .rip]; simp)
  have mem36 : t36.external = t35.external := f36.external (by simp [Component.Covers])
  have saved36 : memLoad t36.external (stackPtr s - 56#64) 64 = s.regValue .rdi := by
    rw [mem36]; exact saved35
  have v36 : (Operand.reg 0 : Operand 64).read t36 = s.regValue .rdi := by
    have h : (Operand.reg 0 : Operand 64).read t36 =
      memLoad t35.external (rspOf t35 + 16#64) 64 := e36.writes
    rw [show rspOf t35 + 16#64 = stackPtr s - 56#64 from st35.scratch_address (offset := 16) (by decide), saved35] at h
    exact h
  have h36r0 : (Operand.reg 0 : Operand 64).read t36 = s.regValue .rdi := by
    exact v36
  have h36r14 : (Operand.reg 14 : Operand 64).read t36 = a.l0 := by
    rw [f36.read (r := 14) (n := 64) (by simp), f35.read (r := 14) (n := 64) (by simp), f34.read (r := 14) (n := 64) (by simp)]
    exact v33
  have h36r3 : (Operand.reg 3 : Operand 64).read t36 = a.l1 := by
    rw [f36.read (r := 3) (n := 64) (by simp), f35.read (r := 3) (n := 64) (by simp), f34.read (r := 3) (n := 64) (by simp), f33.read (r := 3) (n := 64) (by simp), f32.read (r := 3) (n := 64) (by simp), f31.read (r := 3) (n := 64) (by simp), f30.read (r := 3) (n := 64) (by simp), f29.read (r := 3) (n := 64) (by simp), f28.read (r := 3) (n := 64) (by simp)]
    exact v27
  have h36r9 : (Operand.reg 9 : Operand 64).read t36 = a.l2 := by
    rw [f36.read (r := 9) (n := 64) (by simp), f35.read (r := 9) (n := 64) (by simp), f34.read (r := 9) (n := 64) (by simp), f33.read (r := 9) (n := 64) (by simp), f32.read (r := 9) (n := 64) (by simp), f31.read (r := 9) (n := 64) (by simp), f30.read (r := 9) (n := 64) (by simp), f29.read (r := 9) (n := 64) (by simp), f28.read (r := 9) (n := 64) (by simp), f27.read (r := 9) (n := 64) (by simp), f26.read (r := 9) (n := 64) (by simp), f25.read (r := 9) (n := 64) (by simp), f24.read (r := 9) (n := 64) (by simp), f23.read (r := 9) (n := 64) (by simp), f22.read (r := 9) (n := 64) (by simp), f21.read (r := 9) (n := 64) (by simp), f20.read (r := 9) (n := 64) (by simp)]
    exact v19
  have h36r10 : (Operand.reg 10 : Operand 64).read t36 = a.l3 := by
    rw [f36.read (r := 10) (n := 64) (by simp), f35.read (r := 10) (n := 64) (by simp), f34.read (r := 10) (n := 64) (by simp), f33.read (r := 10) (n := 64) (by simp), f32.read (r := 10) (n := 64) (by simp), f31.read (r := 10) (n := 64) (by simp), f30.read (r := 10) (n := 64) (by simp), f29.read (r := 10) (n := 64) (by simp), f28.read (r := 10) (n := 64) (by simp), f27.read (r := 10) (n := 64) (by simp), f26.read (r := 10) (n := 64) (by simp), f25.read (r := 10) (n := 64) (by simp), f24.read (r := 10) (n := 64) (by simp), f23.read (r := 10) (n := 64) (by simp), f22.read (r := 10) (n := 64) (by simp), f21.read (r := 10) (n := 64) (by simp), f20.read (r := 10) (n := 64) (by simp), f19.read (r := 10) (n := 64) (by simp), f18.read (r := 10) (n := 64) (by simp), f17.read (r := 10) (n := 64) (by simp), f16.read (r := 10) (n := 64) (by simp), f15.read (r := 10) (n := 64) (by simp), f14.read (r := 10) (n := 64) (by simp), f13.read (r := 10) (n := 64) (by simp), f12.read (r := 10) (n := 64) (by simp), f11.read (r := 10) (n := 64) (by simp), f10.read (r := 10) (n := 64) (by simp), f9.read (r := 10) (n := 64) (by simp), f8.read (r := 10) (n := 64) (by simp)]
    exact v7
  exact ⟨t36, st36, e36.rip, h36r0, h36r14, h36r3, h36r9, h36r10⟩

end P256.Proofs.Nonce.Initialize.Conversions.ShiftZero.Store
