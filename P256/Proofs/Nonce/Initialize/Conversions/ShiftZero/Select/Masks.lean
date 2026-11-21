import P256.Proofs.Nonce.Initialize.Conversions.ShiftZero.Load
import P256.Proofs.Nonce.Initialize.Conversions.ShiftZero.Store.Memory
import P256.Proofs.Common.Encoding.Serialize.Tail.ByteOps.Store
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

namespace P256.Proofs.Nonce.Initialize.Conversions.ShiftZero

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Field
open P256.Proofs.SecretKeyFromBytes.Scalar

open P256.Proofs.Common.Instructions

structure MaskedState [Bindings] (s t : RamState) (boundary : ReturnBoundary)
    (a : Limbs) : Prop extends Stage s t boundary where
  rip : t.RIP = 0x1095c0
  outputSaved : memLoad t.external (stackPtr s - 56) 64 = s.regValue .rdi
  rdx : t.regValue .rdx = 0
  r13 : t.regValue .r13 = a.l3
  r15 : t.regValue .r15 = a.l2
  r10 : t.regValue .r10 = a.l0
  r14 : t.regValue .r14 = a.l1
  r9 : t.regValue .r9 = 0
  r12 : t.regValue .r12 = 0
  r11 : t.regValue .r11 = 0
  rbp : t.regValue .rbp = 0
  rax : t.regValue .rax = 0
  rsi : t.regValue .rsi = 0
  r8 : t.regValue .r8 = 0
  rbx : t.regValue .rbx = 0

set_option maxHeartbeats 1600000 in
theorem mask_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary} {a : Limbs}
    (pre : CalleePre s boundary 0x109530 32 32 128)
    (state : LoadedState s t boundary a) :
    ∃ u, MaskedState s u boundary a := by
  have st0 := state.toStage
  have ready0 := state.ready
  have saved0 := state.outputSaved
  have h0r0 : (Operand.reg 0 : Operand 8).read t = 0 := by
    change ((Operand.reg 0 : Operand 64).read t).setWidth 8 = _
    have h : (Operand.reg 0 : Operand 64).read t = 0 := state.rax
    rw [h]
    rfl
  obtain ⟨t1, run1, ready1, e1⟩ :=
    (mov_m8_r8_legacy_effect_step 0x109565 0 (by decide) (.sib 4 none 0 (.d8 11)) (by decide) rfl rfl).advances ready0
      (programText_slice (programLoaded_codeIn st0.loaded) 0x9565 _
        (by decide) (by decide +kernel))
      ⟨state.rip, st0.scratch_byte_writable pre (offset := 11) (by decide),
        st0.scratch_code_apart pre (offset := 11) (codeOffset := 0x9565)
          (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x9569 (by decide)))
  have ce1 : (storeEffect 0x109565 4 (storeAddrAt 0x109565 (.sib 4 none 0 (.d8 11)) 4) (fun u => (Operand.reg 0 : Operand 8).read u) t).components = [.mem (rspOf t + 11#64) 1, .rip] := by
    simp [storeEffect_components, storeAddrAt, AddrMode.addr, AddrMode.reg64,
      Disp.value, rspOf, Operand.read]
  have f1 : AgreesExcept [.mem (rspOf t + 11#64) 1, .rip] t t1 := by
    have h := e1.agrees
    change AgreesExcept (storeEffect 0x109565 4 (storeAddrAt 0x109565 (.sib 4 none 0 (.d8 11)) 4) (fun u => (Operand.reg 0 : Operand 8).read u) t).components t t1 at h
    rw [ce1] at h
    exact h
  have st1 := st0.of_effect pre run1 ready1 e1
    (by change ∀ c ∈ (storeEffect 0x109565 4 (storeAddrAt 0x109565 (.sib 4 none 0 (.d8 11)) 4) (fun u => (Operand.reg 0 : Operand 8).read u) t).components, BodyComponent (rspOf t) c
        rw [ce1]
        intro c hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl
        · exact ⟨11, rfl, by decide⟩
        · trivial)
    (by simp [storeEffect_components])
  have saved1 := (Store.byte_store_saved_pointer st0 (by decide) f1).trans saved0
  have zero1 : memLoad t1.external (stackPtr s - 61#64) 8 = 0 := by
    have h : memLoad t1.external (rspOf t + 11#64) 8 =
      (Operand.reg 0 : Operand 8).read t := e1.writes
    rw [st0.scratch_address (offset := 11) (by decide), h0r0] at h
    exact h
  obtain ⟨t2, run2, ready2, e2⟩ :=
    (lea_r64_effect_step 0x109569 0x48 (by simp [RexWPrefix]) 6 (.sib 4 none 0 (.d8 11)) (by decide) rfl rfl).advances ready1
      (programText_slice (programLoaded_codeIn st1.loaded) 0x9569 _
        (by decide) (by decide +kernel))
      e1.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x956e (by decide)))
  have f2 : AgreesExcept [.reg 6, .rip] t1 t2 := e2.agrees
  have st2 := st1.of_effect pre run2 ready2 e2
    (by change ∀ c ∈ [.reg 6, .rip], BodyComponent (rspOf t1) c
        simp [BodyComponent])
    (by change Component.reg 4 ∉ [.reg 6, .rip]; simp)
  have mem2 : t2.external = t1.external := f2.external (by simp [Component.Covers])
  have saved2 : memLoad t2.external (stackPtr s - 56#64) 64 = s.regValue .rdi := by
    rw [mem2]
    exact saved1
  obtain ⟨t3, run3, ready3, e3⟩ :=
    (movzx_r_m8_rex_effect_step 0x10956e 0x44 (by simp [RexPrefix]) 32 (.inr rfl) (fun _ => rfl) 1 (.sib 4 none 0 (.d8 11)) (by decide) rfl rfl).advances ready2
      (programText_slice (programLoaded_codeIn st2.loaded) 0x956e _
        (by decide) (by decide +kernel))
      ⟨e2.rip, st2.scratch_readable pre (offset := 11) (len := 1) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x9574 (by decide)))
  have f3 : AgreesExcept [.reg 9, .rip] t2 t3 := e3.agrees
  have st3 := st2.of_effect pre run3 ready3 e3
    (by change ∀ c ∈ [.reg 9, .rip], BodyComponent (rspOf t2) c
        simp [BodyComponent])
    (by change Component.reg 4 ∉ [.reg 9, .rip]; simp)
  have mem3 : t3.external = t2.external := f3.external (by simp [Component.Covers])
  have saved3 : memLoad t3.external (stackPtr s - 56#64) 64 = s.regValue .rdi := by
    rw [mem3]
    exact saved2
  have v3 : (Operand.reg 9 : Operand 64).read t3 = 0 := by
    have h : (Operand.reg 9 : Operand 64).read t3 =
      (memLoad t2.external (rspOf t2 + 11#64) 8).setWidth 64 := e3.writes
    rw [st2.scratch_address (offset := 11) (by decide), mem2, zero1] at h
    exact h
  have h3r0 : (Operand.reg 0 : Operand 8).read t3 = 0 := by
    change ((Operand.reg 0 : Operand 64).read t3).setWidth 8 = _
    rw [f3.read (r := 0) (n := 64) (by simp), f2.read (r := 0) (n := 64) (by simp), f1.read (r := 0) (n := 64) (by simp)]
    have h : (Operand.reg 0 : Operand 64).read t = 0 := state.rax
    rw [h]
    rfl
  obtain ⟨t4, run4, ready4, e4⟩ :=
    (mov_m8_r8_legacy_effect_step 0x109574 0 (by decide) (.sib 4 none 0 (.d8 11)) (by decide) rfl rfl).advances ready3
      (programText_slice (programLoaded_codeIn st3.loaded) 0x9574 _
        (by decide) (by decide +kernel))
      ⟨e3.rip, st3.scratch_byte_writable pre (offset := 11) (by decide),
        st3.scratch_code_apart pre (offset := 11) (codeOffset := 0x9574)
          (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x9578 (by decide)))
  have ce4 : (storeEffect 0x109574 4 (storeAddrAt 0x109574 (.sib 4 none 0 (.d8 11)) 4) (fun u => (Operand.reg 0 : Operand 8).read u) t3).components = [.mem (rspOf t3 + 11#64) 1, .rip] := by
    simp [storeEffect_components, storeAddrAt, AddrMode.addr, AddrMode.reg64,
      Disp.value, rspOf, Operand.read]
  have f4 : AgreesExcept [.mem (rspOf t3 + 11#64) 1, .rip] t3 t4 := by
    have h := e4.agrees
    change AgreesExcept (storeEffect 0x109574 4 (storeAddrAt 0x109574 (.sib 4 none 0 (.d8 11)) 4) (fun u => (Operand.reg 0 : Operand 8).read u) t3).components t3 t4 at h
    rw [ce4] at h
    exact h
  have st4 := st3.of_effect pre run4 ready4 e4
    (by change ∀ c ∈ (storeEffect 0x109574 4 (storeAddrAt 0x109574 (.sib 4 none 0 (.d8 11)) 4) (fun u => (Operand.reg 0 : Operand 8).read u) t3).components, BodyComponent (rspOf t3) c
        rw [ce4]
        intro c hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl
        · exact ⟨11, rfl, by decide⟩
        · trivial)
    (by simp [storeEffect_components])
  have saved4 := (Store.byte_store_saved_pointer st3 (by decide) f4).trans saved3
  have zero4 : memLoad t4.external (stackPtr s - 61#64) 8 = 0 := by
    have h : memLoad t4.external (rspOf t3 + 11#64) 8 =
      (Operand.reg 0 : Operand 8).read t3 := e4.writes
    rw [st3.scratch_address (offset := 11) (by decide), h3r0] at h
    exact h
  obtain ⟨t5, run5, ready5, e5⟩ :=
    (movzx_r_m8_rex_effect_step 0x109578 0x44 (by simp [RexPrefix]) 32 (.inr rfl) (fun _ => rfl) 4 (.sib 4 none 0 (.d8 11)) (by decide) rfl rfl).advances ready4
      (programText_slice (programLoaded_codeIn st4.loaded) 0x9578 _
        (by decide) (by decide +kernel))
      ⟨e4.rip, st4.scratch_readable pre (offset := 11) (len := 1) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x957e (by decide)))
  have f5 : AgreesExcept [.reg 12, .rip] t4 t5 := e5.agrees
  have st5 := st4.of_effect pre run5 ready5 e5
    (by change ∀ c ∈ [.reg 12, .rip], BodyComponent (rspOf t4) c
        simp [BodyComponent])
    (by change Component.reg 4 ∉ [.reg 12, .rip]; simp)
  have mem5 : t5.external = t4.external := f5.external (by simp [Component.Covers])
  have saved5 : memLoad t5.external (stackPtr s - 56#64) 64 = s.regValue .rdi := by
    rw [mem5]
    exact saved4
  have v5 : (Operand.reg 12 : Operand 64).read t5 = 0 := by
    have h : (Operand.reg 12 : Operand 64).read t5 =
      (memLoad t4.external (rspOf t4 + 11#64) 8).setWidth 64 := e5.writes
    rw [st4.scratch_address (offset := 11) (by decide), zero4] at h
    exact h
  have h5r0 : (Operand.reg 0 : Operand 8).read t5 = 0 := by
    change ((Operand.reg 0 : Operand 64).read t5).setWidth 8 = _
    rw [f5.read (r := 0) (n := 64) (by simp), f4.read (r := 0) (n := 64) (by simp), f3.read (r := 0) (n := 64) (by simp), f2.read (r := 0) (n := 64) (by simp), f1.read (r := 0) (n := 64) (by simp)]
    have h : (Operand.reg 0 : Operand 64).read t = 0 := state.rax
    rw [h]
    rfl
  obtain ⟨t6, run6, ready6, e6⟩ :=
    (mov_m8_r8_legacy_effect_step 0x10957e 0 (by decide) (.sib 4 none 0 (.d8 11)) (by decide) rfl rfl).advances ready5
      (programText_slice (programLoaded_codeIn st5.loaded) 0x957e _
        (by decide) (by decide +kernel))
      ⟨e5.rip, st5.scratch_byte_writable pre (offset := 11) (by decide),
        st5.scratch_code_apart pre (offset := 11) (codeOffset := 0x957e)
          (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x9582 (by decide)))
  have ce6 : (storeEffect 0x10957e 4 (storeAddrAt 0x10957e (.sib 4 none 0 (.d8 11)) 4) (fun u => (Operand.reg 0 : Operand 8).read u) t5).components = [.mem (rspOf t5 + 11#64) 1, .rip] := by
    simp [storeEffect_components, storeAddrAt, AddrMode.addr, AddrMode.reg64,
      Disp.value, rspOf, Operand.read]
  have f6 : AgreesExcept [.mem (rspOf t5 + 11#64) 1, .rip] t5 t6 := by
    have h := e6.agrees
    change AgreesExcept (storeEffect 0x10957e 4 (storeAddrAt 0x10957e (.sib 4 none 0 (.d8 11)) 4) (fun u => (Operand.reg 0 : Operand 8).read u) t5).components t5 t6 at h
    rw [ce6] at h
    exact h
  have st6 := st5.of_effect pre run6 ready6 e6
    (by change ∀ c ∈ (storeEffect 0x10957e 4 (storeAddrAt 0x10957e (.sib 4 none 0 (.d8 11)) 4) (fun u => (Operand.reg 0 : Operand 8).read u) t5).components, BodyComponent (rspOf t5) c
        rw [ce6]
        intro c hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl
        · exact ⟨11, rfl, by decide⟩
        · trivial)
    (by simp [storeEffect_components])
  have saved6 := (Store.byte_store_saved_pointer st5 (by decide) f6).trans saved5
  have zero6 : memLoad t6.external (stackPtr s - 61#64) 8 = 0 := by
    have h : memLoad t6.external (rspOf t5 + 11#64) 8 =
      (Operand.reg 0 : Operand 8).read t5 := e6.writes
    rw [st5.scratch_address (offset := 11) (by decide), h5r0] at h
    exact h
  obtain ⟨t7, run7, ready7, e7⟩ :=
    (movzx_r_m8_rex_effect_step 0x109582 0x44 (by simp [RexPrefix]) 32 (.inr rfl) (fun _ => rfl) 3 (.sib 4 none 0 (.d8 11)) (by decide) rfl rfl).advances ready6
      (programText_slice (programLoaded_codeIn st6.loaded) 0x9582 _
        (by decide) (by decide +kernel))
      ⟨e6.rip, st6.scratch_readable pre (offset := 11) (len := 1) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x9588 (by decide)))
  have f7 : AgreesExcept [.reg 11, .rip] t6 t7 := e7.agrees
  have st7 := st6.of_effect pre run7 ready7 e7
    (by change ∀ c ∈ [.reg 11, .rip], BodyComponent (rspOf t6) c
        simp [BodyComponent])
    (by change Component.reg 4 ∉ [.reg 11, .rip]; simp)
  have mem7 : t7.external = t6.external := f7.external (by simp [Component.Covers])
  have saved7 : memLoad t7.external (stackPtr s - 56#64) 64 = s.regValue .rdi := by
    rw [mem7]
    exact saved6
  have v7 : (Operand.reg 11 : Operand 64).read t7 = 0 := by
    have h : (Operand.reg 11 : Operand 64).read t7 =
      (memLoad t6.external (rspOf t6 + 11#64) 8).setWidth 64 := e7.writes
    rw [st6.scratch_address (offset := 11) (by decide), zero6] at h
    exact h
  have h7r0 : (Operand.reg 0 : Operand 8).read t7 = 0 := by
    change ((Operand.reg 0 : Operand 64).read t7).setWidth 8 = _
    rw [f7.read (r := 0) (n := 64) (by simp), f6.read (r := 0) (n := 64) (by simp), f5.read (r := 0) (n := 64) (by simp), f4.read (r := 0) (n := 64) (by simp), f3.read (r := 0) (n := 64) (by simp), f2.read (r := 0) (n := 64) (by simp), f1.read (r := 0) (n := 64) (by simp)]
    have h : (Operand.reg 0 : Operand 64).read t = 0 := state.rax
    rw [h]
    rfl
  obtain ⟨t8, run8, ready8, e8⟩ :=
    (mov_m8_r8_legacy_effect_step 0x109588 0 (by decide) (.sib 4 none 0 (.d8 13)) (by decide) rfl rfl).advances ready7
      (programText_slice (programLoaded_codeIn st7.loaded) 0x9588 _
        (by decide) (by decide +kernel))
      ⟨e7.rip, st7.scratch_byte_writable pre (offset := 13) (by decide),
        st7.scratch_code_apart pre (offset := 13) (codeOffset := 0x9588)
          (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x958c (by decide)))
  have ce8 : (storeEffect 0x109588 4 (storeAddrAt 0x109588 (.sib 4 none 0 (.d8 13)) 4) (fun u => (Operand.reg 0 : Operand 8).read u) t7).components = [.mem (rspOf t7 + 13#64) 1, .rip] := by
    simp [storeEffect_components, storeAddrAt, AddrMode.addr, AddrMode.reg64,
      Disp.value, rspOf, Operand.read]
  have f8 : AgreesExcept [.mem (rspOf t7 + 13#64) 1, .rip] t7 t8 := by
    have h := e8.agrees
    change AgreesExcept (storeEffect 0x109588 4 (storeAddrAt 0x109588 (.sib 4 none 0 (.d8 13)) 4) (fun u => (Operand.reg 0 : Operand 8).read u) t7).components t7 t8 at h
    rw [ce8] at h
    exact h
  have st8 := st7.of_effect pre run8 ready8 e8
    (by change ∀ c ∈ (storeEffect 0x109588 4 (storeAddrAt 0x109588 (.sib 4 none 0 (.d8 13)) 4) (fun u => (Operand.reg 0 : Operand 8).read u) t7).components, BodyComponent (rspOf t7) c
        rw [ce8]
        intro c hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl
        · exact ⟨13, rfl, by decide⟩
        · trivial)
    (by simp [storeEffect_components])
  have saved8 := (Store.byte_store_saved_pointer st7 (by decide) f8).trans saved7
  have zero8 : memLoad t8.external (stackPtr s - 59#64) 8 = 0 := by
    have h : memLoad t8.external (rspOf t7 + 13#64) 8 =
      (Operand.reg 0 : Operand 8).read t7 := e8.writes
    rw [st7.scratch_address (offset := 13) (by decide), h7r0] at h
    exact h
  obtain ⟨t9, run9, ready9, e9⟩ :=
    (lea_r64_effect_step 0x10958c 0x48 (by simp [RexWPrefix]) 3 (.sib 4 none 0 (.d8 13)) (by decide) rfl rfl).advances ready8
      (programText_slice (programLoaded_codeIn st8.loaded) 0x958c _
        (by decide) (by decide +kernel))
      e8.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x9591 (by decide)))
  have f9 : AgreesExcept [.reg 3, .rip] t8 t9 := e9.agrees
  have st9 := st8.of_effect pre run9 ready9 e9
    (by change ∀ c ∈ [.reg 3, .rip], BodyComponent (rspOf t8) c
        simp [BodyComponent])
    (by change Component.reg 4 ∉ [.reg 3, .rip]; simp)
  have mem9 : t9.external = t8.external := f9.external (by simp [Component.Covers])
  have saved9 : memLoad t9.external (stackPtr s - 56#64) 64 = s.regValue .rdi := by
    rw [mem9]
    exact saved8
  obtain ⟨t10, run10, ready10, e10⟩ :=
    (movzx_r32_m8_effect_step 0x109591 5 (.sib 4 none 0 (.d8 13)) (by decide) rfl rfl).advances ready9
      (programText_slice (programLoaded_codeIn st9.loaded) 0x9591 _
        (by decide) (by decide +kernel))
      ⟨e9.rip, st9.scratch_readable pre (offset := 13) (len := 1) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x9596 (by decide)))
  have f10 : AgreesExcept [.reg 5, .rip] t9 t10 := e10.agrees
  have st10 := st9.of_effect pre run10 ready10 e10
    (by change ∀ c ∈ [.reg 5, .rip], BodyComponent (rspOf t9) c
        simp [BodyComponent])
    (by change Component.reg 4 ∉ [.reg 5, .rip]; simp)
  have mem10 : t10.external = t9.external := f10.external (by simp [Component.Covers])
  have saved10 : memLoad t10.external (stackPtr s - 56#64) 64 = s.regValue .rdi := by
    rw [mem10]
    exact saved9
  have v10 : (Operand.reg 5 : Operand 64).read t10 = 0 := by
    have h : (Operand.reg 5 : Operand 64).read t10 =
      (memLoad t9.external (rspOf t9 + 13#64) 8).setWidth 64 := e10.writes
    rw [st9.scratch_address (offset := 13) (by decide), mem9, zero8] at h
    exact h
  have h10r2 : (Operand.reg 2 : Operand 64).read t10 = 0 := by
    rw [f10.read (r := 2) (n := 64) (by simp), f9.read (r := 2) (n := 64) (by simp), f8.read (r := 2) (n := 64) (by simp), f7.read (r := 2) (n := 64) (by simp), f6.read (r := 2) (n := 64) (by simp), f5.read (r := 2) (n := 64) (by simp), f4.read (r := 2) (n := 64) (by simp), f3.read (r := 2) (n := 64) (by simp), f2.read (r := 2) (n := 64) (by simp), f1.read (r := 2) (n := 64) (by simp)]
    exact state.rdx
  obtain ⟨t11, run11, ready11, e11⟩ :=
    (mov_r32_r32_effect_step 0x109596 0xd1 rfl).advances ready10
      (programText_slice (programLoaded_codeIn st10.loaded) 0x9596 _
        (by decide) (by decide +kernel))
      e10.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x9598 (by decide)))
  have f11 : AgreesExcept [.reg 1, .rip] t10 t11 := e11.agrees
  have st11 := st10.of_effect pre run11 ready11 e11
    (by change ∀ c ∈ [.reg 1, .rip], BodyComponent (rspOf t10) c
        simp [BodyComponent])
    (by change Component.reg 4 ∉ [.reg 1, .rip]; simp)
  have mem11 : t11.external = t10.external := f11.external (by simp [Component.Covers])
  have saved11 : memLoad t11.external (stackPtr s - 56#64) 64 = s.regValue .rdi := by
    rw [mem11]
    exact saved10
  have v11 : (Operand.reg 1 : Operand 64).read t11 = 0 := by
    have h : (Operand.reg 1 : Operand 64).read t11 =
      (((Operand.reg 2 : Operand 64).read t10).setWidth 32).setWidth 64 := e11.writes
    rw [h10r2] at h
    exact h
  have h11r1 : (Operand.reg 1 : Operand 64).read t11 = 0 := by
    exact v11
  obtain ⟨t12, run12, ready12, e12⟩ :=
    (shr_r32_imm8_effect_step 0x109598 0xe9 7 rfl rfl).advances ready11
      (programText_slice (programLoaded_codeIn st11.loaded) 0x9598 _
        (by decide) (by decide +kernel))
      e11.rip
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x959b (by decide)))
  have f12 : AgreesExcept [.reg 1, .flags, .rip] t11 t12 := e12.agrees
  have st12 := st11.of_effect pre run12 ready12 e12
    (by change ∀ c ∈ [.reg 1, .flags, .rip], BodyComponent (rspOf t11) c
        simp [BodyComponent])
    (by change Component.reg 4 ∉ [.reg 1, .flags, .rip]; simp)
  have mem12 : t12.external = t11.external := f12.external (by simp [Component.Covers])
  have saved12 : memLoad t12.external (stackPtr s - 56#64) 64 = s.regValue .rdi := by
    rw [mem12]
    exact saved11
  have v12 : (Operand.reg 1 : Operand 64).read t12 = 0 := by
    have h : (Operand.reg 1 : Operand 64).read t12 =
      ((((Operand.reg 1 : Operand 64).read t11).setWidth 32) >>> 7).setWidth 64 := e12.writes
    rw [h11r1] at h
    exact h
  have h12r1 : (Operand.reg 1 : Operand 8).read t12 = 0 := by
    change ((Operand.reg 1 : Operand 64).read t12).setWidth 8 = _
    have h : (Operand.reg 1 : Operand 64).read t12 = 0 := v12
    rw [h]
    rfl
  obtain ⟨t13, run13, ready13, e13⟩ :=
    (mov_m8_r8_legacy_effect_step 0x10959b 1 (by decide) (.sib 4 none 0 (.d8 11)) (by decide) rfl rfl).advances ready12
      (programText_slice (programLoaded_codeIn st12.loaded) 0x959b _
        (by decide) (by decide +kernel))
      ⟨e12.rip, st12.scratch_byte_writable pre (offset := 11) (by decide),
        st12.scratch_code_apart pre (offset := 11) (codeOffset := 0x959b)
          (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x959f (by decide)))
  have ce13 : (storeEffect 0x10959b 4 (storeAddrAt 0x10959b (.sib 4 none 0 (.d8 11)) 4) (fun u => (Operand.reg 1 : Operand 8).read u) t12).components = [.mem (rspOf t12 + 11#64) 1, .rip] := by
    simp [storeEffect_components, storeAddrAt, AddrMode.addr, AddrMode.reg64,
      Disp.value, rspOf, Operand.read]
  have f13 : AgreesExcept [.mem (rspOf t12 + 11#64) 1, .rip] t12 t13 := by
    have h := e13.agrees
    change AgreesExcept (storeEffect 0x10959b 4 (storeAddrAt 0x10959b (.sib 4 none 0 (.d8 11)) 4) (fun u => (Operand.reg 1 : Operand 8).read u) t12).components t12 t13 at h
    rw [ce13] at h
    exact h
  have st13 := st12.of_effect pre run13 ready13 e13
    (by change ∀ c ∈ (storeEffect 0x10959b 4 (storeAddrAt 0x10959b (.sib 4 none 0 (.d8 11)) 4) (fun u => (Operand.reg 1 : Operand 8).read u) t12).components, BodyComponent (rspOf t12) c
        rw [ce13]
        intro c hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl
        · exact ⟨11, rfl, by decide⟩
        · trivial)
    (by simp [storeEffect_components])
  have saved13 := (Store.byte_store_saved_pointer st12 (by decide) f13).trans saved12
  have zero13 : memLoad t13.external (stackPtr s - 61#64) 8 = 0 := by
    have h : memLoad t13.external (rspOf t12 + 11#64) 8 =
      (Operand.reg 1 : Operand 8).read t12 := e13.writes
    rw [st12.scratch_address (offset := 11) (by decide), h12r1] at h
    exact h
  obtain ⟨t14, run14, ready14, e14⟩ :=
    (movzx_r32_m8_effect_step 0x10959f 0 (.sib 4 none 0 (.d8 11)) (by decide) rfl rfl).advances ready13
      (programText_slice (programLoaded_codeIn st13.loaded) 0x959f _
        (by decide) (by decide +kernel))
      ⟨e13.rip, st13.scratch_readable pre (offset := 11) (len := 1) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x95a4 (by decide)))
  have f14 : AgreesExcept [.reg 0, .rip] t13 t14 := e14.agrees
  have st14 := st13.of_effect pre run14 ready14 e14
    (by change ∀ c ∈ [.reg 0, .rip], BodyComponent (rspOf t13) c
        simp [BodyComponent])
    (by change Component.reg 4 ∉ [.reg 0, .rip]; simp)
  have mem14 : t14.external = t13.external := f14.external (by simp [Component.Covers])
  have saved14 : memLoad t14.external (stackPtr s - 56#64) 64 = s.regValue .rdi := by
    rw [mem14]
    exact saved13
  have v14 : (Operand.reg 0 : Operand 64).read t14 = 0 := by
    have h : (Operand.reg 0 : Operand 64).read t14 =
      (memLoad t13.external (rspOf t13 + 11#64) 8).setWidth 64 := e14.writes
    rw [st13.scratch_address (offset := 11) (by decide), zero13] at h
    exact h
  have h14r1 : (Operand.reg 1 : Operand 8).read t14 = 0 := by
    change ((Operand.reg 1 : Operand 64).read t14).setWidth 8 = _
    rw [f14.read (r := 1) (n := 64) (by simp), f13.read (r := 1) (n := 64) (by simp)]
    have h : (Operand.reg 1 : Operand 64).read t12 = 0 := v12
    rw [h]
    rfl
  obtain ⟨t15, run15, ready15, e15⟩ :=
    (mov_m8_r8_legacy_effect_step 0x1095a4 1 (by decide) (.sib 4 none 0 (.d8 11)) (by decide) rfl rfl).advances ready14
      (programText_slice (programLoaded_codeIn st14.loaded) 0x95a4 _
        (by decide) (by decide +kernel))
      ⟨e14.rip, st14.scratch_byte_writable pre (offset := 11) (by decide),
        st14.scratch_code_apart pre (offset := 11) (codeOffset := 0x95a4)
          (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x95a8 (by decide)))
  have ce15 : (storeEffect 0x1095a4 4 (storeAddrAt 0x1095a4 (.sib 4 none 0 (.d8 11)) 4) (fun u => (Operand.reg 1 : Operand 8).read u) t14).components = [.mem (rspOf t14 + 11#64) 1, .rip] := by
    simp [storeEffect_components, storeAddrAt, AddrMode.addr, AddrMode.reg64,
      Disp.value, rspOf, Operand.read]
  have f15 : AgreesExcept [.mem (rspOf t14 + 11#64) 1, .rip] t14 t15 := by
    have h := e15.agrees
    change AgreesExcept (storeEffect 0x1095a4 4 (storeAddrAt 0x1095a4 (.sib 4 none 0 (.d8 11)) 4) (fun u => (Operand.reg 1 : Operand 8).read u) t14).components t14 t15 at h
    rw [ce15] at h
    exact h
  have st15 := st14.of_effect pre run15 ready15 e15
    (by change ∀ c ∈ (storeEffect 0x1095a4 4 (storeAddrAt 0x1095a4 (.sib 4 none 0 (.d8 11)) 4) (fun u => (Operand.reg 1 : Operand 8).read u) t14).components, BodyComponent (rspOf t14) c
        rw [ce15]
        intro c hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl
        · exact ⟨11, rfl, by decide⟩
        · trivial)
    (by simp [storeEffect_components])
  have saved15 := (Store.byte_store_saved_pointer st14 (by decide) f15).trans saved14
  have zero15 : memLoad t15.external (stackPtr s - 61#64) 8 = 0 := by
    have h : memLoad t15.external (rspOf t14 + 11#64) 8 =
      (Operand.reg 1 : Operand 8).read t14 := e15.writes
    rw [st14.scratch_address (offset := 11) (by decide), h14r1] at h
    exact h
  obtain ⟨t16, run16, ready16, e16⟩ :=
    (movzx_r32_m8_effect_step 0x1095a8 6 (.sib 4 none 0 (.d8 11)) (by decide) rfl rfl).advances ready15
      (programText_slice (programLoaded_codeIn st15.loaded) 0x95a8 _
        (by decide) (by decide +kernel))
      ⟨e15.rip, st15.scratch_readable pre (offset := 11) (len := 1) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x95ad (by decide)))
  have f16 : AgreesExcept [.reg 6, .rip] t15 t16 := e16.agrees
  have st16 := st15.of_effect pre run16 ready16 e16
    (by change ∀ c ∈ [.reg 6, .rip], BodyComponent (rspOf t15) c
        simp [BodyComponent])
    (by change Component.reg 4 ∉ [.reg 6, .rip]; simp)
  have mem16 : t16.external = t15.external := f16.external (by simp [Component.Covers])
  have saved16 : memLoad t16.external (stackPtr s - 56#64) 64 = s.regValue .rdi := by
    rw [mem16]
    exact saved15
  have v16 : (Operand.reg 6 : Operand 64).read t16 = 0 := by
    have h : (Operand.reg 6 : Operand 64).read t16 =
      (memLoad t15.external (rspOf t15 + 11#64) 8).setWidth 64 := e16.writes
    rw [st15.scratch_address (offset := 11) (by decide), zero15] at h
    exact h
  have h16r1 : (Operand.reg 1 : Operand 8).read t16 = 0 := by
    change ((Operand.reg 1 : Operand 64).read t16).setWidth 8 = _
    rw [f16.read (r := 1) (n := 64) (by simp), f15.read (r := 1) (n := 64) (by simp), f14.read (r := 1) (n := 64) (by simp), f13.read (r := 1) (n := 64) (by simp)]
    have h : (Operand.reg 1 : Operand 64).read t12 = 0 := v12
    rw [h]
    rfl
  obtain ⟨t17, run17, ready17, e17⟩ :=
    (mov_m8_r8_legacy_effect_step 0x1095ad 1 (by decide) (.sib 4 none 0 (.d8 13)) (by decide) rfl rfl).advances ready16
      (programText_slice (programLoaded_codeIn st16.loaded) 0x95ad _
        (by decide) (by decide +kernel))
      ⟨e16.rip, st16.scratch_byte_writable pre (offset := 13) (by decide),
        st16.scratch_code_apart pre (offset := 13) (codeOffset := 0x95ad)
          (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x95b1 (by decide)))
  have ce17 : (storeEffect 0x1095ad 4 (storeAddrAt 0x1095ad (.sib 4 none 0 (.d8 13)) 4) (fun u => (Operand.reg 1 : Operand 8).read u) t16).components = [.mem (rspOf t16 + 13#64) 1, .rip] := by
    simp [storeEffect_components, storeAddrAt, AddrMode.addr, AddrMode.reg64,
      Disp.value, rspOf, Operand.read]
  have f17 : AgreesExcept [.mem (rspOf t16 + 13#64) 1, .rip] t16 t17 := by
    have h := e17.agrees
    change AgreesExcept (storeEffect 0x1095ad 4 (storeAddrAt 0x1095ad (.sib 4 none 0 (.d8 13)) 4) (fun u => (Operand.reg 1 : Operand 8).read u) t16).components t16 t17 at h
    rw [ce17] at h
    exact h
  have st17 := st16.of_effect pre run17 ready17 e17
    (by change ∀ c ∈ (storeEffect 0x1095ad 4 (storeAddrAt 0x1095ad (.sib 4 none 0 (.d8 13)) 4) (fun u => (Operand.reg 1 : Operand 8).read u) t16).components, BodyComponent (rspOf t16) c
        rw [ce17]
        intro c hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl
        · exact ⟨13, rfl, by decide⟩
        · trivial)
    (by simp [storeEffect_components])
  have saved17 := (Store.byte_store_saved_pointer st16 (by decide) f17).trans saved16
  have zero17 : memLoad t17.external (stackPtr s - 59#64) 8 = 0 := by
    have h : memLoad t17.external (rspOf t16 + 13#64) 8 =
      (Operand.reg 1 : Operand 8).read t16 := e17.writes
    rw [st16.scratch_address (offset := 13) (by decide), h16r1] at h
    exact h
  obtain ⟨t18, run18, ready18, e18⟩ :=
    (movzx_r_m8_rex_effect_step 0x1095b1 0x44 (by simp [RexPrefix]) 32 (.inr rfl) (fun _ => rfl) 0 (.sib 4 none 0 (.d8 13)) (by decide) rfl rfl).advances ready17
      (programText_slice (programLoaded_codeIn st17.loaded) 0x95b1 _
        (by decide) (by decide +kernel))
      ⟨e17.rip, st17.scratch_readable pre (offset := 13) (len := 1) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x95b7 (by decide)))
  have f18 : AgreesExcept [.reg 8, .rip] t17 t18 := e18.agrees
  have st18 := st17.of_effect pre run18 ready18 e18
    (by change ∀ c ∈ [.reg 8, .rip], BodyComponent (rspOf t17) c
        simp [BodyComponent])
    (by change Component.reg 4 ∉ [.reg 8, .rip]; simp)
  have mem18 : t18.external = t17.external := f18.external (by simp [Component.Covers])
  have saved18 : memLoad t18.external (stackPtr s - 56#64) 64 = s.regValue .rdi := by
    rw [mem18]
    exact saved17
  have v18 : (Operand.reg 8 : Operand 64).read t18 = 0 := by
    have h : (Operand.reg 8 : Operand 64).read t18 =
      (memLoad t17.external (rspOf t17 + 13#64) 8).setWidth 64 := e18.writes
    rw [st17.scratch_address (offset := 13) (by decide), zero17] at h
    exact h
  have h18r1 : (Operand.reg 1 : Operand 8).read t18 = 0 := by
    change ((Operand.reg 1 : Operand 64).read t18).setWidth 8 = _
    rw [f18.read (r := 1) (n := 64) (by simp), f17.read (r := 1) (n := 64) (by simp), f16.read (r := 1) (n := 64) (by simp), f15.read (r := 1) (n := 64) (by simp), f14.read (r := 1) (n := 64) (by simp), f13.read (r := 1) (n := 64) (by simp)]
    have h : (Operand.reg 1 : Operand 64).read t12 = 0 := v12
    rw [h]
    rfl
  obtain ⟨t19, run19, ready19, e19⟩ :=
    (mov_m8_r8_legacy_effect_step 0x1095b7 1 (by decide) (.sib 4 none 0 (.d8 13)) (by decide) rfl rfl).advances ready18
      (programText_slice (programLoaded_codeIn st18.loaded) 0x95b7 _
        (by decide) (by decide +kernel))
      ⟨e18.rip, st18.scratch_byte_writable pre (offset := 13) (by decide),
        st18.scratch_code_apart pre (offset := 13) (codeOffset := 0x95b7)
          (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x95bb (by decide)))
  have ce19 : (storeEffect 0x1095b7 4 (storeAddrAt 0x1095b7 (.sib 4 none 0 (.d8 13)) 4) (fun u => (Operand.reg 1 : Operand 8).read u) t18).components = [.mem (rspOf t18 + 13#64) 1, .rip] := by
    simp [storeEffect_components, storeAddrAt, AddrMode.addr, AddrMode.reg64,
      Disp.value, rspOf, Operand.read]
  have f19 : AgreesExcept [.mem (rspOf t18 + 13#64) 1, .rip] t18 t19 := by
    have h := e19.agrees
    change AgreesExcept (storeEffect 0x1095b7 4 (storeAddrAt 0x1095b7 (.sib 4 none 0 (.d8 13)) 4) (fun u => (Operand.reg 1 : Operand 8).read u) t18).components t18 t19 at h
    rw [ce19] at h
    exact h
  have st19 := st18.of_effect pre run19 ready19 e19
    (by change ∀ c ∈ (storeEffect 0x1095b7 4 (storeAddrAt 0x1095b7 (.sib 4 none 0 (.d8 13)) 4) (fun u => (Operand.reg 1 : Operand 8).read u) t18).components, BodyComponent (rspOf t18) c
        rw [ce19]
        intro c hc
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl
        · exact ⟨13, rfl, by decide⟩
        · trivial)
    (by simp [storeEffect_components])
  have saved19 := (Store.byte_store_saved_pointer st18 (by decide) f19).trans saved18
  have zero19 : memLoad t19.external (stackPtr s - 59#64) 8 = 0 := by
    have h : memLoad t19.external (rspOf t18 + 13#64) 8 =
      (Operand.reg 1 : Operand 8).read t18 := e19.writes
    rw [st18.scratch_address (offset := 13) (by decide), h18r1] at h
    exact h
  obtain ⟨t20, run20, ready20, e20⟩ :=
    (movzx_r32_m8_effect_step 0x1095bb 3 (.sib 4 none 0 (.d8 13)) (by decide) rfl rfl).advances ready19
      (programText_slice (programLoaded_codeIn st19.loaded) 0x95bb _
        (by decide) (by decide +kernel))
      ⟨e19.rip, st19.scratch_readable pre (offset := 13) (len := 1) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x95c0 (by decide)))
  have f20 : AgreesExcept [.reg 3, .rip] t19 t20 := e20.agrees
  have st20 := st19.of_effect pre run20 ready20 e20
    (by change ∀ c ∈ [.reg 3, .rip], BodyComponent (rspOf t19) c
        simp [BodyComponent])
    (by change Component.reg 4 ∉ [.reg 3, .rip]; simp)
  have mem20 : t20.external = t19.external := f20.external (by simp [Component.Covers])
  have saved20 : memLoad t20.external (stackPtr s - 56#64) 64 = s.regValue .rdi := by
    rw [mem20]
    exact saved19
  have v20 : (Operand.reg 3 : Operand 64).read t20 = 0 := by
    have h : (Operand.reg 3 : Operand 64).read t20 =
      (memLoad t19.external (rspOf t19 + 13#64) 8).setWidth 64 := e20.writes
    rw [st19.scratch_address (offset := 13) (by decide), zero19] at h
    exact h
  have h20r2 : (Operand.reg 2 : Operand 64).read t20 = 0 := by
    rw [f20.read (r := 2) (n := 64) (by simp), f19.read (r := 2) (n := 64) (by simp), f18.read (r := 2) (n := 64) (by simp), f17.read (r := 2) (n := 64) (by simp), f16.read (r := 2) (n := 64) (by simp), f15.read (r := 2) (n := 64) (by simp), f14.read (r := 2) (n := 64) (by simp), f13.read (r := 2) (n := 64) (by simp), f12.read (r := 2) (n := 64) (by simp), f11.read (r := 2) (n := 64) (by simp), f10.read (r := 2) (n := 64) (by simp), f9.read (r := 2) (n := 64) (by simp), f8.read (r := 2) (n := 64) (by simp), f7.read (r := 2) (n := 64) (by simp), f6.read (r := 2) (n := 64) (by simp), f5.read (r := 2) (n := 64) (by simp), f4.read (r := 2) (n := 64) (by simp), f3.read (r := 2) (n := 64) (by simp), f2.read (r := 2) (n := 64) (by simp), f1.read (r := 2) (n := 64) (by simp)]
    exact state.rdx
  have h20r13 : (Operand.reg 13 : Operand 64).read t20 = a.l3 := by
    rw [f20.read (r := 13) (n := 64) (by simp), f19.read (r := 13) (n := 64) (by simp), f18.read (r := 13) (n := 64) (by simp), f17.read (r := 13) (n := 64) (by simp), f16.read (r := 13) (n := 64) (by simp), f15.read (r := 13) (n := 64) (by simp), f14.read (r := 13) (n := 64) (by simp), f13.read (r := 13) (n := 64) (by simp), f12.read (r := 13) (n := 64) (by simp), f11.read (r := 13) (n := 64) (by simp), f10.read (r := 13) (n := 64) (by simp), f9.read (r := 13) (n := 64) (by simp), f8.read (r := 13) (n := 64) (by simp), f7.read (r := 13) (n := 64) (by simp), f6.read (r := 13) (n := 64) (by simp), f5.read (r := 13) (n := 64) (by simp), f4.read (r := 13) (n := 64) (by simp), f3.read (r := 13) (n := 64) (by simp), f2.read (r := 13) (n := 64) (by simp), f1.read (r := 13) (n := 64) (by simp)]
    exact state.r13
  have h20r15 : (Operand.reg 15 : Operand 64).read t20 = a.l2 := by
    rw [f20.read (r := 15) (n := 64) (by simp), f19.read (r := 15) (n := 64) (by simp), f18.read (r := 15) (n := 64) (by simp), f17.read (r := 15) (n := 64) (by simp), f16.read (r := 15) (n := 64) (by simp), f15.read (r := 15) (n := 64) (by simp), f14.read (r := 15) (n := 64) (by simp), f13.read (r := 15) (n := 64) (by simp), f12.read (r := 15) (n := 64) (by simp), f11.read (r := 15) (n := 64) (by simp), f10.read (r := 15) (n := 64) (by simp), f9.read (r := 15) (n := 64) (by simp), f8.read (r := 15) (n := 64) (by simp), f7.read (r := 15) (n := 64) (by simp), f6.read (r := 15) (n := 64) (by simp), f5.read (r := 15) (n := 64) (by simp), f4.read (r := 15) (n := 64) (by simp), f3.read (r := 15) (n := 64) (by simp), f2.read (r := 15) (n := 64) (by simp), f1.read (r := 15) (n := 64) (by simp)]
    exact state.r15
  have h20r10 : (Operand.reg 10 : Operand 64).read t20 = a.l0 := by
    rw [f20.read (r := 10) (n := 64) (by simp), f19.read (r := 10) (n := 64) (by simp), f18.read (r := 10) (n := 64) (by simp), f17.read (r := 10) (n := 64) (by simp), f16.read (r := 10) (n := 64) (by simp), f15.read (r := 10) (n := 64) (by simp), f14.read (r := 10) (n := 64) (by simp), f13.read (r := 10) (n := 64) (by simp), f12.read (r := 10) (n := 64) (by simp), f11.read (r := 10) (n := 64) (by simp), f10.read (r := 10) (n := 64) (by simp), f9.read (r := 10) (n := 64) (by simp), f8.read (r := 10) (n := 64) (by simp), f7.read (r := 10) (n := 64) (by simp), f6.read (r := 10) (n := 64) (by simp), f5.read (r := 10) (n := 64) (by simp), f4.read (r := 10) (n := 64) (by simp), f3.read (r := 10) (n := 64) (by simp), f2.read (r := 10) (n := 64) (by simp), f1.read (r := 10) (n := 64) (by simp)]
    exact state.r10
  have h20r14 : (Operand.reg 14 : Operand 64).read t20 = a.l1 := by
    rw [f20.read (r := 14) (n := 64) (by simp), f19.read (r := 14) (n := 64) (by simp), f18.read (r := 14) (n := 64) (by simp), f17.read (r := 14) (n := 64) (by simp), f16.read (r := 14) (n := 64) (by simp), f15.read (r := 14) (n := 64) (by simp), f14.read (r := 14) (n := 64) (by simp), f13.read (r := 14) (n := 64) (by simp), f12.read (r := 14) (n := 64) (by simp), f11.read (r := 14) (n := 64) (by simp), f10.read (r := 14) (n := 64) (by simp), f9.read (r := 14) (n := 64) (by simp), f8.read (r := 14) (n := 64) (by simp), f7.read (r := 14) (n := 64) (by simp), f6.read (r := 14) (n := 64) (by simp), f5.read (r := 14) (n := 64) (by simp), f4.read (r := 14) (n := 64) (by simp), f3.read (r := 14) (n := 64) (by simp), f2.read (r := 14) (n := 64) (by simp), f1.read (r := 14) (n := 64) (by simp)]
    exact state.r14
  have h20r9 : (Operand.reg 9 : Operand 64).read t20 = 0 := by
    rw [f20.read (r := 9) (n := 64) (by simp), f19.read (r := 9) (n := 64) (by simp), f18.read (r := 9) (n := 64) (by simp), f17.read (r := 9) (n := 64) (by simp), f16.read (r := 9) (n := 64) (by simp), f15.read (r := 9) (n := 64) (by simp), f14.read (r := 9) (n := 64) (by simp), f13.read (r := 9) (n := 64) (by simp), f12.read (r := 9) (n := 64) (by simp), f11.read (r := 9) (n := 64) (by simp), f10.read (r := 9) (n := 64) (by simp), f9.read (r := 9) (n := 64) (by simp), f8.read (r := 9) (n := 64) (by simp), f7.read (r := 9) (n := 64) (by simp), f6.read (r := 9) (n := 64) (by simp), f5.read (r := 9) (n := 64) (by simp), f4.read (r := 9) (n := 64) (by simp)]
    exact v3
  have h20r12 : (Operand.reg 12 : Operand 64).read t20 = 0 := by
    rw [f20.read (r := 12) (n := 64) (by simp), f19.read (r := 12) (n := 64) (by simp), f18.read (r := 12) (n := 64) (by simp), f17.read (r := 12) (n := 64) (by simp), f16.read (r := 12) (n := 64) (by simp), f15.read (r := 12) (n := 64) (by simp), f14.read (r := 12) (n := 64) (by simp), f13.read (r := 12) (n := 64) (by simp), f12.read (r := 12) (n := 64) (by simp), f11.read (r := 12) (n := 64) (by simp), f10.read (r := 12) (n := 64) (by simp), f9.read (r := 12) (n := 64) (by simp), f8.read (r := 12) (n := 64) (by simp), f7.read (r := 12) (n := 64) (by simp), f6.read (r := 12) (n := 64) (by simp)]
    exact v5
  have h20r11 : (Operand.reg 11 : Operand 64).read t20 = 0 := by
    rw [f20.read (r := 11) (n := 64) (by simp), f19.read (r := 11) (n := 64) (by simp), f18.read (r := 11) (n := 64) (by simp), f17.read (r := 11) (n := 64) (by simp), f16.read (r := 11) (n := 64) (by simp), f15.read (r := 11) (n := 64) (by simp), f14.read (r := 11) (n := 64) (by simp), f13.read (r := 11) (n := 64) (by simp), f12.read (r := 11) (n := 64) (by simp), f11.read (r := 11) (n := 64) (by simp), f10.read (r := 11) (n := 64) (by simp), f9.read (r := 11) (n := 64) (by simp), f8.read (r := 11) (n := 64) (by simp)]
    exact v7
  have h20r5 : (Operand.reg 5 : Operand 64).read t20 = 0 := by
    rw [f20.read (r := 5) (n := 64) (by simp), f19.read (r := 5) (n := 64) (by simp), f18.read (r := 5) (n := 64) (by simp), f17.read (r := 5) (n := 64) (by simp), f16.read (r := 5) (n := 64) (by simp), f15.read (r := 5) (n := 64) (by simp), f14.read (r := 5) (n := 64) (by simp), f13.read (r := 5) (n := 64) (by simp), f12.read (r := 5) (n := 64) (by simp), f11.read (r := 5) (n := 64) (by simp)]
    exact v10
  have h20r0 : (Operand.reg 0 : Operand 64).read t20 = 0 := by
    rw [f20.read (r := 0) (n := 64) (by simp), f19.read (r := 0) (n := 64) (by simp), f18.read (r := 0) (n := 64) (by simp), f17.read (r := 0) (n := 64) (by simp), f16.read (r := 0) (n := 64) (by simp), f15.read (r := 0) (n := 64) (by simp)]
    exact v14
  have h20r6 : (Operand.reg 6 : Operand 64).read t20 = 0 := by
    rw [f20.read (r := 6) (n := 64) (by simp), f19.read (r := 6) (n := 64) (by simp), f18.read (r := 6) (n := 64) (by simp), f17.read (r := 6) (n := 64) (by simp)]
    exact v16
  have h20r8 : (Operand.reg 8 : Operand 64).read t20 = 0 := by
    rw [f20.read (r := 8) (n := 64) (by simp), f19.read (r := 8) (n := 64) (by simp)]
    exact v18
  have h20r3 : (Operand.reg 3 : Operand 64).read t20 = 0 := by
    exact v20
  exact ⟨t20, st20, e20.rip, saved20, h20r2, h20r13, h20r15, h20r10, h20r14, h20r9, h20r12, h20r11, h20r5, h20r0, h20r6, h20r8, h20r3⟩

end P256.Proofs.Nonce.Initialize.Conversions.ShiftZero
