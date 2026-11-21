import P256.Proofs.Projective.Double.CrossTerms.PairProducts
set_option autoImplicit false


namespace P256.Proofs.Projective.Double

variable {inputRegister : X86.Syntax.Reg}

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Program.FieldCall P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open CrossTerms

theorem cross_terms_correct [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {point : Projective} (pre : CalleePre s boundary 0x105d80 0 96 1016 inputRegister)
    (state : FrameState s t 96 1016 728) (rip : t.RIP = 0x105dc3)
    (input : SquaresAt s t point) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u 96 1016 728 ∧
      u.RIP = 0x105fd1 ∧ CrossTermsAt s u point := by
  let delta := Standards.SECG.ECC.Curve.fieldSub P256.Spec.Operations.domain.p
    (P256.Spec.Operations.domain.b * (values point).zz % P256.Spec.Operations.domain.p) (values point).xz2
  obtain ⟨n8, t8, run8, frame8, rip8, pair⟩ := pair_products_correct pre state rip input
  have point8 := pair.pointAt
  have reg8_3 := pair.rbx
  have reg8_14 : t8.regValue .r14 = stackSlot s 552 := by
    have h := pair.r14
    rw [stackSlot_eq s (by decide)]
    exact h
  have mem8_104 : MontgomeryAt t8 (stackSlot s 104) (values point).xx := by
    have h := pair.xx
    rw [stackSlot_eq s (by decide)]
    exact h
  have mem8_136 : MontgomeryAt t8 (stackSlot s 136) (values point).yy := by
    have h := pair.yy
    rw [stackSlot_eq s (by decide)]
    exact h
  have mem8_168 : MontgomeryAt t8 (stackSlot s 168) (values point).zz := by
    have h := pair.zz
    rw [stackSlot_eq s (by decide)]
    exact h
  have mem8_552 : MontgomeryAt t8 (stackSlot s 552) (values point).xy2 := by
    have h := pair.xy2
    rw [stackSlot_eq s (by decide)]
    exact h
  have mem8_72 : MontgomeryAt t8 (stackSlot s 72) (point.x * point.z % P256.Spec.Operations.domain.p) := by
    have h := pair.xz
    rw [stackSlot_eq s (by decide)]
    exact h
  have mem8_200 : MontgomeryAt t8 (stackSlot s 200) (values point).xz2 := by
    have h := pair.xz2
    rw [stackSlot_eq s (by decide)]
    exact h
  obtain ⟨t9, run9, frame9, rip9, frameScratch9, arg9_5, arg9_15, arg9_6, arg9_2, arg9_7, word9_8, word9_16, word9_24, word9_32, word9_40, word9_48, word9_56, word9_64⟩ :=
    bZZ pre frame8 rip8
  have reg9_3 : t9.regValue .rbx = s.regValue .rdi :=
    (frameScratch9.read (n := 64) (r := 3) (by simp [scratchComponents])).trans reg8_3
  have reg9_14 : t9.regValue .r14 = stackSlot s 552 :=
    (frameScratch9.read (n := 64) (r := 14) (by simp [scratchComponents])).trans reg8_14
  have reg9_5 : t9.regValue .rbp = 0xd89cdf6229c4bddf := arg9_5
  have reg9_15 : t9.regValue .r15 = stackSlot s 72 := arg9_15
  have reg9_6 : t9.regValue .rsi = stackSlot s 8 := arg9_6
  have reg9_2 : t9.regValue .rdx = stackSlot s 40 := arg9_2
  have reg9_7 : t9.regValue .rdi = stackSlot s 72 := arg9_7
  have point9 := scratch_point pre frameScratch9 (by decide) point8
  have mem9_104 : MontgomeryAt t9 (stackSlot s 104) ((values point).xx) :=
    scratch_montgomery frameScratch9 (slots_apart (by decide) (by decide) (by decide)) mem8_104
  have mem9_136 : MontgomeryAt t9 (stackSlot s 136) ((values point).yy) :=
    scratch_montgomery frameScratch9 (slots_apart (by decide) (by decide) (by decide)) mem8_136
  have mem9_168 : MontgomeryAt t9 (stackSlot s 168) ((values point).zz) :=
    scratch_montgomery frameScratch9 (slots_apart (by decide) (by decide) (by decide)) mem8_168
  have mem9_72 : MontgomeryAt t9 (stackSlot s 72) ((point.x*point.z) % P256.Spec.Operations.domain.p) :=
    scratch_montgomery frameScratch9 (slots_apart (by decide) (by decide) (by decide)) mem8_72
  have mem9_552 : MontgomeryAt t9 (stackSlot s 552) ((values point).xy2) :=
    scratch_montgomery frameScratch9 (slots_apart (by decide) (by decide) (by decide)) mem8_552
  have mem9_200 : MontgomeryAt t9 (stackSlot s 200) ((values point).xz2) :=
    scratch_montgomery frameScratch9 (slots_apart (by decide) (by decide) (by decide)) mem8_200
  have mem9_8 : MontgomeryAt t9 (stackSlot s 8) P256.Spec.Operations.domain.b := by
    apply montgomeryAt_coefficient_b
    · have allocated := stack_readable (frameOffset := 728) pre frame9
        (offset := 8) (len := 32) (by decide) (by decide)
      rw [frame9.rsp] at allocated
      exact allocated.mem
    · exact word9_8
    · simpa only [show stackSlot s 8 + 8 = stackSlot s 16 from slot_add s 8 8] using word9_16
    · simpa only [show stackSlot s 8 + 16 = stackSlot s 24 from slot_add s 8 16] using word9_24
    · simpa only [show stackSlot s 8 + 24 = stackSlot s 32 from slot_add s 8 24] using word9_32
  have mem9_40 : MontgomeryAt t9 (stackSlot s 40) ((values point).zz) := by
    apply copied (dst := 40) pre frame9 (by decide) mem8_168
    · exact word9_40
    · change memLoad t9.external (stackSlot s 48) 64 =
        memLoad t8.external (stackSlot s 168 + BitVec.ofNat 64 8) 64
      rw [slot_add]
      exact word9_48
    · change memLoad t9.external (stackSlot s 56) 64 =
        memLoad t8.external (stackSlot s 168 + BitVec.ofNat 64 16) 64
      rw [slot_add]
      exact word9_56
    · change memLoad t9.external (stackSlot s 64) 64 =
        memLoad t8.external (stackSlot s 168 + BitVec.ofNat 64 24) 64
      rw [slot_add]
      exact word9_64
  have input9_6 : t9.regValue .rsi = stackPtr s - BitVec.ofNat 64 720 := by
    have h := reg9_6
    rw [stackSlot_eq s (by decide)] at h
    exact h
  have input9_7 : t9.regValue .rdi = stackPtr s - BitVec.ofNat 64 656 := by
    have h := reg9_7
    rw [stackSlot_eq s (by decide)] at h
    exact h
  have input9_2 : t9.regValue .rdx = stackPtr s - BitVec.ofNat 64 688 := by
    have h := reg9_2
    rw [stackSlot_eq s (by decide)] at h
    exact h
  have value9_8 : MontgomeryAt t9 (stackPtr s - BitVec.ofNat 64 720) (P256.Spec.Operations.domain.b) := by
    have h := mem9_8
    rw [stackSlot_eq s (by decide)] at h
    exact h
  have value9_40 : MontgomeryAt t9 (stackPtr s - BitVec.ofNat 64 688) ((values point).zz) := by
    have h := mem9_40
    rw [stackSlot_eq s (by decide)] at h
    exact h
  obtain ⟨n10, t10, run10, frame10, rip10, value10, regs10, bytes10, work10⟩ :=
    binary_call pre frame9 mulBZZSite (op := fun x y => x*y % P256.Spec.Operations.domain.p)
      (fun _ hp hx hy => field_mul_correct hp hx hy) rip9
      input9_6 input9_2 input9_7 value9_8 value9_40
  have point10 := point_of_stack pre (work_stack_frame pre work10) point9
  have reg10_3 : t10.regValue .rbx = s.regValue .rdi :=
    (regs10 .rbx (by decide)).trans reg9_3
  have reg10_15 : t10.regValue .r15 = stackSlot s 72 :=
    (regs10 .r15 (by decide)).trans reg9_15
  have reg10_14 : t10.regValue .r14 = stackSlot s 552 :=
    (regs10 .r14 (by decide)).trans reg9_14
  have reg10_5 : t10.regValue .rbp = 0xd89cdf6229c4bddf :=
    (regs10 .rbp (by decide)).trans reg9_5
  have mem10_104 : MontgomeryAt t10 (stackSlot s 104) ((values point).xx) := by
    have h := mem9_104
    rw [stackSlot_eq s (by decide)] at h ⊢
    exact ⟨h.1, h.2.1, fun i hi => (bytes10 624 32 (by decide) (by decide) (by decide) i hi).trans (h.2.2 i hi)⟩
  have mem10_136 : MontgomeryAt t10 (stackSlot s 136) ((values point).yy) := by
    have h := mem9_136
    rw [stackSlot_eq s (by decide)] at h ⊢
    exact ⟨h.1, h.2.1, fun i hi => (bytes10 592 32 (by decide) (by decide) (by decide) i hi).trans (h.2.2 i hi)⟩
  have mem10_168 : MontgomeryAt t10 (stackSlot s 168) ((values point).zz) := by
    have h := mem9_168
    rw [stackSlot_eq s (by decide)] at h ⊢
    exact ⟨h.1, h.2.1, fun i hi => (bytes10 560 32 (by decide) (by decide) (by decide) i hi).trans (h.2.2 i hi)⟩
  have mem10_552 : MontgomeryAt t10 (stackSlot s 552) ((values point).xy2) := by
    have h := mem9_552
    rw [stackSlot_eq s (by decide)] at h ⊢
    exact ⟨h.1, h.2.1, fun i hi => (bytes10 176 32 (by decide) (by decide) (by decide) i hi).trans (h.2.2 i hi)⟩
  have mem10_200 : MontgomeryAt t10 (stackSlot s 200) ((values point).xz2) := by
    have h := mem9_200
    rw [stackSlot_eq s (by decide)] at h ⊢
    exact ⟨h.1, h.2.1, fun i hi => (bytes10 528 32 (by decide) (by decide) (by decide) i hi).trans (h.2.2 i hi)⟩
  have mem10_8 : MontgomeryAt t10 (stackSlot s 8) (P256.Spec.Operations.domain.b) := by
    have h := mem9_8
    rw [stackSlot_eq s (by decide)] at h ⊢
    exact ⟨h.1, h.2.1, fun i hi => (bytes10 720 32 (by decide) (by decide) (by decide) i hi).trans (h.2.2 i hi)⟩
  have mem10_40 : MontgomeryAt t10 (stackSlot s 40) ((values point).zz) := by
    have h := mem9_40
    rw [stackSlot_eq s (by decide)] at h ⊢
    exact ⟨h.1, h.2.1, fun i hi => (bytes10 688 32 (by decide) (by decide) (by decide) i hi).trans (h.2.2 i hi)⟩
  have mem10_72 : MontgomeryAt t10 (stackSlot s 72) ((P256.Spec.Operations.domain.b*(values point).zz) % P256.Spec.Operations.domain.p) := by
    rw [stackSlot_eq s (by decide)]
    exact value10
  obtain ⟨t11, run11, frame11, rip11, frameScratch11, arg11_12, arg11_2, arg11_7, arg11_6, word11_8, word11_16, word11_24, word11_32⟩ :=
    subtract pre frame10 rip10
  have reg11_3 : t11.regValue .rbx = s.regValue .rdi :=
    (frameScratch11.read (n := 64) (r := 3) (by simp [scratchComponents])).trans reg10_3
  have reg11_15 : t11.regValue .r15 = stackSlot s 72 :=
    (frameScratch11.read (n := 64) (r := 15) (by simp [scratchComponents])).trans reg10_15
  have reg11_14 : t11.regValue .r14 = stackSlot s 552 :=
    (frameScratch11.read (n := 64) (r := 14) (by simp [scratchComponents])).trans reg10_14
  have reg11_5 : t11.regValue .rbp = 0xd89cdf6229c4bddf :=
    (frameScratch11.read (n := 64) (r := 5) (by simp [scratchComponents])).trans reg10_5
  have reg11_12 : t11.regValue .r12 = stackSlot s 264 := arg11_12
  have reg11_2 : t11.regValue .rdx = stackSlot s 8 := arg11_2
  have reg11_7 : t11.regValue .rdi = stackSlot s 264 := arg11_7
  have reg11_6 : t11.regValue .rsi = stackSlot s 72 := arg11_6.trans reg10_15
  have point11 := scratch_point pre frameScratch11 (by decide) point10
  have mem11_104 : MontgomeryAt t11 (stackSlot s 104) ((values point).xx) :=
    scratch_montgomery frameScratch11 (slots_apart (by decide) (by decide) (by decide)) mem10_104
  have mem11_136 : MontgomeryAt t11 (stackSlot s 136) ((values point).yy) :=
    scratch_montgomery frameScratch11 (slots_apart (by decide) (by decide) (by decide)) mem10_136
  have mem11_168 : MontgomeryAt t11 (stackSlot s 168) ((values point).zz) :=
    scratch_montgomery frameScratch11 (slots_apart (by decide) (by decide) (by decide)) mem10_168
  have mem11_72 : MontgomeryAt t11 (stackSlot s 72) ((P256.Spec.Operations.domain.b*(values point).zz) % P256.Spec.Operations.domain.p) :=
    scratch_montgomery frameScratch11 (slots_apart (by decide) (by decide) (by decide)) mem10_72
  have mem11_552 : MontgomeryAt t11 (stackSlot s 552) ((values point).xy2) :=
    scratch_montgomery frameScratch11 (slots_apart (by decide) (by decide) (by decide)) mem10_552
  have mem11_200 : MontgomeryAt t11 (stackSlot s 200) ((values point).xz2) :=
    scratch_montgomery frameScratch11 (slots_apart (by decide) (by decide) (by decide)) mem10_200
  have mem11_40 : MontgomeryAt t11 (stackSlot s 40) ((values point).zz) :=
    scratch_montgomery frameScratch11 (slots_apart (by decide) (by decide) (by decide)) mem10_40
  have mem11_8 : MontgomeryAt t11 (stackSlot s 8) ((values point).xz2) := by
    apply copied (dst := 8) pre frame11 (by decide) mem10_200
    · exact word11_8
    · change memLoad t11.external (stackSlot s 16) 64 =
        memLoad t10.external (stackSlot s 200 + BitVec.ofNat 64 8) 64
      rw [slot_add]
      exact word11_16
    · change memLoad t11.external (stackSlot s 24) 64 =
        memLoad t10.external (stackSlot s 200 + BitVec.ofNat 64 16) 64
      rw [slot_add]
      exact word11_24
    · change memLoad t11.external (stackSlot s 32) 64 =
        memLoad t10.external (stackSlot s 200 + BitVec.ofNat 64 24) 64
      rw [slot_add]
      exact word11_32
  have input11_6 : t11.regValue .rsi = stackPtr s - BitVec.ofNat 64 656 := by
    have h := reg11_6
    rw [stackSlot_eq s (by decide)] at h
    exact h
  have input11_7 : t11.regValue .rdi = stackPtr s - BitVec.ofNat 64 464 := by
    have h := reg11_7
    rw [stackSlot_eq s (by decide)] at h
    exact h
  have input11_2 : t11.regValue .rdx = stackPtr s - BitVec.ofNat 64 720 := by
    have h := reg11_2
    rw [stackSlot_eq s (by decide)] at h
    exact h
  have value11_72 : MontgomeryAt t11 (stackPtr s - BitVec.ofNat 64 656) ((P256.Spec.Operations.domain.b*(values point).zz) % P256.Spec.Operations.domain.p) := by
    have h := mem11_72
    rw [stackSlot_eq s (by decide)] at h
    exact h
  have value11_8 : MontgomeryAt t11 (stackPtr s - BitVec.ofNat 64 720) ((values point).xz2) := by
    have h := mem11_8
    rw [stackSlot_eq s (by decide)] at h
    exact h
  obtain ⟨n12, t12, run12, frame12, rip12, value12, regs12, bytes12, work12⟩ :=
    binary_call pre frame11 differenceSite (op := Standards.SECG.ECC.Curve.fieldSub P256.Spec.Operations.domain.p)
      (fun _ hp hx hy => by simpa only [Standards.SECG.ECC.Curve.fieldSub, Nat.mod_eq_of_lt hx.1, Nat.mod_eq_of_lt hy.1] using field_subtract_correct hp hx hy) rip11
      input11_6 input11_2 input11_7 value11_72 value11_8
  have point12 := point_of_stack pre (work_stack_frame pre work12) point11
  have reg12_3 : t12.regValue .rbx = s.regValue .rdi :=
    (regs12 .rbx (by decide)).trans reg11_3
  have reg12_15 : t12.regValue .r15 = stackSlot s 72 :=
    (regs12 .r15 (by decide)).trans reg11_15
  have reg12_14 : t12.regValue .r14 = stackSlot s 552 :=
    (regs12 .r14 (by decide)).trans reg11_14
  have reg12_5 : t12.regValue .rbp = 0xd89cdf6229c4bddf :=
    (regs12 .rbp (by decide)).trans reg11_5
  have reg12_12 : t12.regValue .r12 = stackSlot s 264 :=
    (regs12 .r12 (by decide)).trans reg11_12
  have mem12_104 : MontgomeryAt t12 (stackSlot s 104) ((values point).xx) := by
    have h := mem11_104
    rw [stackSlot_eq s (by decide)] at h ⊢
    exact ⟨h.1, h.2.1, fun i hi => (bytes12 624 32 (by decide) (by decide) (by decide) i hi).trans (h.2.2 i hi)⟩
  have mem12_136 : MontgomeryAt t12 (stackSlot s 136) ((values point).yy) := by
    have h := mem11_136
    rw [stackSlot_eq s (by decide)] at h ⊢
    exact ⟨h.1, h.2.1, fun i hi => (bytes12 592 32 (by decide) (by decide) (by decide) i hi).trans (h.2.2 i hi)⟩
  have mem12_168 : MontgomeryAt t12 (stackSlot s 168) ((values point).zz) := by
    have h := mem11_168
    rw [stackSlot_eq s (by decide)] at h ⊢
    exact ⟨h.1, h.2.1, fun i hi => (bytes12 560 32 (by decide) (by decide) (by decide) i hi).trans (h.2.2 i hi)⟩
  have mem12_72 : MontgomeryAt t12 (stackSlot s 72) ((P256.Spec.Operations.domain.b*(values point).zz) % P256.Spec.Operations.domain.p) := by
    have h := mem11_72
    rw [stackSlot_eq s (by decide)] at h ⊢
    exact ⟨h.1, h.2.1, fun i hi => (bytes12 656 32 (by decide) (by decide) (by decide) i hi).trans (h.2.2 i hi)⟩
  have mem12_552 : MontgomeryAt t12 (stackSlot s 552) ((values point).xy2) := by
    have h := mem11_552
    rw [stackSlot_eq s (by decide)] at h ⊢
    exact ⟨h.1, h.2.1, fun i hi => (bytes12 176 32 (by decide) (by decide) (by decide) i hi).trans (h.2.2 i hi)⟩
  have mem12_200 : MontgomeryAt t12 (stackSlot s 200) ((values point).xz2) := by
    have h := mem11_200
    rw [stackSlot_eq s (by decide)] at h ⊢
    exact ⟨h.1, h.2.1, fun i hi => (bytes12 528 32 (by decide) (by decide) (by decide) i hi).trans (h.2.2 i hi)⟩
  have mem12_40 : MontgomeryAt t12 (stackSlot s 40) ((values point).zz) := by
    have h := mem11_40
    rw [stackSlot_eq s (by decide)] at h ⊢
    exact ⟨h.1, h.2.1, fun i hi => (bytes12 688 32 (by decide) (by decide) (by decide) i hi).trans (h.2.2 i hi)⟩
  have mem12_8 : MontgomeryAt t12 (stackSlot s 8) ((values point).xz2) := by
    have h := mem11_8
    rw [stackSlot_eq s (by decide)] at h ⊢
    exact ⟨h.1, h.2.1, fun i hi => (bytes12 720 32 (by decide) (by decide) (by decide) i hi).trans (h.2.2 i hi)⟩
  have mem12_264 : MontgomeryAt t12 (stackSlot s 264) (delta) := by
    rw [stackSlot_eq s (by decide)]
    exact value12
  obtain ⟨t13, run13, frame13, rip13, frameScratch13, arg13_13, arg13_7, arg13_6⟩ :=
    doubleDifference pre frame12 rip12
  have reg13_3 : t13.regValue .rbx = s.regValue .rdi :=
    (frameScratch13.read (n := 64) (r := 3) (by simp [scratchComponents])).trans reg12_3
  have reg13_15 : t13.regValue .r15 = stackSlot s 72 :=
    (frameScratch13.read (n := 64) (r := 15) (by simp [scratchComponents])).trans reg12_15
  have reg13_14 : t13.regValue .r14 = stackSlot s 552 :=
    (frameScratch13.read (n := 64) (r := 14) (by simp [scratchComponents])).trans reg12_14
  have reg13_5 : t13.regValue .rbp = 0xd89cdf6229c4bddf :=
    (frameScratch13.read (n := 64) (r := 5) (by simp [scratchComponents])).trans reg12_5
  have reg13_12 : t13.regValue .r12 = stackSlot s 264 :=
    (frameScratch13.read (n := 64) (r := 12) (by simp [scratchComponents])).trans reg12_12
  have reg13_13 : t13.regValue .r13 = stackSlot s 40 := arg13_13
  have reg13_7 : t13.regValue .rdi = stackSlot s 40 := arg13_7
  have reg13_6 : t13.regValue .rsi = stackSlot s 264 := arg13_6.trans reg12_12
  have point13 := scratch_point pre frameScratch13 (by decide) point12
  have mem13_104 : MontgomeryAt t13 (stackSlot s 104) ((values point).xx) :=
    scratch_montgomery frameScratch13 (slots_apart (by decide) (by decide) (by decide)) mem12_104
  have mem13_136 : MontgomeryAt t13 (stackSlot s 136) ((values point).yy) :=
    scratch_montgomery frameScratch13 (slots_apart (by decide) (by decide) (by decide)) mem12_136
  have mem13_168 : MontgomeryAt t13 (stackSlot s 168) ((values point).zz) :=
    scratch_montgomery frameScratch13 (slots_apart (by decide) (by decide) (by decide)) mem12_168
  have mem13_72 : MontgomeryAt t13 (stackSlot s 72) ((P256.Spec.Operations.domain.b*(values point).zz) % P256.Spec.Operations.domain.p) :=
    scratch_montgomery frameScratch13 (slots_apart (by decide) (by decide) (by decide)) mem12_72
  have mem13_552 : MontgomeryAt t13 (stackSlot s 552) ((values point).xy2) :=
    scratch_montgomery frameScratch13 (slots_apart (by decide) (by decide) (by decide)) mem12_552
  have mem13_200 : MontgomeryAt t13 (stackSlot s 200) ((values point).xz2) :=
    scratch_montgomery frameScratch13 (slots_apart (by decide) (by decide) (by decide)) mem12_200
  have mem13_264 : MontgomeryAt t13 (stackSlot s 264) (delta) :=
    scratch_montgomery frameScratch13 (slots_apart (by decide) (by decide) (by decide)) mem12_264
  have input13_6 : t13.regValue .rsi = stackPtr s - BitVec.ofNat 64 464 := by
    have h := reg13_6
    rw [stackSlot_eq s (by decide)] at h
    exact h
  have input13_7 : t13.regValue .rdi = stackPtr s - BitVec.ofNat 64 688 := by
    have h := reg13_7
    rw [stackSlot_eq s (by decide)] at h
    exact h
  have value13_264 : MontgomeryAt t13 (stackPtr s - BitVec.ofNat 64 464) (delta) := by
    have h := mem13_264
    rw [stackSlot_eq s (by decide)] at h
    exact h
  obtain ⟨n14, t14, run14, frame14, rip14, value14, regs14, bytes14, work14⟩ :=
    unary_call pre frame13 (entry := 0x1137f0) (outputBytes := 32) (reserve := 16)
      (x := delta) (resultAt := fun u ptr => MontgomeryAt u ptr ((delta+delta) % P256.Spec.Operations.domain.p))
      (⟨736, 464, 688, by decide, by decide, by decide, by decide,
        by decide, by decide, by decide⟩ : StackCallLayout 1016 32 32 16)
      rfl (by decide) 0x5f80 0xd86b (by decide) (by decide +kernel)
      (by decide) (by decide) (inProgram_of_textOffset 0x137f0 (by decide))
      (fun _ hp hx => field_double_correct hp hx) rip13 input13_6 input13_7 value13_264
  have point14 := point_of_stack pre (work_stack_frame pre work14) point13
  have reg14_3 : t14.regValue .rbx = s.regValue .rdi :=
    (regs14 .rbx (by decide)).trans reg13_3
  have reg14_15 : t14.regValue .r15 = stackSlot s 72 :=
    (regs14 .r15 (by decide)).trans reg13_15
  have reg14_14 : t14.regValue .r14 = stackSlot s 552 :=
    (regs14 .r14 (by decide)).trans reg13_14
  have reg14_5 : t14.regValue .rbp = 0xd89cdf6229c4bddf :=
    (regs14 .rbp (by decide)).trans reg13_5
  have reg14_12 : t14.regValue .r12 = stackSlot s 264 :=
    (regs14 .r12 (by decide)).trans reg13_12
  have reg14_13 : t14.regValue .r13 = stackSlot s 40 :=
    (regs14 .r13 (by decide)).trans reg13_13
  have mem14_104 : MontgomeryAt t14 (stackSlot s 104) ((values point).xx) := by
    have h := mem13_104
    rw [stackSlot_eq s (by decide)] at h ⊢
    exact ⟨h.1, h.2.1, fun i hi => (bytes14 624 32 (by decide) (by decide) (by decide) i hi).trans (h.2.2 i hi)⟩
  have mem14_136 : MontgomeryAt t14 (stackSlot s 136) ((values point).yy) := by
    have h := mem13_136
    rw [stackSlot_eq s (by decide)] at h ⊢
    exact ⟨h.1, h.2.1, fun i hi => (bytes14 592 32 (by decide) (by decide) (by decide) i hi).trans (h.2.2 i hi)⟩
  have mem14_168 : MontgomeryAt t14 (stackSlot s 168) ((values point).zz) := by
    have h := mem13_168
    rw [stackSlot_eq s (by decide)] at h ⊢
    exact ⟨h.1, h.2.1, fun i hi => (bytes14 560 32 (by decide) (by decide) (by decide) i hi).trans (h.2.2 i hi)⟩
  have mem14_72 : MontgomeryAt t14 (stackSlot s 72) ((P256.Spec.Operations.domain.b*(values point).zz) % P256.Spec.Operations.domain.p) := by
    have h := mem13_72
    rw [stackSlot_eq s (by decide)] at h ⊢
    exact ⟨h.1, h.2.1, fun i hi => (bytes14 656 32 (by decide) (by decide) (by decide) i hi).trans (h.2.2 i hi)⟩
  have mem14_552 : MontgomeryAt t14 (stackSlot s 552) ((values point).xy2) := by
    have h := mem13_552
    rw [stackSlot_eq s (by decide)] at h ⊢
    exact ⟨h.1, h.2.1, fun i hi => (bytes14 176 32 (by decide) (by decide) (by decide) i hi).trans (h.2.2 i hi)⟩
  have mem14_200 : MontgomeryAt t14 (stackSlot s 200) ((values point).xz2) := by
    have h := mem13_200
    rw [stackSlot_eq s (by decide)] at h ⊢
    exact ⟨h.1, h.2.1, fun i hi => (bytes14 528 32 (by decide) (by decide) (by decide) i hi).trans (h.2.2 i hi)⟩
  have mem14_264 : MontgomeryAt t14 (stackSlot s 264) (delta) := by
    have h := mem13_264
    rw [stackSlot_eq s (by decide)] at h ⊢
    exact ⟨h.1, h.2.1, fun i hi => (bytes14 464 32 (by decide) (by decide) (by decide) i hi).trans (h.2.2 i hi)⟩
  have mem14_40 : MontgomeryAt t14 (stackSlot s 40) ((delta+delta) % P256.Spec.Operations.domain.p) := by
    rw [stackSlot_eq s (by decide)]
    exact value14
  obtain ⟨t15, run15, frame15, rip15, frameScratch15, arg15_15, arg15_2, arg15_7, arg15_6, word15_8, word15_16, word15_24, word15_32⟩ :=
    triple pre frame14 rip14
  have reg15_3 : t15.regValue .rbx = s.regValue .rdi :=
    (frameScratch15.read (n := 64) (r := 3) (by simp [scratchComponents])).trans reg14_3
  have reg15_14 : t15.regValue .r14 = stackSlot s 552 :=
    (frameScratch15.read (n := 64) (r := 14) (by simp [scratchComponents])).trans reg14_14
  have reg15_5 : t15.regValue .rbp = 0xd89cdf6229c4bddf :=
    (frameScratch15.read (n := 64) (r := 5) (by simp [scratchComponents])).trans reg14_5
  have reg15_12 : t15.regValue .r12 = stackSlot s 264 :=
    (frameScratch15.read (n := 64) (r := 12) (by simp [scratchComponents])).trans reg14_12
  have reg15_13 : t15.regValue .r13 = stackSlot s 40 :=
    (frameScratch15.read (n := 64) (r := 13) (by simp [scratchComponents])).trans reg14_13
  have reg15_15 : t15.regValue .r15 = stackSlot s 296 := arg15_15
  have reg15_2 : t15.regValue .rdx = stackSlot s 8 := arg15_2
  have reg15_7 : t15.regValue .rdi = stackSlot s 296 := arg15_7
  have reg15_6 : t15.regValue .rsi = stackSlot s 40 := arg15_6.trans reg14_13
  have point15 := scratch_point pre frameScratch15 (by decide) point14
  have mem15_104 : MontgomeryAt t15 (stackSlot s 104) ((values point).xx) :=
    scratch_montgomery frameScratch15 (slots_apart (by decide) (by decide) (by decide)) mem14_104
  have mem15_136 : MontgomeryAt t15 (stackSlot s 136) ((values point).yy) :=
    scratch_montgomery frameScratch15 (slots_apart (by decide) (by decide) (by decide)) mem14_136
  have mem15_168 : MontgomeryAt t15 (stackSlot s 168) ((values point).zz) :=
    scratch_montgomery frameScratch15 (slots_apart (by decide) (by decide) (by decide)) mem14_168
  have mem15_72 : MontgomeryAt t15 (stackSlot s 72) ((P256.Spec.Operations.domain.b*(values point).zz) % P256.Spec.Operations.domain.p) :=
    scratch_montgomery frameScratch15 (slots_apart (by decide) (by decide) (by decide)) mem14_72
  have mem15_552 : MontgomeryAt t15 (stackSlot s 552) ((values point).xy2) :=
    scratch_montgomery frameScratch15 (slots_apart (by decide) (by decide) (by decide)) mem14_552
  have mem15_200 : MontgomeryAt t15 (stackSlot s 200) ((values point).xz2) :=
    scratch_montgomery frameScratch15 (slots_apart (by decide) (by decide) (by decide)) mem14_200
  have mem15_264 : MontgomeryAt t15 (stackSlot s 264) (delta) :=
    scratch_montgomery frameScratch15 (slots_apart (by decide) (by decide) (by decide)) mem14_264
  have mem15_40 : MontgomeryAt t15 (stackSlot s 40) ((delta+delta) % P256.Spec.Operations.domain.p) :=
    scratch_montgomery frameScratch15 (slots_apart (by decide) (by decide) (by decide)) mem14_40
  have mem15_8 : MontgomeryAt t15 (stackSlot s 8) (delta) := by
    apply copied (dst := 8) pre frame15 (by decide) mem14_264
    · exact word15_8
    · change memLoad t15.external (stackSlot s 16) 64 =
        memLoad t14.external (stackSlot s 264 + BitVec.ofNat 64 8) 64
      rw [slot_add]
      exact word15_16
    · change memLoad t15.external (stackSlot s 24) 64 =
        memLoad t14.external (stackSlot s 264 + BitVec.ofNat 64 16) 64
      rw [slot_add]
      exact word15_24
    · change memLoad t15.external (stackSlot s 32) 64 =
        memLoad t14.external (stackSlot s 264 + BitVec.ofNat 64 24) 64
      rw [slot_add]
      exact word15_32
  have input15_6 : t15.regValue .rsi = stackPtr s - BitVec.ofNat 64 688 := by
    have h := reg15_6
    rw [stackSlot_eq s (by decide)] at h
    exact h
  have input15_7 : t15.regValue .rdi = stackPtr s - BitVec.ofNat 64 432 := by
    have h := reg15_7
    rw [stackSlot_eq s (by decide)] at h
    exact h
  have input15_2 : t15.regValue .rdx = stackPtr s - BitVec.ofNat 64 720 := by
    have h := reg15_2
    rw [stackSlot_eq s (by decide)] at h
    exact h
  have value15_40 : MontgomeryAt t15 (stackPtr s - BitVec.ofNat 64 688) ((delta+delta) % P256.Spec.Operations.domain.p) := by
    have h := mem15_40
    rw [stackSlot_eq s (by decide)] at h
    exact h
  have value15_8 : MontgomeryAt t15 (stackPtr s - BitVec.ofNat 64 720) (delta) := by
    have h := mem15_8
    rw [stackSlot_eq s (by decide)] at h
    exact h
  obtain ⟨n16, t16, run16, frame16, rip16, value16, regs16, bytes16, work16⟩ :=
    binary_call pre frame15 tripleDifferenceSite (op := fun x y => (x+y) % P256.Spec.Operations.domain.p)
      (fun _ hp hx hy => field_add_correct hp hx hy) rip15
      input15_6 input15_2 input15_7 value15_40 value15_8
  have point16 := point_of_stack pre (work_stack_frame pre work16) point15
  have reg16_3 : t16.regValue .rbx = s.regValue .rdi :=
    (regs16 .rbx (by decide)).trans reg15_3
  have reg16_15 : t16.regValue .r15 = stackSlot s 296 :=
    (regs16 .r15 (by decide)).trans reg15_15
  have reg16_14 : t16.regValue .r14 = stackSlot s 552 :=
    (regs16 .r14 (by decide)).trans reg15_14
  have reg16_5 : t16.regValue .rbp = 0xd89cdf6229c4bddf :=
    (regs16 .rbp (by decide)).trans reg15_5
  have reg16_12 : t16.regValue .r12 = stackSlot s 264 :=
    (regs16 .r12 (by decide)).trans reg15_12
  have reg16_13 : t16.regValue .r13 = stackSlot s 40 :=
    (regs16 .r13 (by decide)).trans reg15_13
  have mem16_104 : MontgomeryAt t16 (stackSlot s 104) ((values point).xx) := by
    have h := mem15_104
    rw [stackSlot_eq s (by decide)] at h ⊢
    exact ⟨h.1, h.2.1, fun i hi => (bytes16 624 32 (by decide) (by decide) (by decide) i hi).trans (h.2.2 i hi)⟩
  have mem16_136 : MontgomeryAt t16 (stackSlot s 136) ((values point).yy) := by
    have h := mem15_136
    rw [stackSlot_eq s (by decide)] at h ⊢
    exact ⟨h.1, h.2.1, fun i hi => (bytes16 592 32 (by decide) (by decide) (by decide) i hi).trans (h.2.2 i hi)⟩
  have mem16_168 : MontgomeryAt t16 (stackSlot s 168) ((values point).zz) := by
    have h := mem15_168
    rw [stackSlot_eq s (by decide)] at h ⊢
    exact ⟨h.1, h.2.1, fun i hi => (bytes16 560 32 (by decide) (by decide) (by decide) i hi).trans (h.2.2 i hi)⟩
  have mem16_72 : MontgomeryAt t16 (stackSlot s 72) ((P256.Spec.Operations.domain.b*(values point).zz) % P256.Spec.Operations.domain.p) := by
    have h := mem15_72
    rw [stackSlot_eq s (by decide)] at h ⊢
    exact ⟨h.1, h.2.1, fun i hi => (bytes16 656 32 (by decide) (by decide) (by decide) i hi).trans (h.2.2 i hi)⟩
  have mem16_552 : MontgomeryAt t16 (stackSlot s 552) ((values point).xy2) := by
    have h := mem15_552
    rw [stackSlot_eq s (by decide)] at h ⊢
    exact ⟨h.1, h.2.1, fun i hi => (bytes16 176 32 (by decide) (by decide) (by decide) i hi).trans (h.2.2 i hi)⟩
  have mem16_200 : MontgomeryAt t16 (stackSlot s 200) ((values point).xz2) := by
    have h := mem15_200
    rw [stackSlot_eq s (by decide)] at h ⊢
    exact ⟨h.1, h.2.1, fun i hi => (bytes16 528 32 (by decide) (by decide) (by decide) i hi).trans (h.2.2 i hi)⟩
  have mem16_264 : MontgomeryAt t16 (stackSlot s 264) (delta) := by
    have h := mem15_264
    rw [stackSlot_eq s (by decide)] at h ⊢
    exact ⟨h.1, h.2.1, fun i hi => (bytes16 464 32 (by decide) (by decide) (by decide) i hi).trans (h.2.2 i hi)⟩
  have mem16_40 : MontgomeryAt t16 (stackSlot s 40) ((delta+delta) % P256.Spec.Operations.domain.p) := by
    have h := mem15_40
    rw [stackSlot_eq s (by decide)] at h ⊢
    exact ⟨h.1, h.2.1, fun i hi => (bytes16 688 32 (by decide) (by decide) (by decide) i hi).trans (h.2.2 i hi)⟩
  have mem16_8 : MontgomeryAt t16 (stackSlot s 8) (delta) := by
    have h := mem15_8
    rw [stackSlot_eq s (by decide)] at h ⊢
    exact ⟨h.1, h.2.1, fun i hi => (bytes16 720 32 (by decide) (by decide) (by decide) i hi).trans (h.2.2 i hi)⟩
  have mem16_296 : MontgomeryAt t16 (stackSlot s 296) ((values point).bzz3) := by
    rw [stackSlot_eq s (by decide)]
    exact value16
  refine ⟨_, t16, ((((((((run8.trans run9).trans run10).trans run11).trans run12).trans run13).trans run14).trans run15).trans run16), frame16, rip16, point16, reg16_3, reg16_5, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have h := reg16_14
    rw [stackSlot_eq s (by decide)] at h
    exact h
  · have h := reg16_15
    rw [stackSlot_eq s (by decide)] at h
    exact h
  · have h := mem16_104
    rw [stackSlot_eq s (by decide)] at h
    exact h
  · have h := mem16_136
    rw [stackSlot_eq s (by decide)] at h
    exact h
  · have h := mem16_168
    rw [stackSlot_eq s (by decide)] at h
    exact h
  · have h := mem16_552
    rw [stackSlot_eq s (by decide)] at h
    exact h
  · have h := mem16_200
    rw [stackSlot_eq s (by decide)] at h
    exact h
  · have h := mem16_296
    rw [stackSlot_eq s (by decide)] at h
    exact h

end P256.Proofs.Projective.Double
