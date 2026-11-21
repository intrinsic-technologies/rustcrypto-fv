import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.StoreWindow
import X86Proofs.Instructions.Dec.Generated.R.Triple
import X86Proofs.Instructions.Cmp.Generated.RR.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Branch.Triple
import P256.Proofs.Common.Instructions.CmovMemory.Effect

set_option autoImplicit false


namespace P256.Proofs.Sec1.SquareRoot.ExponentInitialize

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem enter_tail [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {x : Nat} (ctx : ExponentPre s boundary x) (hf : Frame s t)
    (hbp : t.regValue .rbp = 4) (hbx : t.regValue .rbx = 3)
    (hwindow : (Operand.mem (exponentFrameBase s+0x78) : Operand 32).read t = 16)
    (hip : t.RIP = 0x115499) :
    ∃ u, Advances boundary 6 t u ∧ Frame s u ∧ u.RIP = 0x1154c5 ∧
      u.regValue .rbp = 3 ∧ u.regValue .r14 = 16 ∧
      AgreesExcept [.reg 5, .reg 14, .flags, .mem (exponentFrameBase s+0x2c0) 8, .rip] t u ∧
      u.external = memStore t.external (exponentFrameBase s+0x2c0) (3 : BitVec 64) := by
  have hnext (offset : Nat) (ho : offset < 118431) :
      Extracted.textAddress + BitVec.ofNat 64 offset ≠ boundary.rip :=
    boundary_ne_program ctx.toCalleePre.outerBoundary (inProgram_of_textOffset offset ho)
  have hc := programLoaded_codeIn hf.loaded
  have hc1 : CodeIn (codeRange 0x115499 [0x48,0xff,0xcd]) t :=
    programText_slice hc 0x15499 _ (by decide) (by decide +kernel)
  obtain ⟨t1, ha1, hr1, he1⟩ :=
    (dec_r64_effect_step 0x115499 0x48 0xcd (by constructor <;> rfl) rfl rfl).advances
      (readyToStep hf.machine hf.bindingsSupported) hc1 hip (hnext 0x1549c (by decide))
  have hs1 : AgreesExcept [.reg 5, .flags, .rip] t t1 := he1.agrees
  have hv1 : (Operand.reg 5 : Operand 64).read t1 =
      3 := by
    exact he1.writes.trans (by change t.regValue .rbp - (1#64) = 3; rw [hbp]; rfl)
  have hb1 : (Operand.reg 3 : Operand 64).read t1 = 3 :=
    (hs1.read (by decide)).trans hbx
  have hc2 : CodeIn (codeRange 0x11549c [0x48,0x39,0xdd]) t1 :=
    programText_slice (hs1.codeIn (by simp [Component.Covers]) hc) 0x1549c _
      (by decide) (by decide +kernel)
  obtain ⟨t2, ha2, hr2, he2⟩ :=
    (cmp_r64_r64_effect_step 0x11549c 0x48 0xdd (by constructor <;> rfl) rfl).advances
      hr1 hc2 he1.rip (hnext 0x1549f (by decide))
  have hs2 : AgreesExcept [.flags, .rip] t1 t2 := he2.agrees
  have hf2 : (StatusFlags.ofRFLAGS t2.RFLAGS).ZF = true := by
    have hf := he2.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS t2.RFLAGS).ZF =
      (((Operand.reg 5 : Operand 64).read t1 - (Operand.reg 3 : Operand 64).read t1) == 0) at hf
    rw [hf, hv1, hb1]
    rfl
  have hag2 : AgreesExcept [.reg 5, .flags, .rip] t t2 :=
    (hs1.trans hs2).mono (by
      intro c hc
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
      grind only)
  have hc3 : CodeIn (codeRange 0x11549f [0x41,0xbe,16,0,0,0]) t2 :=
    programText_slice (hag2.codeIn (by simp [Component.Covers]) hc) 0x1549f _
      (by decide) (by decide +kernel)
  obtain ⟨t3, ha3, hr3, he3⟩ :=
    (mov_r32_imm32_rex_effect_step 0x11549f 0x41 0xbe
      (by simp [RexNoWPrefix]) (by decide) 16).advances
      hr2 hc3 he2.rip (hnext 0x154a5 (by decide))
  have hs3 : AgreesExcept [.reg 14, .rip] t2 t3 := he3.agrees
  have hag3 : AgreesExcept [.reg 5, .reg 14, .flags, .rip] t t3 :=
    (hag2.trans hs3).mono (by
      intro c hc
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
      grind only)
  have hf3 : (StatusFlags.ofRFLAGS t3.RFLAGS).ZF = true := by
    rw [hs3.rflags (by decide) (by decide), hf2]
  have hv3 : (Operand.reg 14 : Operand 64).read t3 = 16 := he3.writes
  have hl3 : (Operand.reg 14 : Operand 32).read t3 = 16 :=
    congrArg (BitVec.setWidth 32) hv3
  have hframe3 := hf.after_registers hr3 hag3 (by simp [Component.Covers]) (by decide)
  have haddr : (AddrMode.sib 4 none 0 (.d8 0x78)).addr t3 0x1154ab =
      exponentFrameBase s + 0x78 := by
    change stackPtr t3+0x78#64=_
    exact congrArg (fun p ↦ p+0x78) hframe3.rsp
  have hread : MemReadable t3 ((AddrMode.sib 4 none 0 (.d8 0x78)).addr t3 0x1154ab) 4 := by
    rw [haddr]
    have h := ScalarFrame.stack_readable (frameOffset := 1416) ctx.toCalleePre hframe3
      (offset := 120) (len := 4) (by decide) (by decide)
    have sp : stackPtr t3=exponentFrameBase s := hframe3.rsp
    rwa [sp] at h
  have hc4 : CodeIn (codeRange 0x1154a5 [0x44,0x0f,0x44,0x74,0x24,0x78]) t3 :=
    programText_slice (hag3.codeIn (by simp [Component.Covers]) hc) 0x154a5 _
      (by decide) (by decide +kernel)
  obtain ⟨t4, ha4, hr4, he4⟩ := (P256.Proofs.Common.Instructions.cmov_r32_m32_rex_effect_step 0x1154a5 0x44 0x44
    (by simp [RexNoWPrefix]) (.inr (.inl rfl)) 6 (.sib 4 none 0 (.d8 0x78)) (by decide) rfl rfl).advances
    hr3 hc4 ⟨he3.rip, hread⟩ (hnext 0x154ab (by decide))
  have hs4 : AgreesExcept [.reg 14, .rip] t3 t4 := he4.agrees
  have bp4 : t4.regValue .rbp = 3 := by
    change (Operand.reg 5 : Operand 64).read t4 = _
    rw [hs4.read (by decide), hs3.read (by decide), hs2.read (by decide)]
    exact hv1
  have hg4 : AgreesExcept [.reg 5, .reg 14, .flags, .rip] t t4 :=
    (hag3.trans hs4).mono (by simp_all)
  have hf4 := hf.after_registers hr4 hg4 (by simp [Component.Covers]) (by decide)
  have r144 : t4.regValue .r14 = 16 := by
    have hh := he4.writes
    change (Operand.reg 14 : Operand 64).read t4 =
      (if (StatusFlags.ofRFLAGS t3.RFLAGS).ZF then
        (Operand.mem ((AddrMode.sib 4 none 0 (.d8 0x78)).addr t3 0x1154ab) : Operand 32).read t3
      else (Operand.reg 14 : Operand 32).read t3).setWidth 64 at hh
    rw [hf3, ite_eq_left rfl, haddr] at hh
    have hm3 : t3.external = t.external := hag3.external (by simp [Component.Covers])
    have hw3 : (Operand.mem (exponentFrameBase s+0x78) : Operand 32).read t3 = 16 := by
      change memLoad t3.external _ _ = _
      rw [hm3]
      exact hwindow
    rw [hw3] at hh
    exact hh
  obtain ⟨t5, ha5, hf5, hi5, hv5, hg5, hm5⟩ :=
    frame_store_r64 ctx.toCalleePre hf4 0x154ab 0x2c0 (.d32 0x2c0) 0x48 5
      (by simp [RexWPrefix]) rfl rfl rfl (by decide)
      he4.rip (by decide) (by decide +kernel)
  change AgreesExcept [.mem (exponentFrameBase s+0x2c0) 8, .rip] t4 t5 at hg5
  change t5.external = memStore t4.external (exponentFrameBase s+0x2c0) (t4.regValue .rbp) at hm5
  rw [bp4, hg4.external (by simp [Component.Covers])] at hm5
  obtain ⟨t6, ha6, hr6, he6⟩ := (jmp_rel8_effect_step 0x1154b3 0x10 (by decide)).advances
    (readyToStep hf5.machine hf5.bindingsSupported)
    (programText_slice (programLoaded_codeIn hf5.loaded) 0x154b3 _ (by decide) (by decide +kernel))
    hi5 (hnext 0x154c5 (by decide))
  have hg6 : AgreesExcept [.rip] t5 t6 := he6.agrees
  have hf6 := hf5.after_registers hr6 hg6 (by simp [Component.Covers]) (by decide)
  refine ⟨t6, ((((ha1.trans ha2).trans ha3).trans ha4).trans ha5).trans ha6,
    hf6, he6.rip, ?_, ?_, ((hg4.trans hg5).trans hg6).mono (by simp_all), ?_⟩
  · exact ((hg5.trans hg6).read (n := 64) (r := 5) (by simp)).trans bp4
  · exact ((hg5.trans hg6).read (n := 64) (r := 14) (by simp)).trans r144
  · exact (hg6.external (by simp [Component.Covers])).trans hm5

end P256.Proofs.Sec1.SquareRoot.ExponentInitialize
