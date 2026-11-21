import P256.Proofs.Sec1.Affine.Compact.Compare.Load
import P256.Proofs.Sec1.Affine.Compact.Compare.Store
import P256.Proofs.Sec1.Affine.Compact.Compare.Arithmetic
import P256.Proofs.Generate.Scalar.Compare.Setup

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Compact.Compare

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Field.Subtract (borrow subWord)
open P256.Proofs.Common.Field.FieldNeg.Instructions (or_r64_r64_effect_step)
open P256.Proofs.Common.Field.Instructions (sub_r64_m64_effect_step)
open P256.Proofs.Common.Instructions (sar_r64_imm8_effect_step)

theorem word3 [Bindings] {s t : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    (pre : AffineDecodePre s boundary bytes) (frame : Frame s t)
    (rip : t.RIP=0x110498) (a b c : BitVec 64)
    (left : memLoad t.external ((stackPtr s-760)+368) 64=a)
    (right : memLoad t.external ((stackPtr s-760)+600) 64=b)
    (carry : memLoad t.external (stackPtr s-512) 64=c)
    (zero : t.regValue .r13=0)
    : ∃ u, Advances boundary 14 t u ∧ Frame s u ∧ u.RIP=0x1104d8 ∧
      memLoad u.external (stackPtr s-512) 64=borrow a b (subWord a b c) ∧
      AgreesExcept [.reg 0,.reg 1,.reg 2,.reg 6,.reg 7,.reg 13,.flags,.rip,.mem (stackPtr s-512) 8] t u := by
  have addr1 (next : BitVec 64) : (AddrMode.sib 4 none 0 (.d32 248)).addr t next=(stackPtr s-760)+248 := by
    change stackPtr t+248#64=_
    rw [frame.rsp]
    rfl
  have read1 : MemReadable t ((stackPtr s-760)+248) 8 := by
    have h := ScalarFrame.stack_readable (frameOffset := 760) pre.toCalleePre frame
      (offset := 248) (len := 8) (by decide) (by decide)
    rw [frame.rsp] at h
    exact h
  have mem1 : memLoad t.external ((stackPtr s-760)+248) 64=c := by
    have addr : (stackPtr s-760)+248=stackPtr s-512 := by
      simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]; rfl
    rw [addr]
    exact carry
  obtain ⟨t1,a1,ready1,effect1⟩ := (sub_r64_m64_effect_step 0x110498 0x4c (by simp [RexWPrefix]) 5 (AddrMode.sib 4 none 0 (.d32 248)) (by decide) rfl rfl).advances
    (readyToStep frame.machine frame.bindingsSupported)
    (programText_slice (programLoaded_codeIn frame.loaded) 0x10498 _ (by decide) (by decide +kernel))
    ⟨rip,by rw [addr1]; exact read1⟩ (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x104a0 (by decide)))
  have g1 : AgreesExcept [.reg 13,.flags,.rip] t t1 := effect1.agrees
  have f1 := frame.after_registers ready1 g1 (by simp [Component.Covers]) (by simp)
  have ip1 : t1.RIP=0x1104a0 := effect1.rip
  have value1 : t1.regValue .r13=(0)-c := by
    have h := effect1.writes
    change t1.regValue .r13=t.regValue .r13-(Operand.mem ((AddrMode.sib 4 none 0 (.d32 248)).addr t 0x1104a0) : Operand 64).read t at h
    rw [addr1] at h
    change t1.regValue .r13=t.regValue .r13-memLoad t.external ((stackPtr s-760)+248) 64 at h
    rw [zero,mem1] at h
    exact h
  have addr2 (next : BitVec 64) : (AddrMode.sib 4 none 0 (.d32 368)).addr t1 next=(stackPtr s-760)+368 := by
    change stackPtr t1+368#64=_
    rw [f1.rsp]
    rfl
  have read2 : MemReadable t1 ((stackPtr s-760)+368) 8 := by
    have h := ScalarFrame.stack_readable (frameOffset := 760) pre.toCalleePre f1
      (offset := 368) (len := 8) (by decide) (by decide)
    rw [f1.rsp] at h
    exact h
  have mem2 : memLoad t1.external ((stackPtr s-760)+368) 64=a := by
    rw [g1.external (by simp [Component.Covers])]
    exact left
  obtain ⟨t2,a2,f2,ip2,v2,g2,m2⟩ := frame_load_r64 pre.outerBoundary f1
      0x104a0 0x48 1 (AddrMode.sib 4 none 0 (.d32 368)) (by simp [RexWPrefix]) (by decide) rfl rfl
      (by decide) ip1 (by decide) (by decide +kernel) (by rw [addr2]; exact read2)
  change AgreesExcept [.reg 1,.rip] t1 t2 at g2
  have value2 : t2.regValue .rcx=a := by
    rw [addr2] at v2
    exact v2.trans mem2
  have addr3 (next : BitVec 64) : (AddrMode.sib 4 none 0 (.d32 600)).addr t2 next=(stackPtr s-760)+600 := by
    change stackPtr t2+600#64=_
    rw [f2.rsp]
    rfl
  have read3 : MemReadable t2 ((stackPtr s-760)+600) 8 := by
    have h := ScalarFrame.stack_readable (frameOffset := 760) pre.toCalleePre f2
      (offset := 600) (len := 8) (by decide) (by decide)
    rw [f2.rsp] at h
    exact h
  have mem3 : memLoad t2.external ((stackPtr s-760)+600) 64=b := by
    rw [(g1.trans g2).external (by simp [Component.Covers])]
    exact right
  obtain ⟨t3,a3,f3,ip3,v3,g3,m3⟩ := frame_load_r64 pre.outerBoundary f2
      0x104a8 0x48 2 (AddrMode.sib 4 none 0 (.d32 600)) (by simp [RexWPrefix]) (by decide) rfl rfl
      (by decide) ip2 (by decide) (by decide +kernel) (by rw [addr3]; exact read3)
  change AgreesExcept [.reg 2,.rip] t2 t3 at g3
  have value3 : t3.regValue .rdx=b := by
    rw [addr3] at v3
    exact v3.trans mem3
  have r4_13 : t3.regValue .r13=(0)-c := ((g2.trans g3).read (n := 64) (r := 13) (by simp)).trans value1
  obtain ⟨t4,a4,ready4,effect4⟩ := (sar_r64_imm8_effect_step 0x1104b0 0x49 0xfd 63 (by simp [RexWPrefix]) rfl rfl).advances
    (readyToStep f3.machine f3.bindingsSupported)
    (programText_slice (programLoaded_codeIn f3.loaded) 0x104b0 _ (by decide) (by decide +kernel))
    ip3 (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x104b4 (by decide)))
  have g4 : AgreesExcept [.reg 13,.flags,.rip] t3 t4 := effect4.agrees
  have f4 := f3.after_registers ready4 g4 (by simp [Component.Covers]) (by simp)
  have ip4 : t4.RIP=0x1104b4 := effect4.rip
  have value4 : t4.regValue .r13=((0)-c).sshiftRight 63 := by
    have h := effect4.writes
    change t4.regValue .r13=(t3.regValue .r13).sshiftRight 63 at h
    rw [r4_13] at h
    exact h
  have r5_1 : t4.regValue .rcx=a := ((g3.trans g4).read (n := 64) (r := 1) (by simp)).trans value2
  obtain ⟨t5,a5,ready5,effect5⟩ := (add_r64_r64_effect_step 0x1104b4 0x49 0xcd (by simp [RexWPrefix]) rfl).advances
    (readyToStep f4.machine f4.bindingsSupported)
    (programText_slice (programLoaded_codeIn f4.loaded) 0x104b4 _ (by decide) (by decide +kernel))
    ip4 (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x104b7 (by decide)))
  have g5 : AgreesExcept [.reg 13,.flags,.rip] t4 t5 := effect5.agrees
  have f5 := f4.after_registers ready5 g5 (by simp [Component.Covers]) (by simp)
  have ip5 : t5.RIP=0x1104b7 := effect5.rip
  have value5 : t5.regValue .r13=(((0)-c).sshiftRight 63) + (a) := by
    have h := effect5.writes
    change t5.regValue .r13=(t4.regValue .r13) + (t4.regValue .rcx) at h
    rw [r5_1,value4] at h
    exact h
  have r6_2 : t5.regValue .rdx=b := ((g4.trans g5).read (n := 64) (r := 2) (by simp)).trans value3
  obtain ⟨t6,a6,ready6,effect6⟩ := (sub_r64_r64_effect_step 0x1104b7 0x49 0xd5 (by simp [RexWPrefix]) rfl).advances
    (readyToStep f5.machine f5.bindingsSupported)
    (programText_slice (programLoaded_codeIn f5.loaded) 0x104b7 _ (by decide) (by decide +kernel))
    ip5 (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x104ba (by decide)))
  have g6 : AgreesExcept [.reg 13,.flags,.rip] t5 t6 := effect6.agrees
  have f6 := f5.after_registers ready6 g6 (by simp [Component.Covers]) (by simp)
  have ip6 : t6.RIP=0x1104ba := effect6.rip
  have value6 : t6.regValue .r13=((((0)-c).sshiftRight 63) + (a)) - (b) := by
    have h := effect6.writes
    change t6.regValue .r13=(t5.regValue .r13) - (t5.regValue .rdx) at h
    rw [r6_2,value5] at h
    exact h
  have r7_1 : t6.regValue .rcx=a := ((((g3.trans g4).trans g5).trans g6).read (n := 64) (r := 1) (by simp)).trans value2
  obtain ⟨t7,a7,ready7,effect7⟩ := (not_r64_effect_step 0x1104ba 0x48 0xd1 (by simp [RexWPrefix]) rfl rfl).advances
    (readyToStep f6.machine f6.bindingsSupported)
    (programText_slice (programLoaded_codeIn f6.loaded) 0x104ba _ (by decide) (by decide +kernel))
    ip6 (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x104bd (by decide)))
  have g7 : AgreesExcept [.reg 1,.rip] t6 t7 := effect7.agrees
  have f7 := f6.after_registers ready7 g7 (by simp [Component.Covers]) (by simp)
  have ip7 : t7.RIP=0x1104bd := effect7.rip
  have value7 : t7.regValue .rcx= ~~~(a) := by
    have h := effect7.writes
    change t7.regValue .rcx= ~~~(t6.regValue .rcx) at h
    rw [r7_1] at h
    exact h
  have r8_2 : t7.regValue .rdx=b := ((((g4.trans g5).trans g6).trans g7).read (n := 64) (r := 2) (by simp)).trans value3
  obtain ⟨t8,a8,ready8,effect8⟩ := (mov_r64_r64_effect_step 0x1104bd 0x48 0xd6 (by simp [RexWPrefix]) rfl).advances
    (readyToStep f7.machine f7.bindingsSupported)
    (programText_slice (programLoaded_codeIn f7.loaded) 0x104bd _ (by decide) (by decide +kernel))
    ip7 (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x104c0 (by decide)))
  have g8 : AgreesExcept [.reg 6,.rip] t7 t8 := effect8.agrees
  have f8 := f7.after_registers ready8 g8 (by simp [Component.Covers]) (by simp)
  have ip8 : t8.RIP=0x1104c0 := effect8.rip
  have value8 : t8.regValue .rsi=b := by
    have h := effect8.writes
    change t8.regValue .rsi=t7.regValue .rdx at h
    rw [r8_2] at h
    exact h
  have r9_1 : t8.regValue .rcx= ~~~(a) := (g8.read (n := 64) (r := 1) (by simp)).trans value7
  obtain ⟨t9,a9,ready9,effect9⟩ := (and_r64_r64_effect_step 0x1104c0 0x48 0xce (by simp [RexWPrefix]) rfl).advances
    (readyToStep f8.machine f8.bindingsSupported)
    (programText_slice (programLoaded_codeIn f8.loaded) 0x104c0 _ (by decide) (by decide +kernel))
    ip8 (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x104c3 (by decide)))
  have g9 : AgreesExcept [.reg 6,.flags,.rip] t8 t9 := effect9.agrees
  have f9 := f8.after_registers ready9 g9 (by simp [Component.Covers]) (by simp)
  have ip9 : t9.RIP=0x1104c3 := effect9.rip
  have value9 : t9.regValue .rsi=(b) &&& (~~~(a)) := by
    have h := effect9.writes
    change t9.regValue .rsi=(t8.regValue .rsi) &&& (t8.regValue .rcx) at h
    rw [r9_1,value8] at h
    exact h
  have r10_2 : t9.regValue .rdx=b := ((((((g4.trans g5).trans g6).trans g7).trans g8).trans g9).read (n := 64) (r := 2) (by simp)).trans value3
  have r10_1 : t9.regValue .rcx= ~~~(a) := ((g8.trans g9).read (n := 64) (r := 1) (by simp)).trans value7
  obtain ⟨t10,a10,ready10,effect10⟩ := (or_r64_r64_effect_step 0x1104c3 0x48 0xd1 (by simp [RexWPrefix]) rfl).advances
    (readyToStep f9.machine f9.bindingsSupported)
    (programText_slice (programLoaded_codeIn f9.loaded) 0x104c3 _ (by decide) (by decide +kernel))
    ip9 (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x104c6 (by decide)))
  have g10 : AgreesExcept [.reg 1,.flags,.rip] t9 t10 := effect10.agrees
  have f10 := f9.after_registers ready10 g10 (by simp [Component.Covers]) (by simp)
  have ip10 : t10.RIP=0x1104c6 := effect10.rip
  have value10 : t10.regValue .rcx=(~~~(a)) ||| (b) := by
    have h := effect10.writes
    change t10.regValue .rcx=(t9.regValue .rcx) ||| (t9.regValue .rdx) at h
    rw [r10_2,r10_1] at h
    exact h
  have r11_13 : t10.regValue .r13=((((0)-c).sshiftRight 63) + (a)) - (b) := ((((g7.trans g8).trans g9).trans g10).read (n := 64) (r := 13) (by simp)).trans value6
  obtain ⟨t11,a11,ready11,effect11⟩ := (and_r64_r64_effect_step 0x1104c6 0x4c 0xe9 (by simp [RexWPrefix]) rfl).advances
    (readyToStep f10.machine f10.bindingsSupported)
    (programText_slice (programLoaded_codeIn f10.loaded) 0x104c6 _ (by decide) (by decide +kernel))
    ip10 (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x104c9 (by decide)))
  have g11 : AgreesExcept [.reg 1,.flags,.rip] t10 t11 := effect11.agrees
  have f11 := f10.after_registers ready11 g11 (by simp [Component.Covers]) (by simp)
  have ip11 : t11.RIP=0x1104c9 := effect11.rip
  have value11 : t11.regValue .rcx=((~~~(a)) ||| (b)) &&& (((((0)-c).sshiftRight 63) + (a)) - (b)) := by
    have h := effect11.writes
    change t11.regValue .rcx=(t10.regValue .rcx) &&& (t10.regValue .r13) at h
    rw [r11_13,value10] at h
    exact h
  have r12_6 : t11.regValue .rsi=(b) &&& (~~~(a)) := ((g10.trans g11).read (n := 64) (r := 6) (by simp)).trans value9
  obtain ⟨t12,a12,ready12,effect12⟩ := (or_r64_r64_effect_step 0x1104c9 0x48 0xf1 (by simp [RexWPrefix]) rfl).advances
    (readyToStep f11.machine f11.bindingsSupported)
    (programText_slice (programLoaded_codeIn f11.loaded) 0x104c9 _ (by decide) (by decide +kernel))
    ip11 (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x104cc (by decide)))
  have g12 : AgreesExcept [.reg 1,.flags,.rip] t11 t12 := effect12.agrees
  have f12 := f11.after_registers ready12 g12 (by simp [Component.Covers]) (by simp)
  have ip12 : t12.RIP=0x1104cc := effect12.rip
  have value12 : t12.regValue .rcx=(((~~~(a)) ||| (b)) &&& (((((0)-c).sshiftRight 63) + (a)) - (b))) ||| ((b) &&& (~~~(a))) := by
    have h := effect12.writes
    change t12.regValue .rcx=(t11.regValue .rcx) ||| (t11.regValue .rsi) at h
    rw [r12_6,value11] at h
    exact h
  obtain ⟨t13,a13,ready13,effect13⟩ := (shr_r64_imm8_effect_step 0x1104cc 0x48 0xe9 63 (by simp [RexWPrefix]) rfl rfl).advances
    (readyToStep f12.machine f12.bindingsSupported)
    (programText_slice (programLoaded_codeIn f12.loaded) 0x104cc _ (by decide) (by decide +kernel))
    ip12 (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x104d0 (by decide)))
  have g13 : AgreesExcept [.reg 1,.flags,.rip] t12 t13 := effect13.agrees
  have f13 := f12.after_registers ready13 g13 (by simp [Component.Covers]) (by simp)
  have ip13 : t13.RIP=0x1104d0 := effect13.rip
  have value13 : t13.regValue .rcx=((((~~~(a)) ||| (b)) &&& (((((0)-c).sshiftRight 63) + (a)) - (b))) ||| ((b) &&& (~~~(a)))) >>> 63 := by
    have h := effect13.writes
    change t13.regValue .rcx=(t12.regValue .rcx) >>> 63 at h
    rw [value12] at h
    exact h
  obtain ⟨t14,a14,f14,ip14,v14,g14,m14⟩ := frame_store_r64 pre.toCalleePre f13
    0x104d0 248 (.d32 248) 0x48 1 (by simp [RexWPrefix]) rfl rfl rfl
    (by decide) ip13 (by decide) (by decide +kernel)
  have scratch14 : (stackPtr s-760)+248=stackPtr s-512 := by
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]; rfl
  change AgreesExcept [.mem ((stackPtr s-760)+248) 8,.rip] t13 t14 at g14
  rw [scratch14] at g14
  have value14 : memLoad t14.external (stackPtr s-512) 64=((((~~~(a)) ||| (b)) &&& (((((0)-c).sshiftRight 63) + (a)) - (b))) ||| ((b) &&& (~~~(a)))) >>> 63 := by
    have h := v14
    change memLoad t14.external ((stackPtr s-760)+248) 64=t13.regValue .rcx at h
    rw [value13] at h
    have addr : (stackPtr s-760)+248=stackPtr s-512 := by
      simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]; rfl
    rwa [addr] at h
  refine ⟨t14,(((((((((((((a1.trans a2).trans a3).trans a4).trans a5).trans a6).trans a7).trans a8).trans a9).trans a10).trans a11).trans a12).trans a13).trans a14),f14,ip14,?_,?_⟩
  · simpa only [borrow,subWord,BitVec.sub_eq_add_neg,BitVec.add_assoc,
      BitVec.ofNat_eq_ofNat,BitVec.zero_add,BitVec.neg_zero] using value14
  · exact (((((((((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).trans g8).trans g9).trans g10).trans g11).trans g12).trans g13).trans g14).mono (by
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
      grind only)

end P256.Proofs.Sec1.Affine.Compact.Compare
