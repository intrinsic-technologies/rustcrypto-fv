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

theorem word1 [Bindings] {s t : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    (pre : AffineDecodePre s boundary bytes) (frame : Frame s t)
    (rip : t.RIP=0x11040c) (a b c : BitVec 64)
    (left : memLoad t.external ((stackPtr s-760)+352) 64=a)
    (right : memLoad t.external ((stackPtr s-760)+584) 64=b)
    (carry : memLoad t.external (stackPtr s-512) 64=c)
    : ∃ u, Advances boundary 16 t u ∧ Frame s u ∧ u.RIP=0x110456 ∧
      memLoad u.external (stackPtr s-512) 64=borrow a b (subWord a b c) ∧
      AgreesExcept [.reg 0,.reg 1,.reg 2,.reg 6,.reg 7,.flags,.rip,.mem (stackPtr s-512) 8] t u := by
  obtain ⟨t1,a1,ready1,effect1⟩ := (lea_r64_effect_step 0x11040c 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 248)) (by decide) rfl rfl).advances
    (readyToStep frame.machine frame.bindingsSupported)
    (programText_slice (programLoaded_codeIn frame.loaded) 0x1040c _ (by decide) (by decide +kernel))
    rip (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x10414 (by decide)))
  have g1 : AgreesExcept [.reg 0,.rip] t t1 := effect1.agrees
  have f1 := frame.after_registers ready1 g1 (by simp [Component.Covers]) (by simp)
  have ip1 : t1.RIP=0x110414 := effect1.rip
  have value1 : t1.regValue .rax=(stackPtr s-760)+248 := by
    have h := effect1.writes
    change t1.regValue .rax=stackPtr t+248 at h
    rw [frame.rsp] at h
    exact h
  obtain ⟨t2,a2,ready2,effect2⟩ := (xor_r32_r32_effect_step 0x110414 0xc9 rfl).advances
    (readyToStep f1.machine f1.bindingsSupported)
    (programText_slice (programLoaded_codeIn f1.loaded) 0x10414 _ (by decide) (by decide +kernel))
    ip1 (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x10416 (by decide)))
  have g2 : AgreesExcept [.reg 1,.flags,.rip] t1 t2 := effect2.agrees
  have f2 := f1.after_registers ready2 g2 (by simp [Component.Covers]) (by simp)
  have ip2 : t2.RIP=0x110416 := effect2.rip
  have value2 : t2.regValue .rcx=0 := by
    have h := effect2.writes
    change t2.regValue .rcx=(((t1.regValue .rcx).setWidth 32) ^^^ ((t1.regValue .rcx).setWidth 32)).setWidth 64 at h
    rw [BitVec.xor_self] at h
    exact h
  have addr3 (next : BitVec 64) : (AddrMode.sib 4 none 0 (.d32 248)).addr t2 next=(stackPtr s-760)+248 := by
    change stackPtr t2+248#64=_
    rw [f2.rsp]
    rfl
  have read3 : MemReadable t2 ((stackPtr s-760)+248) 8 := by
    have h := ScalarFrame.stack_readable (frameOffset := 760) pre.toCalleePre f2
      (offset := 248) (len := 8) (by decide) (by decide)
    rw [f2.rsp] at h
    exact h
  have mem3 : memLoad t2.external ((stackPtr s-760)+248) 64=c := by
    rw [(g1.trans g2).external (by simp [Component.Covers])]
    have addr : (stackPtr s-760)+248=stackPtr s-512 := by
      simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]; rfl
    rw [addr]
    exact carry
  obtain ⟨t3,a3,ready3,effect3⟩ := (sub_r64_m64_effect_step 0x110416 0x48 (by simp [RexWPrefix]) 1 (AddrMode.sib 4 none 0 (.d32 248)) (by decide) rfl rfl).advances
    (readyToStep f2.machine f2.bindingsSupported)
    (programText_slice (programLoaded_codeIn f2.loaded) 0x10416 _ (by decide) (by decide +kernel))
    ⟨ip2,by rw [addr3]; exact read3⟩ (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1041e (by decide)))
  have g3 : AgreesExcept [.reg 1,.flags,.rip] t2 t3 := effect3.agrees
  have f3 := f2.after_registers ready3 g3 (by simp [Component.Covers]) (by simp)
  have ip3 : t3.RIP=0x11041e := effect3.rip
  have value3 : t3.regValue .rcx=(0)-c := by
    have h := effect3.writes
    change t3.regValue .rcx=t2.regValue .rcx-(Operand.mem ((AddrMode.sib 4 none 0 (.d32 248)).addr t2 0x11041e) : Operand 64).read t2 at h
    rw [addr3] at h
    change t3.regValue .rcx=t2.regValue .rcx-memLoad t2.external ((stackPtr s-760)+248) 64 at h
    rw [value2,mem3] at h
    exact h
  have addr4 (next : BitVec 64) : (AddrMode.sib 4 none 0 (.d32 352)).addr t3 next=(stackPtr s-760)+352 := by
    change stackPtr t3+352#64=_
    rw [f3.rsp]
    rfl
  have read4 : MemReadable t3 ((stackPtr s-760)+352) 8 := by
    have h := ScalarFrame.stack_readable (frameOffset := 760) pre.toCalleePre f3
      (offset := 352) (len := 8) (by decide) (by decide)
    rw [f3.rsp] at h
    exact h
  have mem4 : memLoad t3.external ((stackPtr s-760)+352) 64=a := by
    rw [((g1.trans g2).trans g3).external (by simp [Component.Covers])]
    exact left
  obtain ⟨t4,a4,f4,ip4,v4,g4,m4⟩ := frame_load_r64 pre.outerBoundary f3
      0x1041e 0x48 2 (AddrMode.sib 4 none 0 (.d32 352)) (by simp [RexWPrefix]) (by decide) rfl rfl
      (by decide) ip3 (by decide) (by decide +kernel) (by rw [addr4]; exact read4)
  change AgreesExcept [.reg 2,.rip] t3 t4 at g4
  have value4 : t4.regValue .rdx=a := by
    rw [addr4] at v4
    exact v4.trans mem4
  have addr5 (next : BitVec 64) : (AddrMode.sib 4 none 0 (.d32 584)).addr t4 next=(stackPtr s-760)+584 := by
    change stackPtr t4+584#64=_
    rw [f4.rsp]
    rfl
  have read5 : MemReadable t4 ((stackPtr s-760)+584) 8 := by
    have h := ScalarFrame.stack_readable (frameOffset := 760) pre.toCalleePre f4
      (offset := 584) (len := 8) (by decide) (by decide)
    rw [f4.rsp] at h
    exact h
  have mem5 : memLoad t4.external ((stackPtr s-760)+584) 64=b := by
    rw [(((g1.trans g2).trans g3).trans g4).external (by simp [Component.Covers])]
    exact right
  obtain ⟨t5,a5,f5,ip5,v5,g5,m5⟩ := frame_load_r64 pre.outerBoundary f4
      0x10426 0x48 6 (AddrMode.sib 4 none 0 (.d32 584)) (by simp [RexWPrefix]) (by decide) rfl rfl
      (by decide) ip4 (by decide) (by decide +kernel) (by rw [addr5]; exact read5)
  change AgreesExcept [.reg 6,.rip] t4 t5 at g5
  have value5 : t5.regValue .rsi=b := by
    rw [addr5] at v5
    exact v5.trans mem5
  have r6_1 : t5.regValue .rcx=(0)-c := ((g4.trans g5).read (n := 64) (r := 1) (by simp)).trans value3
  obtain ⟨t6,a6,ready6,effect6⟩ := (sar_r64_imm8_effect_step 0x11042e 0x48 0xf9 63 (by simp [RexWPrefix]) rfl rfl).advances
    (readyToStep f5.machine f5.bindingsSupported)
    (programText_slice (programLoaded_codeIn f5.loaded) 0x1042e _ (by decide) (by decide +kernel))
    ip5 (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x10432 (by decide)))
  have g6 : AgreesExcept [.reg 1,.flags,.rip] t5 t6 := effect6.agrees
  have f6 := f5.after_registers ready6 g6 (by simp [Component.Covers]) (by simp)
  have ip6 : t6.RIP=0x110432 := effect6.rip
  have value6 : t6.regValue .rcx=((0)-c).sshiftRight 63 := by
    have h := effect6.writes
    change t6.regValue .rcx=(t5.regValue .rcx).sshiftRight 63 at h
    rw [r6_1] at h
    exact h
  have r7_2 : t6.regValue .rdx=a := ((g5.trans g6).read (n := 64) (r := 2) (by simp)).trans value4
  obtain ⟨t7,a7,ready7,effect7⟩ := (add_r64_r64_effect_step 0x110432 0x48 0xd1 (by simp [RexWPrefix]) rfl).advances
    (readyToStep f6.machine f6.bindingsSupported)
    (programText_slice (programLoaded_codeIn f6.loaded) 0x10432 _ (by decide) (by decide +kernel))
    ip6 (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x10435 (by decide)))
  have g7 : AgreesExcept [.reg 1,.flags,.rip] t6 t7 := effect7.agrees
  have f7 := f6.after_registers ready7 g7 (by simp [Component.Covers]) (by simp)
  have ip7 : t7.RIP=0x110435 := effect7.rip
  have value7 : t7.regValue .rcx=(((0)-c).sshiftRight 63) + (a) := by
    have h := effect7.writes
    change t7.regValue .rcx=(t6.regValue .rcx) + (t6.regValue .rdx) at h
    rw [r7_2,value6] at h
    exact h
  have r8_6 : t7.regValue .rsi=b := ((g6.trans g7).read (n := 64) (r := 6) (by simp)).trans value5
  obtain ⟨t8,a8,ready8,effect8⟩ := (sub_r64_r64_effect_step 0x110435 0x48 0xf1 (by simp [RexWPrefix]) rfl).advances
    (readyToStep f7.machine f7.bindingsSupported)
    (programText_slice (programLoaded_codeIn f7.loaded) 0x10435 _ (by decide) (by decide +kernel))
    ip7 (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x10438 (by decide)))
  have g8 : AgreesExcept [.reg 1,.flags,.rip] t7 t8 := effect8.agrees
  have f8 := f7.after_registers ready8 g8 (by simp [Component.Covers]) (by simp)
  have ip8 : t8.RIP=0x110438 := effect8.rip
  have value8 : t8.regValue .rcx=((((0)-c).sshiftRight 63) + (a)) - (b) := by
    have h := effect8.writes
    change t8.regValue .rcx=(t7.regValue .rcx) - (t7.regValue .rsi) at h
    rw [r8_6,value7] at h
    exact h
  have r9_2 : t8.regValue .rdx=a := ((((g5.trans g6).trans g7).trans g8).read (n := 64) (r := 2) (by simp)).trans value4
  obtain ⟨t9,a9,ready9,effect9⟩ := (not_r64_effect_step 0x110438 0x48 0xd2 (by simp [RexWPrefix]) rfl rfl).advances
    (readyToStep f8.machine f8.bindingsSupported)
    (programText_slice (programLoaded_codeIn f8.loaded) 0x10438 _ (by decide) (by decide +kernel))
    ip8 (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1043b (by decide)))
  have g9 : AgreesExcept [.reg 2,.rip] t8 t9 := effect9.agrees
  have f9 := f8.after_registers ready9 g9 (by simp [Component.Covers]) (by simp)
  have ip9 : t9.RIP=0x11043b := effect9.rip
  have value9 : t9.regValue .rdx= ~~~(a) := by
    have h := effect9.writes
    change t9.regValue .rdx= ~~~(t8.regValue .rdx) at h
    rw [r9_2] at h
    exact h
  have r10_6 : t9.regValue .rsi=b := ((((g6.trans g7).trans g8).trans g9).read (n := 64) (r := 6) (by simp)).trans value5
  obtain ⟨t10,a10,ready10,effect10⟩ := (mov_r64_r64_effect_step 0x11043b 0x48 0xf7 (by simp [RexWPrefix]) rfl).advances
    (readyToStep f9.machine f9.bindingsSupported)
    (programText_slice (programLoaded_codeIn f9.loaded) 0x1043b _ (by decide) (by decide +kernel))
    ip9 (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1043e (by decide)))
  have g10 : AgreesExcept [.reg 7,.rip] t9 t10 := effect10.agrees
  have f10 := f9.after_registers ready10 g10 (by simp [Component.Covers]) (by simp)
  have ip10 : t10.RIP=0x11043e := effect10.rip
  have value10 : t10.regValue .rdi=b := by
    have h := effect10.writes
    change t10.regValue .rdi=t9.regValue .rsi at h
    rw [r10_6] at h
    exact h
  have r11_2 : t10.regValue .rdx= ~~~(a) := (g10.read (n := 64) (r := 2) (by simp)).trans value9
  obtain ⟨t11,a11,ready11,effect11⟩ := (and_r64_r64_effect_step 0x11043e 0x48 0xd7 (by simp [RexWPrefix]) rfl).advances
    (readyToStep f10.machine f10.bindingsSupported)
    (programText_slice (programLoaded_codeIn f10.loaded) 0x1043e _ (by decide) (by decide +kernel))
    ip10 (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x10441 (by decide)))
  have g11 : AgreesExcept [.reg 7,.flags,.rip] t10 t11 := effect11.agrees
  have f11 := f10.after_registers ready11 g11 (by simp [Component.Covers]) (by simp)
  have ip11 : t11.RIP=0x110441 := effect11.rip
  have value11 : t11.regValue .rdi=(b) &&& (~~~(a)) := by
    have h := effect11.writes
    change t11.regValue .rdi=(t10.regValue .rdi) &&& (t10.regValue .rdx) at h
    rw [r11_2,value10] at h
    exact h
  have r12_6 : t11.regValue .rsi=b := ((((((g6.trans g7).trans g8).trans g9).trans g10).trans g11).read (n := 64) (r := 6) (by simp)).trans value5
  have r12_2 : t11.regValue .rdx= ~~~(a) := ((g10.trans g11).read (n := 64) (r := 2) (by simp)).trans value9
  obtain ⟨t12,a12,ready12,effect12⟩ := (or_r64_r64_effect_step 0x110441 0x48 0xf2 (by simp [RexWPrefix]) rfl).advances
    (readyToStep f11.machine f11.bindingsSupported)
    (programText_slice (programLoaded_codeIn f11.loaded) 0x10441 _ (by decide) (by decide +kernel))
    ip11 (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x10444 (by decide)))
  have g12 : AgreesExcept [.reg 2,.flags,.rip] t11 t12 := effect12.agrees
  have f12 := f11.after_registers ready12 g12 (by simp [Component.Covers]) (by simp)
  have ip12 : t12.RIP=0x110444 := effect12.rip
  have value12 : t12.regValue .rdx=(~~~(a)) ||| (b) := by
    have h := effect12.writes
    change t12.regValue .rdx=(t11.regValue .rdx) ||| (t11.regValue .rsi) at h
    rw [r12_6,r12_2] at h
    exact h
  have r13_1 : t12.regValue .rcx=((((0)-c).sshiftRight 63) + (a)) - (b) := ((((g9.trans g10).trans g11).trans g12).read (n := 64) (r := 1) (by simp)).trans value8
  obtain ⟨t13,a13,ready13,effect13⟩ := (and_r64_r64_effect_step 0x110444 0x48 0xca (by simp [RexWPrefix]) rfl).advances
    (readyToStep f12.machine f12.bindingsSupported)
    (programText_slice (programLoaded_codeIn f12.loaded) 0x10444 _ (by decide) (by decide +kernel))
    ip12 (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x10447 (by decide)))
  have g13 : AgreesExcept [.reg 2,.flags,.rip] t12 t13 := effect13.agrees
  have f13 := f12.after_registers ready13 g13 (by simp [Component.Covers]) (by simp)
  have ip13 : t13.RIP=0x110447 := effect13.rip
  have value13 : t13.regValue .rdx=((~~~(a)) ||| (b)) &&& (((((0)-c).sshiftRight 63) + (a)) - (b)) := by
    have h := effect13.writes
    change t13.regValue .rdx=(t12.regValue .rdx) &&& (t12.regValue .rcx) at h
    rw [r13_1,value12] at h
    exact h
  have r14_7 : t13.regValue .rdi=(b) &&& (~~~(a)) := ((g12.trans g13).read (n := 64) (r := 7) (by simp)).trans value11
  obtain ⟨t14,a14,ready14,effect14⟩ := (or_r64_r64_effect_step 0x110447 0x48 0xfa (by simp [RexWPrefix]) rfl).advances
    (readyToStep f13.machine f13.bindingsSupported)
    (programText_slice (programLoaded_codeIn f13.loaded) 0x10447 _ (by decide) (by decide +kernel))
    ip13 (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1044a (by decide)))
  have g14 : AgreesExcept [.reg 2,.flags,.rip] t13 t14 := effect14.agrees
  have f14 := f13.after_registers ready14 g14 (by simp [Component.Covers]) (by simp)
  have ip14 : t14.RIP=0x11044a := effect14.rip
  have value14 : t14.regValue .rdx=(((~~~(a)) ||| (b)) &&& (((((0)-c).sshiftRight 63) + (a)) - (b))) ||| ((b) &&& (~~~(a))) := by
    have h := effect14.writes
    change t14.regValue .rdx=(t13.regValue .rdx) ||| (t13.regValue .rdi) at h
    rw [r14_7,value13] at h
    exact h
  obtain ⟨t15,a15,ready15,effect15⟩ := (shr_r64_imm8_effect_step 0x11044a 0x48 0xea 63 (by simp [RexWPrefix]) rfl rfl).advances
    (readyToStep f14.machine f14.bindingsSupported)
    (programText_slice (programLoaded_codeIn f14.loaded) 0x1044a _ (by decide) (by decide +kernel))
    ip14 (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1044e (by decide)))
  have g15 : AgreesExcept [.reg 2,.flags,.rip] t14 t15 := effect15.agrees
  have f15 := f14.after_registers ready15 g15 (by simp [Component.Covers]) (by simp)
  have ip15 : t15.RIP=0x11044e := effect15.rip
  have value15 : t15.regValue .rdx=((((~~~(a)) ||| (b)) &&& (((((0)-c).sshiftRight 63) + (a)) - (b))) ||| ((b) &&& (~~~(a)))) >>> 63 := by
    have h := effect15.writes
    change t15.regValue .rdx=(t14.regValue .rdx) >>> 63 at h
    rw [value14] at h
    exact h
  obtain ⟨t16,a16,f16,ip16,v16,g16,m16⟩ := frame_store_r64 pre.toCalleePre f15
    0x1044e 248 (.d32 248) 0x48 2 (by simp [RexWPrefix]) rfl rfl rfl
    (by decide) ip15 (by decide) (by decide +kernel)
  have scratch16 : (stackPtr s-760)+248=stackPtr s-512 := by
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]; rfl
  change AgreesExcept [.mem ((stackPtr s-760)+248) 8,.rip] t15 t16 at g16
  rw [scratch16] at g16
  have value16 : memLoad t16.external (stackPtr s-512) 64=((((~~~(a)) ||| (b)) &&& (((((0)-c).sshiftRight 63) + (a)) - (b))) ||| ((b) &&& (~~~(a)))) >>> 63 := by
    have h := v16
    change memLoad t16.external ((stackPtr s-760)+248) 64=t15.regValue .rdx at h
    rw [value15] at h
    have addr : (stackPtr s-760)+248=stackPtr s-512 := by
      simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]; rfl
    rwa [addr] at h
  refine ⟨t16,(((((((((((((((a1.trans a2).trans a3).trans a4).trans a5).trans a6).trans a7).trans a8).trans a9).trans a10).trans a11).trans a12).trans a13).trans a14).trans a15).trans a16),f16,ip16,?_,?_⟩
  · simpa only [borrow,subWord,BitVec.sub_eq_add_neg,BitVec.add_assoc,
      BitVec.ofNat_eq_ofNat,BitVec.zero_add,BitVec.neg_zero] using value16
  · exact (((((((((((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).trans g8).trans g9).trans g10).trans g11).trans g12).trans g13).trans g14).trans g15).trans g16).mono (by
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
      grind only)

end P256.Proofs.Sec1.Affine.Compact.Compare
