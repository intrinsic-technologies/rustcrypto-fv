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

theorem word0 [Bindings] {s t : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    (pre : AffineDecodePre s boundary bytes) (frame : Frame s t)
    (rip : t.RIP=0x1103d8) (a b _c : BitVec 64)
    (left : memLoad t.external ((stackPtr s-760)+344) 64=a)
    (right : memLoad t.external ((stackPtr s-760)+576) 64=b)
    : ∃ u, Advances boundary 12 t u ∧ Frame s u ∧ u.RIP=0x11040c ∧
      memLoad u.external (stackPtr s-512) 64=borrow a b (a-b) ∧
      AgreesExcept [.reg 0,.reg 1,.reg 2,.reg 6,.reg 7,.flags,.rip,.mem (stackPtr s-512) 8] t u := by
  have addr1 (next : BitVec 64) : (AddrMode.sib 4 none 0 (.d32 344)).addr t next=(stackPtr s-760)+344 := by
    change stackPtr t+344#64=_
    rw [frame.rsp]
    rfl
  have read1 : MemReadable t ((stackPtr s-760)+344) 8 := by
    have h := ScalarFrame.stack_readable (frameOffset := 760) pre.toCalleePre frame
      (offset := 344) (len := 8) (by decide) (by decide)
    rw [frame.rsp] at h
    exact h
  have mem1 : memLoad t.external ((stackPtr s-760)+344) 64=a := by
    exact left
  obtain ⟨t1,a1,f1,ip1,v1,g1,m1⟩ := frame_load_r64 pre.outerBoundary frame
      0x103d8 0x48 0 (AddrMode.sib 4 none 0 (.d32 344)) (by simp [RexWPrefix]) (by decide) rfl rfl
      (by decide) rip (by decide) (by decide +kernel) (by rw [addr1]; exact read1)
  change AgreesExcept [.reg 0,.rip] t t1 at g1
  have value1 : t1.regValue .rax=a := by
    rw [addr1] at v1
    exact v1.trans mem1
  have addr2 (next : BitVec 64) : (AddrMode.sib 4 none 0 (.d32 576)).addr t1 next=(stackPtr s-760)+576 := by
    change stackPtr t1+576#64=_
    rw [f1.rsp]
    rfl
  have read2 : MemReadable t1 ((stackPtr s-760)+576) 8 := by
    have h := ScalarFrame.stack_readable (frameOffset := 760) pre.toCalleePre f1
      (offset := 576) (len := 8) (by decide) (by decide)
    rw [f1.rsp] at h
    exact h
  have mem2 : memLoad t1.external ((stackPtr s-760)+576) 64=b := by
    rw [g1.external (by simp [Component.Covers])]
    exact right
  obtain ⟨t2,a2,f2,ip2,v2,g2,m2⟩ := frame_load_r64 pre.outerBoundary f1
      0x103e0 0x48 1 (AddrMode.sib 4 none 0 (.d32 576)) (by simp [RexWPrefix]) (by decide) rfl rfl
      (by decide) ip1 (by decide) (by decide +kernel) (by rw [addr2]; exact read2)
  change AgreesExcept [.reg 1,.rip] t1 t2 at g2
  have value2 : t2.regValue .rcx=b := by
    rw [addr2] at v2
    exact v2.trans mem2
  have r3_0 : t2.regValue .rax=a := (g2.read (n := 64) (r := 0) (by simp)).trans value1
  obtain ⟨t3,a3,ready3,effect3⟩ := (mov_r64_r64_effect_step 0x1103e8 0x48 0xc2 (by simp [RexWPrefix]) rfl).advances
    (readyToStep f2.machine f2.bindingsSupported)
    (programText_slice (programLoaded_codeIn f2.loaded) 0x103e8 _ (by decide) (by decide +kernel))
    ip2 (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x103eb (by decide)))
  have g3 : AgreesExcept [.reg 2,.rip] t2 t3 := effect3.agrees
  have f3 := f2.after_registers ready3 g3 (by simp [Component.Covers]) (by simp)
  have ip3 : t3.RIP=0x1103eb := effect3.rip
  have value3 : t3.regValue .rdx=a := by
    have h := effect3.writes
    change t3.regValue .rdx=t2.regValue .rax at h
    rw [r3_0] at h
    exact h
  have r4_1 : t3.regValue .rcx=b := (g3.read (n := 64) (r := 1) (by simp)).trans value2
  obtain ⟨t4,a4,ready4,effect4⟩ := (sub_r64_r64_effect_step 0x1103eb 0x48 0xca (by simp [RexWPrefix]) rfl).advances
    (readyToStep f3.machine f3.bindingsSupported)
    (programText_slice (programLoaded_codeIn f3.loaded) 0x103eb _ (by decide) (by decide +kernel))
    ip3 (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x103ee (by decide)))
  have g4 : AgreesExcept [.reg 2,.flags,.rip] t3 t4 := effect4.agrees
  have f4 := f3.after_registers ready4 g4 (by simp [Component.Covers]) (by simp)
  have ip4 : t4.RIP=0x1103ee := effect4.rip
  have value4 : t4.regValue .rdx=(a) - (b) := by
    have h := effect4.writes
    change t4.regValue .rdx=(t3.regValue .rdx) - (t3.regValue .rcx) at h
    rw [r4_1,value3] at h
    exact h
  have r5_0 : t4.regValue .rax=a := (((g2.trans g3).trans g4).read (n := 64) (r := 0) (by simp)).trans value1
  obtain ⟨t5,a5,ready5,effect5⟩ := (not_r64_effect_step 0x1103ee 0x48 0xd0 (by simp [RexWPrefix]) rfl rfl).advances
    (readyToStep f4.machine f4.bindingsSupported)
    (programText_slice (programLoaded_codeIn f4.loaded) 0x103ee _ (by decide) (by decide +kernel))
    ip4 (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x103f1 (by decide)))
  have g5 : AgreesExcept [.reg 0,.rip] t4 t5 := effect5.agrees
  have f5 := f4.after_registers ready5 g5 (by simp [Component.Covers]) (by simp)
  have ip5 : t5.RIP=0x1103f1 := effect5.rip
  have value5 : t5.regValue .rax= ~~~(a) := by
    have h := effect5.writes
    change t5.regValue .rax= ~~~(t4.regValue .rax) at h
    rw [r5_0] at h
    exact h
  have r6_1 : t5.regValue .rcx=b := (((g3.trans g4).trans g5).read (n := 64) (r := 1) (by simp)).trans value2
  obtain ⟨t6,a6,ready6,effect6⟩ := (mov_r64_r64_effect_step 0x1103f1 0x48 0xce (by simp [RexWPrefix]) rfl).advances
    (readyToStep f5.machine f5.bindingsSupported)
    (programText_slice (programLoaded_codeIn f5.loaded) 0x103f1 _ (by decide) (by decide +kernel))
    ip5 (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x103f4 (by decide)))
  have g6 : AgreesExcept [.reg 6,.rip] t5 t6 := effect6.agrees
  have f6 := f5.after_registers ready6 g6 (by simp [Component.Covers]) (by simp)
  have ip6 : t6.RIP=0x1103f4 := effect6.rip
  have value6 : t6.regValue .rsi=b := by
    have h := effect6.writes
    change t6.regValue .rsi=t5.regValue .rcx at h
    rw [r6_1] at h
    exact h
  have r7_0 : t6.regValue .rax= ~~~(a) := (g6.read (n := 64) (r := 0) (by simp)).trans value5
  obtain ⟨t7,a7,ready7,effect7⟩ := (and_r64_r64_effect_step 0x1103f4 0x48 0xc6 (by simp [RexWPrefix]) rfl).advances
    (readyToStep f6.machine f6.bindingsSupported)
    (programText_slice (programLoaded_codeIn f6.loaded) 0x103f4 _ (by decide) (by decide +kernel))
    ip6 (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x103f7 (by decide)))
  have g7 : AgreesExcept [.reg 6,.flags,.rip] t6 t7 := effect7.agrees
  have f7 := f6.after_registers ready7 g7 (by simp [Component.Covers]) (by simp)
  have ip7 : t7.RIP=0x1103f7 := effect7.rip
  have value7 : t7.regValue .rsi=(b) &&& (~~~(a)) := by
    have h := effect7.writes
    change t7.regValue .rsi=(t6.regValue .rsi) &&& (t6.regValue .rax) at h
    rw [r7_0,value6] at h
    exact h
  have r8_1 : t7.regValue .rcx=b := (((((g3.trans g4).trans g5).trans g6).trans g7).read (n := 64) (r := 1) (by simp)).trans value2
  have r8_0 : t7.regValue .rax= ~~~(a) := ((g6.trans g7).read (n := 64) (r := 0) (by simp)).trans value5
  obtain ⟨t8,a8,ready8,effect8⟩ := (or_r64_r64_effect_step 0x1103f7 0x48 0xc8 (by simp [RexWPrefix]) rfl).advances
    (readyToStep f7.machine f7.bindingsSupported)
    (programText_slice (programLoaded_codeIn f7.loaded) 0x103f7 _ (by decide) (by decide +kernel))
    ip7 (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x103fa (by decide)))
  have g8 : AgreesExcept [.reg 0,.flags,.rip] t7 t8 := effect8.agrees
  have f8 := f7.after_registers ready8 g8 (by simp [Component.Covers]) (by simp)
  have ip8 : t8.RIP=0x1103fa := effect8.rip
  have value8 : t8.regValue .rax=(~~~(a)) ||| (b) := by
    have h := effect8.writes
    change t8.regValue .rax=(t7.regValue .rax) ||| (t7.regValue .rcx) at h
    rw [r8_1,r8_0] at h
    exact h
  have r9_2 : t8.regValue .rdx=(a) - (b) := ((((g5.trans g6).trans g7).trans g8).read (n := 64) (r := 2) (by simp)).trans value4
  obtain ⟨t9,a9,ready9,effect9⟩ := (and_r64_r64_effect_step 0x1103fa 0x48 0xd0 (by simp [RexWPrefix]) rfl).advances
    (readyToStep f8.machine f8.bindingsSupported)
    (programText_slice (programLoaded_codeIn f8.loaded) 0x103fa _ (by decide) (by decide +kernel))
    ip8 (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x103fd (by decide)))
  have g9 : AgreesExcept [.reg 0,.flags,.rip] t8 t9 := effect9.agrees
  have f9 := f8.after_registers ready9 g9 (by simp [Component.Covers]) (by simp)
  have ip9 : t9.RIP=0x1103fd := effect9.rip
  have value9 : t9.regValue .rax=((~~~(a)) ||| (b)) &&& ((a) - (b)) := by
    have h := effect9.writes
    change t9.regValue .rax=(t8.regValue .rax) &&& (t8.regValue .rdx) at h
    rw [r9_2,value8] at h
    exact h
  have r10_6 : t9.regValue .rsi=(b) &&& (~~~(a)) := ((g8.trans g9).read (n := 64) (r := 6) (by simp)).trans value7
  obtain ⟨t10,a10,ready10,effect10⟩ := (or_r64_r64_effect_step 0x1103fd 0x48 0xf0 (by simp [RexWPrefix]) rfl).advances
    (readyToStep f9.machine f9.bindingsSupported)
    (programText_slice (programLoaded_codeIn f9.loaded) 0x103fd _ (by decide) (by decide +kernel))
    ip9 (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x10400 (by decide)))
  have g10 : AgreesExcept [.reg 0,.flags,.rip] t9 t10 := effect10.agrees
  have f10 := f9.after_registers ready10 g10 (by simp [Component.Covers]) (by simp)
  have ip10 : t10.RIP=0x110400 := effect10.rip
  have value10 : t10.regValue .rax=(((~~~(a)) ||| (b)) &&& ((a) - (b))) ||| ((b) &&& (~~~(a))) := by
    have h := effect10.writes
    change t10.regValue .rax=(t9.regValue .rax) ||| (t9.regValue .rsi) at h
    rw [r10_6,value9] at h
    exact h
  obtain ⟨t11,a11,ready11,effect11⟩ := (shr_r64_imm8_effect_step 0x110400 0x48 0xe8 63 (by simp [RexWPrefix]) rfl rfl).advances
    (readyToStep f10.machine f10.bindingsSupported)
    (programText_slice (programLoaded_codeIn f10.loaded) 0x10400 _ (by decide) (by decide +kernel))
    ip10 (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x10404 (by decide)))
  have g11 : AgreesExcept [.reg 0,.flags,.rip] t10 t11 := effect11.agrees
  have f11 := f10.after_registers ready11 g11 (by simp [Component.Covers]) (by simp)
  have ip11 : t11.RIP=0x110404 := effect11.rip
  have value11 : t11.regValue .rax=((((~~~(a)) ||| (b)) &&& ((a) - (b))) ||| ((b) &&& (~~~(a)))) >>> 63 := by
    have h := effect11.writes
    change t11.regValue .rax=(t10.regValue .rax) >>> 63 at h
    rw [value10] at h
    exact h
  obtain ⟨t12,a12,f12,ip12,v12,g12,m12⟩ := frame_store_r64 pre.toCalleePre f11
    0x10404 248 (.d32 248) 0x48 0 (by simp [RexWPrefix]) rfl rfl rfl
    (by decide) ip11 (by decide) (by decide +kernel)
  have scratch12 : (stackPtr s-760)+248=stackPtr s-512 := by
    simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]; rfl
  change AgreesExcept [.mem ((stackPtr s-760)+248) 8,.rip] t11 t12 at g12
  rw [scratch12] at g12
  have value12 : memLoad t12.external (stackPtr s-512) 64=((((~~~(a)) ||| (b)) &&& ((a) - (b))) ||| ((b) &&& (~~~(a)))) >>> 63 := by
    have h := v12
    change memLoad t12.external ((stackPtr s-760)+248) 64=t11.regValue .rax at h
    rw [value11] at h
    have addr : (stackPtr s-760)+248=stackPtr s-512 := by
      simp only [BitVec.sub_eq_add_neg,BitVec.add_assoc]; rfl
    rwa [addr] at h
  refine ⟨t12,(((((((((((a1.trans a2).trans a3).trans a4).trans a5).trans a6).trans a7).trans a8).trans a9).trans a10).trans a11).trans a12),f12,ip12,?_,?_⟩
  · simpa only [borrow,subWord,BitVec.sub_eq_add_neg,BitVec.add_assoc,
      BitVec.ofNat_eq_ofNat,BitVec.zero_add,BitVec.neg_zero] using value12
  · exact (((((((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).trans g8).trans g9).trans g10).trans g11).trans g12).mono (by
      simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
      grind only)

end P256.Proofs.Sec1.Affine.Compact.Compare
