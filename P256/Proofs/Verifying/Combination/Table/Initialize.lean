import P256.Proofs.Verifying.Combination.Table.Entry
import P256.Proofs.Verifying.Combination.Table.Setup
import P256.Proofs.Verifying.Combination.Table.Registers
import P256.Proofs.Verifying.Combination.Table.Arithmetic

set_option autoImplicit false

open P256.Proofs.Program (programLoaded_codeIn programText_slice readyToStep
  boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Verifying.Combination.Table

open P256.Proofs.Program

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def copiedCells (value : Projective) : Cells :=
  writeCell (writeCell (fun _ => none) 9 value) 10 value

theorem initialize_copies [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {cursor point : BitVec 64} {value : Projective}
    (pre : TablePre s boundary cursor point) (input : ProjectiveAt s point value) :
    ∃ fuel t, Advances boundary fuel s t ∧ Memory s t cursor point (copiedCells value) ∧
      t.RIP = 0x10b03d ∧ t.regValue .rbx = s.regValue .rdi ∧
      t.regValue .r14 = stackPtr s - 224 ∧ t.regValue .r15 = stackPtr s - 128 := by
  obtain ⟨n0, t0, run0, mem0, rip0, rbx0, rax0⟩ := entry pre
  obtain ⟨n1, t1, run1, ready1, _, effect1⟩ := firstCopySetup_correct boundary pre.outerBoundary t0
    (readyToStep mem0.machine mem0.bindingsSupported)
    (programText_slice (programLoaded_codeIn mem0.loaded) 0xb011 firstCopySetupBytes
      (by decide) (by decide +kernel)) rip0
  have agr1 : AgreesExcept [.reg 14, .reg 1, .reg 7, .reg 6, .rip] t0 t1 := effect1.agrees
  have mem1 := mem0.registers ready1 agr1 (by simp [Component.Covers]) (by simp) (by simp) (by simp)
  have w1 : t1.regValue .r14 = stackPtr t0 + 872 ∧ t1.regValue .rcx = 12 ∧
      t1.regValue .rdi = stackPtr t0 + 872 ∧ t1.regValue .rsi = t0.regValue .rax := effect1.writes
  obtain ⟨t2, run2, mem2, rip2, agr2⟩ := copy_source pre mem1 9 none (by decide)
    0xb024 (by decide) (by decide +kernel) effect1.rip
    (w1.2.2.1.trans (stack_address mem0.rsp (by decide)))
    (w1.2.2.2.trans rax0) w1.2.1 (input_at pre mem1.toFrameState input)
  have rax2 : t2.regValue .rax = point :=
    (agr2.read (n := 64) (r := 0) (by simp)).trans
      ((agr1.read (n := 64) (r := 0) (by simp)).trans rax0)
  have r14_2 : t2.regValue .r14 = stackPtr s - 224 :=
    (agr2.read (n := 64) (r := 14) (by simp)).trans
      (w1.1.trans (stack_address mem0.rsp (by decide)))
  have rbx2 : t2.regValue .rbx = s.regValue .rdi :=
    (agr2.read (n := 64) (r := 3) (by simp)).trans
      ((agr1.read (n := 64) (r := 3) (by simp)).trans rbx0)
  obtain ⟨n3, t3, run3, ready3, _, effect3⟩ := doubleCopySetup_correct boundary pre.outerBoundary t2
    (readyToStep mem2.machine mem2.bindingsSupported)
    (programText_slice (programLoaded_codeIn mem2.loaded) 0xb027 doubleCopySetupBytes
      (by decide) (by decide +kernel)) rip2
  have agr3 : AgreesExcept [.reg 15, .reg 1, .reg 7, .reg 6, .rip] t2 t3 := effect3.agrees
  have mem3 := mem2.registers ready3 agr3 (by simp [Component.Covers]) (by simp) (by simp) (by simp)
  have w3 : t3.regValue .r15 = stackPtr t2 + 968 ∧ t3.regValue .rcx = 12 ∧
      t3.regValue .rdi = stackPtr t2 + 968 ∧ t3.regValue .rsi = t2.regValue .rax := effect3.writes
  obtain ⟨t4, run4, mem4, rip4, agr4⟩ := copy_source pre mem3 10 none (by decide)
    0xb03a (by decide) (by decide +kernel) effect3.rip
    (w3.2.2.1.trans (stack_address mem2.rsp (by decide)))
    (w3.2.2.2.trans rax2) w3.2.1 (input_at pre mem3.toFrameState input)
  refine ⟨n0+n1+12+n3+12, t4, (((run0.trans run1).trans run2).trans run3).trans run4,
    mem4, rip4, ?_, ?_, ?_⟩
  · exact (agr4.read (n := 64) (r := 3) (by simp)).trans
      ((agr3.read (n := 64) (r := 3) (by simp)).trans rbx2)
  · exact (agr4.read (n := 64) (r := 14) (by simp)).trans
      ((agr3.read (n := 64) (r := 14) (by simp)).trans r14_2)
  · exact (agr4.read (n := 64) (r := 15) (by simp)).trans
      (w3.1.trans (stack_address mem2.rsp (by decide)))

def initialCells (value : Projective) : Cells :=
  writeCell (writeCell (writeCell (copiedCells value) 10 value.double) 8 value.double) 0 value

theorem initialize_table [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {cursor point : BitVec 64} {value : Projective}
    (pre : TablePre s boundary cursor point) (input : ProjectiveAt s point value) :
    ∃ fuel t, Advances boundary fuel s t ∧ Memory s t cursor point (initialCells value) ∧
      Registers s t ∧ t.RIP = 0x10b06e := by
  obtain ⟨n0, t0, run0, mem0, rip0, rbx0, r14_0, r15_0⟩ := initialize_copies pre input
  obtain ⟨t1, run1, ready1, effect1⟩ :=
    (mov_r64_r64_effect_step 0x10b03d 0x4c 0xff (by simp [RexWPrefix]) rfl).advances
      (readyToStep mem0.machine mem0.bindingsSupported)
      (programText_slice (programLoaded_codeIn mem0.loaded) 0xb03d
        [0x4c,0x89,0xff] (by decide) (by decide +kernel)) rip0
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xb040 (by decide)))
  have agr1 : AgreesExcept [.reg 7, .rip] t0 t1 := effect1.agrees
  have mem1 := mem0.registers ready1 agr1 (by simp [Component.Covers]) (by simp) (by simp) (by simp)
  have dst1 : t1.regValue .rdi = stackPtr s - 128 :=
    (show t1.regValue .rdi = t0.regValue .r15 from effect1.writes).trans r15_0
  obtain ⟨t2, result2⟩ := double_cells pre mem1 effect1.rip dst1 (mem1.cells 10 value (by rfl))
  have mem2 := result2.toMemory
  obtain ⟨n2, run2⟩ := result2.execution
  have rbx2 : t2.regValue .rbx = s.regValue .rdi :=
    (result2.registers .rbx (by simp)).trans ((agr1.read (n := 64) (r := 3) (by simp)).trans rbx0)
  have r14_2 : t2.regValue .r14 = stackPtr s - 224 :=
    (result2.registers .r14 (by simp)).trans ((agr1.read (n := 64) (r := 14) (by simp)).trans r14_0)
  have r15_2 : t2.regValue .r15 = stackPtr s - 128 :=
    (result2.registers .r15 (by simp)).trans ((agr1.read (n := 64) (r := 15) (by simp)).trans r15_0)
  obtain ⟨n3, t3, run3, ready3, _, effect3⟩ := doubledCopySetup_correct boundary pre.outerBoundary t2
    (readyToStep mem2.machine mem2.bindingsSupported)
    (programText_slice (programLoaded_codeIn mem2.loaded) 0xb045 doubledCopySetupBytes
      (by decide) (by decide +kernel)) result2.rip
  have agr3 : AgreesExcept [.reg 12, .reg 1, .reg 7, .reg 6, .rip] t2 t3 := effect3.agrees
  have mem3 := mem2.registers ready3 agr3 (by simp [Component.Covers]) (by simp) (by simp) (by simp)
  have w3 : t3.regValue .r12 = stackPtr t2 + 776 ∧ t3.regValue .rcx = 12 ∧
      t3.regValue .rdi = stackPtr t2 + 776 ∧ t3.regValue .rsi = t2.regValue .r15 := effect3.writes
  obtain ⟨t4, run4, mem4, rip4, agr4⟩ := copy_source pre mem3 8 (some 10) (by decide)
    0xb058 (by decide) (by decide +kernel) effect3.rip
    (w3.2.2.1.trans (stack_address mem2.rsp (by decide)))
    (w3.2.2.2.trans r15_2) w3.2.1 (mem3.cells 10 value.double (by rfl))
  have rbx4 : t4.regValue .rbx = s.regValue .rdi :=
    (agr4.read (n := 64) (r := 3) (by simp)).trans ((agr3.read (n := 64) (r := 3) (by simp)).trans rbx2)
  have r14_4 : t4.regValue .r14 = stackPtr s - 224 :=
    (agr4.read (n := 64) (r := 14) (by simp)).trans ((agr3.read (n := 64) (r := 14) (by simp)).trans r14_2)
  have r12_4 : t4.regValue .r12 = stackPtr s - 320 :=
    (agr4.read (n := 64) (r := 12) (by simp)).trans (w3.1.trans (stack_address mem2.rsp (by decide)))
  obtain ⟨n5, t5, run5, ready5, _, effect5⟩ := tableStartSetup_correct boundary pre.outerBoundary t4
    (readyToStep mem4.machine mem4.bindingsSupported)
    (programText_slice (programLoaded_codeIn mem4.loaded) 0xb05b tableStartSetupBytes
      (by decide) (by decide +kernel)) rip4
  have agr5 : AgreesExcept [.reg 15, .reg 1, .reg 7, .reg 6, .rip] t4 t5 := effect5.agrees
  have mem5 := mem4.registers ready5 agr5 (by simp [Component.Covers]) (by simp) (by simp) (by simp)
  have w5 : t5.regValue .r15 = stackPtr t4 + 8 ∧ t5.regValue .rcx = 12 ∧
      t5.regValue .rdi = stackPtr t4 + 8 ∧ t5.regValue .rsi = t4.regValue .r14 := effect5.writes
  obtain ⟨t6, run6, mem6, rip6, agr6⟩ := copy_source pre mem5 0 (some 9) (by decide)
    0xb06b (by decide) (by decide +kernel) effect5.rip
    (w5.2.2.1.trans (stack_address mem4.rsp (by decide)))
    (w5.2.2.2.trans r14_4) w5.2.1 (mem5.cells 9 value (by rfl))
  have regs5 : Registers s t5 :=
    ⟨(agr5.read (n := 64) (r := 3) (by simp)).trans rbx4,
      (agr5.read (n := 64) (r := 12) (by simp)).trans r12_4,
      (agr5.read (n := 64) (r := 14) (by simp)).trans r14_4,
      w5.1.trans (stack_address mem4.rsp (by decide))⟩
  exact ⟨n0+1+n2+n3+12+n5+12, t6,
    (((((run0.trans run1).trans run2).trans run3).trans run4).trans run5).trans run6,
    mem6, regs5.agrees agr6 (by simp) (by simp) (by simp) (by simp), rip6⟩

end P256.Proofs.Verifying.Combination.Table
