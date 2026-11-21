import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.Entry
import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.ExponentCopy
import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.Guard
import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.BitCount
import P256.Proofs.Sec1.SquareRoot.Exponent.Frame
import P256.Proofs.Sec1.SquareRoot.Exponent.Preservation
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.ExponentInitialize

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def prefixMemory (s : RamState) : Ram :=
  memStore (exponentCopyMemory s (inputCopyMemory s (saveMemory s)))
    (exponentFrameBase s + 0x2a0) (s.regValue .rdi)

structure PrefixState [Bindings] (s t : RamState) : Prop where
  frame : ExponentFrame s t
  rip : t.RIP = 0x114c3b
  memory : t.external = prefixMemory s
  firstTable : t.regValue .rax = exponentFrameBase s + 0xc0
  count : t.regValue .r14 = 254
  parameter : t.regValue .r15 = s.regValue .rsi + 32
  input : t.regValue .rsi = s.regValue .rsi
  exponent : t.regValue .rdx = 0x202fb8

theorem initialize_prefix [Bindings] {s : RamState} {boundary : ReturnBoundary} {x : Nat}
    (ctx : ExponentPre s boundary x) :
    ∃ u, Advances boundary 32 s u ∧ PrefixState s u := by
  obtain ⟨t, entry⟩ := initialize_input ctx
  have entryReg (r : BitVec 5) (hr : r ≠ 4 ∧ r ≠ 15 ∧ r ≠ 0 ∧ r ≠ 8) :
      (Operand.reg r : Operand 64).read t = (Operand.reg r : Operand 64).read s :=
    entry.agrees.read (by simpa [saveComponents, saveFrame, inputCopyComponents] using hr)
  obtain ⟨v, run1, frame1, rip1, agrees1, memory1⟩ := copy_exponent ctx entry.frame entry.rip
    ((entryReg 2 (by decide)).trans ctx.exponent)
  have count1 : (Operand.reg 1 : Operand 32).read v = 254 :=
    congrArg (BitVec.setWidth 32)
      ((agrees1.read (n := 64) (r := 1) (by simp [exponentCopyComponents])).trans
        ((entryReg 1 (by decide)).trans ctx.bits))
  obtain ⟨w, run2, ready2, rip2, agrees2⟩ := bits_guard
    (readyToStep frame1.machine frame1.bindingsSupported) frame1.loaded ctx.outerBoundary rip1 count1
  have frame2 := frame1.after_registers ready2 agrees2 (by simp [Component.Covers]) (by decide)
  obtain ⟨a, run3, frame3, rip3, output3, agrees3, memory3⟩ := frame_store_r64 ctx.toCalleePre
    frame2 0x14c1a 0x2a0 (.d32 0x2a0) 0x48 7 (by simp [RexWPrefix]) rfl rfl rfl
    (by decide) rip2 (by decide) (by decide +kernel)
  have output2 : w.regValue .rdi = s.regValue .rdi :=
    (agrees2.read (n := 64) (r := 7) (by decide)).trans
      ((agrees1.read (n := 64) (r := 7) (by simp [exponentCopyComponents])).trans
        (entryReg 7 (by decide)))
  have output3' : exponentWordAt a (exponentFrameBase s + 0x2a0) (s.regValue .rdi) := by
    exact output3.trans output2
  have exponentFrame3 := ExponentFrame.of_scalarFrame frame3 output3'
  have count3 : (Operand.reg 1 : Operand 32).read a = 254 :=
    (agrees3.read (by simp)).trans ((agrees2.read (by decide)).trans count1)
  obtain ⟨b, run4, ready4, rip4, count4, agrees4⟩ := bit_count
    (readyToStep frame3.machine frame3.bindingsSupported) frame3.loaded ctx.outerBoundary rip3 count3
  have frame4 := exponentFrame3.of_registers ready4 agrees4 (by decide) (by simp [Component.Covers])
  obtain ⟨u, run5, ready5, effect5⟩ := (lea_r64_effect_step 0x114c33 0x48 (by simp [RexWPrefix])
      0 (.sib 4 none 0 (.d32 0xc0)) (by decide) rfl rfl).advances ready4
      (programText_slice (programLoaded_codeIn frame4.loaded) 0x14c33 _
        (by decide) (by decide +kernel)) rip4
      (boundary_ne_program ctx.outerBoundary (inProgram_of_textOffset 0x14c3b (by decide)))
  have agrees5 : AgreesExcept [.reg 0, .rip] b u := effect5.agrees
  have frame5 := frame4.of_registers ready5 agrees5 (by decide) (by simp [Component.Covers])
  have preserved (r : BitVec 5) (hr : r ≠ 0 ∧ r ≠ 8 ∧ r ≠ 14) :
      (Operand.reg r : Operand 64).read u = (Operand.reg r : Operand 64).read t := by
    apply (((((agrees1.trans agrees2).trans agrees3).trans agrees4).trans agrees5).read)
    simpa [exponentCopyComponents] using (show r ≠ 0 ∧ r ≠ 8 ∧ r ≠ 0 ∧ r ≠ 14 ∧ r ≠ 0 from
      ⟨hr.1, hr.2.1, hr.1, hr.2.2, hr.1⟩)
  refine ⟨u, ((((entry.execution.trans run1).trans run2).trans run3).trans run4).trans run5,
    ⟨frame5, effect5.rip, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · have mem2 := agrees2.external (by simp [Component.Covers])
    have mem4 := agrees4.external (by simp [Component.Covers])
    have mem5 := agrees5.external (by simp [Component.Covers])
    change a.external = memStore w.external (exponentFrameBase s + 0x2a0)
      (w.regValue .rdi) at memory3
    change u.external = memStore _ _ _
    simp only [mem5, mem4, memory3, mem2, memory1, entry.memory, output2]
  · have h : u.regValue .rax = b.regValue .rsp + 0xc0 := effect5.writes
    rwa [frame4.rsp] at h
  · exact (agrees5.read (n := 64) (r := 14) (by decide)).trans count4
  · exact (preserved 15 (by decide)).trans entry.parameter
  · exact (preserved 6 (by decide)).trans (entryReg 6 (by decide))
  · exact (preserved 2 (by decide)).trans ((entryReg 2 (by decide)).trans ctx.exponent)

end P256.Proofs.Sec1.SquareRoot.ExponentInitialize
