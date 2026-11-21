import P256.Proofs.Verifying.Combination.Table.Site
import P256.Proofs.Verifying.Combination.Table.Arithmetic

set_option autoImplicit false

open P256.Proofs.Program (programLoaded_codeIn programText_slice readyToStep
  inProgram_of_textOffset)
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Projective.Multiply.Machine.Loop (CallSite)

namespace P256.Proofs.Verifying.Combination.Table

open P256.Proofs.Program

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem add_current [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {cursor point : BitVec 64} {cells : Cells} {left right : Projective}
    (pre : TablePre s boundary cursor point) (state : Memory s t cursor point cells)
    (regs : Registers s t) (site : AddSite)
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 site.offset)
    (leftCell : cells 9 = some left) (rightCell : cells 8 = some right) :
    ∃ fuel u, Advances boundary fuel t u ∧
      Memory s u cursor point (writeCell cells 9 (left.add right)) ∧
      Registers s u ∧ u.RIP = site.call.returnRip := by
  have mid : InProgram (Extracted.textAddress + BitVec.ofNat 64 site.offset + 3#64) := by
    simpa only [BitVec.ofNat_add, BitVec.add_assoc] using
      inProgram_of_textOffset (site.offset + 3) (by have := site.bounded; omega)
  have stop : InProgram (Extracted.textAddress + BitVec.ofNat 64 site.offset + 6#64) := by
    simpa only [BitVec.ofNat_add, BitVec.add_assoc] using
      inProgram_of_textOffset (site.offset + 6) site.bounded
  obtain ⟨n, v, run, ready, _, effect⟩ :=
    add_setup boundary pre.outerBoundary _ mid stop t
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) site.offset addSetupBytes
        (by simpa [addSetupBytes] using Nat.le_of_lt site.bounded) site.bytes) rip
  have agr : AgreesExcept [.reg 7, .reg 6, .rip] t v := effect.agrees
  have mem := state.registers ready agr (by simp [Component.Covers]) (by simp) (by simp) (by simp)
  have regsV := regs.agrees agr (by simp) (by simp) (by simp) (by simp)
  have writes : v.regValue .rdi = t.regValue .r14 ∧ v.regValue .rsi = t.regValue .r12 := effect.writes
  have ripV : v.RIP = Extracted.textAddress + BitVec.ofNat 64 site.call.offset := by
    rw [site.callOffset, BitVec.ofNat_add, ← BitVec.add_assoc]
    exact effect.rip
  obtain ⟨u, result⟩ := add_cells pre mem site.call ripV
    (writes.1.trans regs.r14) (writes.2.trans regs.r12)
    (mem.cells 9 left leftCell) (mem.cells 8 right rightCell)
  obtain ⟨m, run'⟩ := result.execution
  exact ⟨n+m, u, run.trans run', result.toMemory, regsV.abi result.registers, result.rip⟩

theorem copy_current [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {cursor point : BitVec 64} {cells : Cells} {value : Projective}
    (pre : TablePre s boundary cursor point) (state : Memory s t cursor point cells)
    (regs : Registers s t) (slot : Slot) (hne : slot ≠ 9) (site : CopySite slot)
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 site.startOffset)
    (cell : cells 9 = some value) :
    ∃ fuel u, Advances boundary fuel t u ∧
      Memory s u cursor point (writeCell cells slot value) ∧ Registers s u ∧
      u.RIP = Extracted.textAddress + BitVec.ofNat 64 site.endOffset + 3#64 := by
  obtain ⟨n, v, run, ready, _, effect⟩ := site.correct boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) site.startOffset site.bytes
      site.bounded site.extracted) rip
  have agr : AgreesExcept [.reg 7, .reg 1, .reg 6, .rip] t v := effect.agrees
  have mem := state.registers ready agr (by simp [Component.Covers]) (by simp) (by simp) (by simp)
  have regsV := regs.agrees agr (by simp) (by simp) (by simp) (by simp)
  have writes : v.regValue .rdi = stackPtr t + BitVec.ofNat 64 (1096-offset slot) ∧
      v.regValue .rcx = 12 ∧ v.regValue .rsi = t.regValue .r14 := effect.writes
  have dst : v.regValue .rdi = stackPtr s - BitVec.ofNat 64 (offset slot) := by
    apply writes.1.trans
    have hb : offset slot ≤ 1096 := by have := offset_bounds slot; omega
    simpa only [Nat.sub_sub_self hb] using
      stack_address (offset := 1096-offset slot) state.rsp (by omega)
  obtain ⟨u, run', mem', rip', agr'⟩ := copy_source pre mem slot (some 9)
    (by simpa using Ne.symm hne) site.endOffset site.copyBound site.copyBytes effect.rip
    dst (writes.2.2.trans regs.r14) writes.2.1 (mem.cells 9 value cell)
  exact ⟨n+12, u, run.trans run', mem',
    regsV.agrees agr' (by simp) (by simp) (by simp) (by simp), rip'⟩

theorem add_copy_current [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {cursor point : BitVec 64} {cells : Cells} {left right : Projective}
    (pre : TablePre s boundary cursor point) (state : Memory s t cursor point cells)
    (regs : Registers s t) (addSite : AddSite) (slot : Slot) (hne : slot ≠ 9)
    (copySite : CopySite slot) (connected : addSite.call.returnRip =
      Extracted.textAddress + BitVec.ofNat 64 copySite.startOffset)
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 addSite.offset)
    (leftCell : cells 9 = some left) (rightCell : cells 8 = some right) :
    ∃ fuel u, Advances boundary fuel t u ∧
      Memory s u cursor point (writeCell (writeCell cells 9 (left.add right)) slot (left.add right)) ∧
      Registers s u ∧ u.RIP = Extracted.textAddress + BitVec.ofNat 64 copySite.endOffset + 3#64 := by
  obtain ⟨n, v, run, mem, regsV, ripV⟩ := add_current pre state regs addSite rip leftCell rightCell
  obtain ⟨m, u, run', mem', regs', rip'⟩ := copy_current (value := left.add right) pre mem regsV slot hne copySite
    (ripV.trans connected) (by simp [writeCell])
  exact ⟨n+m, u, run.trans run', mem', regs', rip'⟩

end P256.Proofs.Verifying.Combination.Table
