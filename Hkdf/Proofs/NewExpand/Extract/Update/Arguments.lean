import Hkdf.Proofs.NewExpand.Extract.State
import Hkdf.Proofs.Common.EffectCompose.Advance
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Mov.Triple

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Extract.Update

open Hkdf.Spec.Program Hkdf.Proofs.Common Hkdf.Proofs.Common.Machine
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

inductive CopyPath where
  | short
  | residual

def CopyPath.offset : CopyPath → Nat
  | .short => 0xfc69
  | .residual => 0xfcba

def CopyPath.pc (path : CopyPath) : BitVec 64 :=
  Extracted.textAddress + BitVec.ofNat 64 path.offset

def CopyPath.source : CopyPath → Syntax.Reg
  | .short => .r15
  | .residual => .r12

private def CopyPath.modrm : CopyPath → UInt8
  | .short => 0xfe
  | .residual => 0xe6

private def CopyPath.bytes (path : CopyPath) : List UInt8 :=
  [0x48,0x8d,0x7c,0x24,0x78,0x4c,0x89,path.modrm,0x4c,0x89,0xf2]

theorem arguments [Bindings] {s : RamState} {boundary : ReturnBoundary} (path : CopyPath)
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (outside : ¬ InProgram boundary.rip)
    (rip : s.RIP = path.pc) :
    ∃ t, Advances boundary 3 s t ∧ ReadyToStep t ∧
      t.RIP = path.pc + (11 : BitVec 64) ∧ t.regValue .rdi = stackPtr s + 120 ∧
      t.regValue .rsi = s.regValue path.source ∧ t.regValue .rdx = s.regValue .r14 ∧
      AgreesExcept [.reg 7,.reg 6,.reg 2,.rip] s t := by
  have code : CodeIn (codeRange path.pc path.bytes) s :=
    programText_slice (programLoaded_codeIn loaded) path.offset path.bytes
      (by cases path <;> decide) (by cases path <;> decide +kernel)
  have next (i : Nat) (small : i ≤ 11) : path.pc + BitVec.ofNat 64 i ≠ boundary.rip := by
    apply boundary_ne_program outside
    unfold CopyPath.pc
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    apply inProgram_of_textOffset
    cases path <;> simp only [CopyPath.offset] <;> omega
  obtain ⟨u, first, ru, lea⟩ :=
    (lea_r64_effect_step path.pc 0x48 (by simp [RexWPrefix]) 7
      (.sib 4 none 0 (.d8 120)) (by decide) rfl rfl).advances ready
        (code.mono (by
        have slice := codeRange_slice_subset path.pc path.bytes 0 5
        cases path <;> exact slice)) rip (next 5 (by decide))
  have a : AgreesExcept [.reg 7,.rip] s u := lea.agrees
  have codeU := a.codeIn (by simp [Component.Covers]) code
  have instr : StepEffect (fun u : RamState => u.RIP = path.pc + (5 : BitVec 64))
      (codeRange (path.pc + (5 : BitVec 64)) [0x4c,0x89,path.modrm])
      (movR64R64Effect (path.pc + (5 : BitVec 64)) 6 (match path with | .short => 15 | .residual => 12)) := by
    cases path
    · exact mov_r64_r64_effect_step _ 0x4c 0xfe (by simp [RexWPrefix]) rfl
    · exact mov_r64_r64_effect_step _ 0x4c 0xe6 (by simp [RexWPrefix]) rfl
  obtain ⟨v, second, rv, src⟩ := instr.advances ru
    (codeU.mono (by
        have slice := codeRange_slice_subset path.pc path.bytes 5 3
        cases path <;> exact slice)) lea.rip
    (by cases path <;> exact next 8 (by decide))
  have b : AgreesExcept [.reg 6,.rip] u v := src.agrees
  have codeV := b.codeIn (by simp [Component.Covers]) codeU
  obtain ⟨t, third, rt, len⟩ :=
    (mov_r64_r64_effect_step (path.pc + (8 : BitVec 64)) 0x4c 0xf2 (by simp [RexWPrefix]) rfl).advances rv
      (codeV.mono (by
        have slice := codeRange_slice_subset path.pc path.bytes 8 3
        cases path <;> exact slice))
      (by cases path <;> exact src.rip) (by cases path <;> exact next 11 (by decide))
  have c : AgreesExcept [.reg 2,.rip] v t := len.agrees
  refine ⟨t, (first.trans second).trans third, rt, ?_, ?_, ?_, ?_, ?_⟩
  · cases path <;> exact len.rip
  · have dest : u.regValue .rdi = stackPtr s + 120 := by
      have value : u.regValue .rdi = rspOf s + 120 := lea.writes
      simpa only [show rspOf s = stackPtr s from Operand.read_reg64 s 4] using value
    exact (c.read (n := 64) (r := 7) (by decide)).trans
      ((b.read (n := 64) (r := 7) (by decide)).trans dest)
  · have source : v.regValue .rsi = u.regValue path.source := by cases path <;> exact src.writes
    apply (c.read (n := 64) (r := 6) (by decide)).trans
    apply source.trans
    cases path
    · exact a.read (n := 64) (r := 15) (by decide)
    · exact a.read (n := 64) (r := 12) (by decide)
  · have length : t.regValue .rdx = v.regValue .r14 := len.writes
    exact length.trans ((b.read (n := 64) (r := 14) (by decide)).trans
      (a.read (n := 64) (r := 14) (by decide)))
  · exact ((a.trans b).trans c).mono (by decide)

end Hkdf.Proofs.NewExpand.Extract.Update
