import Hkdf.Proofs.Program
import Hkdf.Proofs.Common.Machine.CallReturn
import Hkdf.Proofs.Common.Machine.Code
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.NopMem.Triple

set_option autoImplicit false

open Hkdf.Proofs.Program

namespace Hkdf.Proofs.Common.ExtractCaller.PadEntry

open Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Machine

theorem mov_eax_three_nop [bindings : Bindings] {s : RamState} {boundary : ReturnBoundary}
    {offset : Nat} {padding : List UInt8}
    (paddingStep : StepEffect
      (fun s ↦ s.RIP = Extracted.textAddress + BitVec.ofNat 64 (offset + 5))
      (codeRange (Extracted.textAddress + BitVec.ofNat 64 (offset + 5)) padding)
      (fun _ ↦ nopEffect (Extracted.textAddress + BitVec.ofNat 64 (offset + 5)) padding.length))
    (ready : ReadyToStep s) (machine : Hkdf.Proofs.Program.SupportedMachine bindings s)
    (loaded : ProgramLoaded s) (outside : ¬ InProgram boundary.rip)
    (rip : s.RIP = Extracted.textAddress + BitVec.ofNat 64 offset)
    (bounded : offset + 5 + padding.length < 115149)
    (movBytes : Extracted.textBytes.toListFrom offset 5 = [0xb8, 3, 0, 0, 0])
    (nopBytes : Extracted.textBytes.toListFrom (offset + 5) padding.length = padding) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧
      Hkdf.Proofs.Program.SupportedMachine bindings t ∧ ProgramLoaded t ∧
      t.RIP = Extracted.textAddress + BitVec.ofNat 64 (offset + 5 + padding.length) ∧
      t.regValue .rax = 3 ∧ AgreesExcept [.reg 0, .rip] s t ∧ t.external = s.external := by
  have movStep : StepEffect (fun s ↦ s.RIP = Extracted.textAddress + BitVec.ofNat 64 offset)
      (codeRange (Extracted.textAddress + BitVec.ofNat 64 offset) [0xb8, 3, 0, 0, 0])
      (movR32Imm32Effect (Extracted.textAddress + BitVec.ofNat 64 offset) 5 0 3) :=
    mov_r32_imm32_effect_step _ 0xb8 (by decide) 3
  have next : Extracted.textAddress + BitVec.ofNat 64 offset + 5 =
      Extracted.textAddress + BitVec.ofNat 64 (offset + 5) := by
    rw [BitVec.ofNat_add, ← BitVec.add_assoc]
    rfl
  obtain ⟨u, run1, readyU, effect1⟩ := movStep.advances ready
    (programText_slice (programLoaded_codeIn loaded) offset _
      (by change offset + 5 ≤ 115149; omega) movBytes) rip (by
      change Extracted.textAddress + BitVec.ofNat 64 offset + 5 ≠ boundary.rip
      rw [next]
      exact boundary_ne_program outside (inProgram_of_textOffset _ (by omega)))
  have frame1 : AgreesExcept [.reg 0, .rip] s u := effect1.agrees
  have codeU := CodeIn.of_external_eq (frame1.external (by simp [Component.Covers]))
    (programLoaded_codeIn loaded)
  have final : Extracted.textAddress + BitVec.ofNat 64 (offset + 5) +
      BitVec.ofNat 64 padding.length =
      Extracted.textAddress + BitVec.ofNat 64 (offset + 5 + padding.length) := by
    simp only [BitVec.ofNat_add, BitVec.add_assoc]
  obtain ⟨t, run2, readyT, effect2⟩ := paddingStep.advances readyU
    (programText_slice codeU (offset + 5) padding (by omega) nopBytes)
    (effect1.rip.trans next) (by
      change Extracted.textAddress + BitVec.ofNat 64 (offset + 5) +
        BitVec.ofNat 64 padding.length ≠ boundary.rip
      rw [final]
      exact boundary_ne_program outside (inProgram_of_textOffset _ bounded))
  have frame : AgreesExcept [.reg 0, .rip] s t :=
    (frame1.trans effect2.agrees).mono (by simp [nopEffect_components])
  have memory : t.external = s.external := frame.external (by simp [Component.Covers])
  have raxU : u.regValue .rax = 3 := effect1.writes
  have raxT : t.regValue .rax = u.regValue .rax :=
    effect2.agrees.read (n := 64) (r := 0) (by simp)
  refine ⟨t, run1.trans run2, readyT,
    Hkdf.Proofs.Common.Machine.supportedMachine_of_ready_agrees machine readyT frame,
    ?_, effect2.rip.trans final, raxT.trans raxU, frame, memory⟩
  intro a b hb
  rw [memory]
  exact loaded a b hb

theorem standard [bindings : Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (machine : Hkdf.Proofs.Program.SupportedMachine bindings s)
    (loaded : ProgramLoaded s) (outside : ¬ InProgram boundary.rip)
    (rip : s.RIP = 0x101497) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧
      Hkdf.Proofs.Program.SupportedMachine bindings t ∧ ProgramLoaded t ∧
      t.RIP = 0x1014a0 ∧ t.regValue .rax = 3 ∧
      AgreesExcept [.reg 0, .rip] s t ∧ t.external = s.external := by
  have paddingStep : StepEffect (fun s ↦ s.RIP = 0x10149c)
      (codeRange 0x10149c [0x0f, 0x1f, 0x40, 0])
      (fun _ ↦ nopEffect 0x10149c 4) :=
    nop_m_effect_step _ [] (by decide) (by decide) (.base 0 (.d8 0))
      ⟨by decide, fun h ↦ by cases h⟩ rfl rfl
  exact mov_eax_three_nop (offset := 0x1497) paddingStep ready machine loaded outside rip
    (by decide) (by decide +kernel) (by decide +kernel)

theorem simple [bindings : Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (machine : Hkdf.Proofs.Program.SupportedMachine bindings s)
    (loaded : ProgramLoaded s) (outside : ¬ InProgram boundary.rip)
    (rip : s.RIP = 0x105cec) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧
      Hkdf.Proofs.Program.SupportedMachine bindings t ∧ ProgramLoaded t ∧
      t.RIP = 0x105d00 ∧ t.regValue .rax = 3 ∧
      AgreesExcept [.reg 0, .rip] s t ∧ t.external = s.external := by
  have paddingStep : StepEffect (fun s ↦ s.RIP = 0x105cf1)
      (codeRange 0x105cf1
        [0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x2e, 0x0f, 0x1f, 0x84, 0, 0, 0, 0, 0])
      (fun _ ↦ nopEffect 0x105cf1 15) :=
    nop_m_effect_step _ [0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x2e]
      (by decide) (by decide) (.sib 0 (some 0) 0 (.d32 0))
      ⟨by decide, fun h ↦ by cases h⟩ rfl rfl
  exact mov_eax_three_nop (offset := 0x5cec) paddingStep ready machine loaded outside rip
    (by decide) (by decide +kernel) (by decide +kernel)

end Hkdf.Proofs.Common.ExtractCaller.PadEntry
