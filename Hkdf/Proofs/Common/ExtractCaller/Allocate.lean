import Hkdf.Proofs.Common.Encoding.Serialize.Prologue
import Hkdf.Proofs.Common.CallFrame

set_option autoImplicit false

namespace Hkdf.Proofs.Common.ExtractCaller.Allocate

open Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Machine

theorem sub_rsp [bindings : Bindings] {s : RamState} {boundary : ReturnBoundary}
    {offset : Nat} {amount : BitVec 32}
    (ready : ReadyToStep s) (machine : Hkdf.Proofs.Program.SupportedMachine bindings s)
    (loaded : ProgramLoaded s) (outside : ¬ InProgram boundary.rip)
    (rip : s.RIP = Extracted.textAddress + BitVec.ofNat 64 offset)
    (bounded : offset + 7 < 115149)
    (bytes : Extracted.textBytes.toListFrom offset 7 =
      0x48 :: 0x81 :: 0xec :: immBytes 32 amount) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧
      Hkdf.Proofs.Program.SupportedMachine bindings t ∧ ProgramLoaded t ∧
      t.RIP = Extracted.textAddress + BitVec.ofNat 64 (offset + 7) ∧
      stackPtr t = stackPtr s - amount.signExtend 64 ∧
      AgreesExcept [.reg 4, .flags, .rip] s t ∧ t.external = s.external := by
  have code := programText_slice (programLoaded_codeIn loaded) offset
    (0x48 :: 0x81 :: 0xec :: immBytes 32 amount) (by
      change offset + 7 ≤ 115149
      omega) (by change Extracted.textBytes.toListFrom offset 7 = _; exact bytes)
  have next : Extracted.textAddress + BitVec.ofNat 64 offset + 7 =
      Extracted.textAddress + BitVec.ofNat 64 (offset + 7) := by
    rw [BitVec.ofNat_add, ← BitVec.add_assoc]
    rfl
  obtain ⟨t, run, readyT, effect⟩ :=
    (sub_r64_imm32_effect_step (Extracted.textAddress + BitVec.ofNat 64 offset)
      0x48 0xec amount (by constructor <;> decide) (by decide) (by decide)).advances
      ready code rip (by
        change Extracted.textAddress + BitVec.ofNat 64 offset + 7 ≠ boundary.rip
        rw [next]
        exact boundary_ne_program outside (inProgram_of_textOffset _ bounded))
  have frame : AgreesExcept [.reg 4, .flags, .rip] s t := effect.agrees
  have memory : t.external = s.external := frame.external (by simp [Component.Covers])
  refine ⟨t, run, readyT,
    Hkdf.Proofs.Common.Machine.supportedMachine_of_ready_agrees machine readyT frame,
    ?_, effect.rip.trans next, effect.writes, frame, memory⟩
  intro a b hb
  rw [memory]
  exact loaded a b hb

theorem standard [bindings : Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (machine : Hkdf.Proofs.Program.SupportedMachine bindings s)
    (loaded : ProgramLoaded s) (outside : ¬ InProgram boundary.rip)
    (rip : s.RIP = 0x10142a) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧
      Hkdf.Proofs.Program.SupportedMachine bindings t ∧ ProgramLoaded t ∧
      t.RIP = 0x101431 ∧ stackPtr t = stackPtr s - 472 ∧
      AgreesExcept [.reg 4, .flags, .rip] s t ∧ t.external = s.external := by
  exact sub_rsp (offset := 0x142a) (amount := 472) ready machine loaded outside rip
    (by decide) (by decide +kernel)

theorem simple [bindings : Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (machine : Hkdf.Proofs.Program.SupportedMachine bindings s)
    (loaded : ProgramLoaded s) (outside : ¬ InProgram boundary.rip)
    (rip : s.RIP = 0x105c7a) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧
      Hkdf.Proofs.Program.SupportedMachine bindings t ∧ ProgramLoaded t ∧
      t.RIP = 0x105c81 ∧ stackPtr t = stackPtr s - 488 ∧
      AgreesExcept [.reg 4, .flags, .rip] s t ∧ t.external = s.external := by
  exact sub_rsp (offset := 0x5c7a) (amount := 488) ready machine loaded outside rip
    (by decide) (by decide +kernel)

end Hkdf.Proofs.Common.ExtractCaller.Allocate
