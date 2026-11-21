import P256.Proofs.Program.Code
import P256.Proofs.Common.Instructions.CrossPageStore
import X86Proofs.Instructions.Mov.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decode

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions.CrossPageStore

theorem reject_tag [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (outside : ¬ InProgram boundary.rip) (rip : s.RIP = 0x10e68e)
    (writable : Writable s (s.regValue .rdi) 8)
    (apart : RangeApart (s.regValue .rdi) 8 0x10e693 3) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ t.RIP = 0x10e696 ∧
      memLoad t.external (s.regValue .rdi) 64 = 1 ∧
      AgreesExcept [.reg 0, .mem (s.regValue .rdi) 8, .rip] s t := by
  obtain ⟨u, hu, ru, eu⟩ :=
    (mov_r32_imm32_effect_step 0x10e68e 0xb8 (by decide) 1).advances ready
      (programText_slice (programLoaded_codeIn loaded) 0xe68e _
        (by decide) (by decide +kernel)) rip
      (boundary_ne_program outside (inProgram_of_textOffset 0xe693 (by decide)))
  have gu : AgreesExcept [.reg 0, .rip] s u := eu.agrees
  have mu : u.external = s.external := gu.external (by simp [Component.Covers])
  have di : u.regValue .rdi = s.regValue .rdi := gu.read (n := 64) (r := 7) (by simp)
  have ax : u.regValue .rax = 1 := eu.writes
  have address (v : RamState) : storeAddrAt 0x10e693 (.base 7 .none) 3 v = v.regValue .rdi := by
    change v.regValue .rdi + 0#64 = v.regValue .rdi
    exact BitVec.add_zero _
  obtain ⟨t, ht, rt, et⟩ :=
    (mov_m64_r64_effect_step_any 0x10e693 0x48 (by simp [RexWPrefix]) 0
      (.base 7 .none) (by decide) rfl rfl).advances ru
      (programText_slice ((programLoaded_codeIn loaded).of_external_eq mu) 0xe693 _
        (by decide) (by decide +kernel))
      ⟨eu.rip, by
        change Writable u (storeAddrAt 0x10e693 (.base 7 .none) 3 u) 8
        rw [address, di]
        exact writable.of_external_eq mu,
       by
        change RangeApart (storeAddrAt 0x10e693 (.base 7 .none) 3 u) 8 0x10e693 3
        rw [address, di]
        exact apart⟩
      (boundary_ne_program outside (inProgram_of_textOffset 0xe696 (by decide)))
  change (storeEffect (n := 64) 0x10e693 3 (storeAddrAt 0x10e693 (.base 7 .none) 3)
    (fun v ↦ (Operand.reg 0 : Operand 64).read v) u).Holds u t at et
  have gt : AgreesExcept [.mem (s.regValue .rdi) 8, .rip] u t := by
    simpa only [storeEffect_components, Nat.reduceDiv, address, di] using et.agrees
  refine ⟨t, hu.trans ht, rt, et.rip, ?_, (gu.trans gt).mono (by simp)⟩
  have hw : memLoad t.external (storeAddrAt 0x10e693 (.base 7 .none) 3 u) 64 = u.regValue .rax := et.writes
  simpa only [address, di, ax] using hw

end P256.Proofs.Sec1.Decode
