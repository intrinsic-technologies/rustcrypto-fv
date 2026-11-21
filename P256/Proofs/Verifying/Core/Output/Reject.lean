import P256.Proofs.Verifying.Core.Output.Branch
import P256.Proofs.Common.Instructions.CrossPageStore.Immediate
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovLoad.Triple

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Output

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions.CrossPageStore

theorem reject_loaded [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (outside : ¬ InProgram boundary.rip) (rip : s.RIP = 0x10e184)
    (writable : Writable s (s.regValue .rax + 8) 8)
    (apart : ∀ off len : Nat, off + len ≤ 118431 →
      RangeApart (s.regValue .rax + 8) 8 (Extracted.textAddress + BitVec.ofNat 64 off) len) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ t.RIP = 0x10e191 ∧
      t.regValue .rcx = 1 ∧ memLoad t.external (s.regValue .rax + 8) 64 = 0 ∧
      AgreesExcept [.mem (s.regValue .rax + 8) 8, .reg 1, .rip] s t := by
  obtain ⟨a, ha, ra, ea⟩ :=
    (mov_m64_imm32_effect_step_any 0x10e184 0x48 (by simp [RexWPrefix])
      (.base 0 (.d8 8)) (by decide) rfl rfl 0).advances ready
      (programText_slice (programLoaded_codeIn loaded) 0xe184 _
        (by decide) (by decide +kernel))
      ⟨rip, writable, apart 0xe184 8 (by decide)⟩
      (boundary_ne_program outside (inProgram_of_textOffset 0xe18c (by decide)))
  have fa : AgreesExcept [.mem (s.regValue .rax + 8) 8, .rip] s a := by
    have addr (q : RamState) : storeAddrAt 0x10e184 (.base 0 (.d8 8)) 8 q =
        q.regValue .rax + 8 := rfl
    simpa only [movM64Imm32Effect, storeEffect_components, Nat.reduceDiv,
      AddrMode.tail, Disp.bytes, immBytes_length, List.length_cons, List.length_nil,
      Nat.reduceAdd, addr] using ea.agrees
  have zero : memLoad a.external (s.regValue .rax + 8) 64 = 0 := ea.writes
  have code : CodeIn (codeRange 0x10e18c (0xb9 :: immBytes 32 1)) a := by
    apply ea.codeIn
    · exact Effect.avoids_of_components_mem_rip
        (by simp only [movM64Imm32Effect_components]; rfl) (apart 0xe18c 5 (by decide))
    · exact programText_slice (programLoaded_codeIn loaded) 0xe18c _
        (by decide) (by decide +kernel)
  obtain ⟨t, ht, rt, et⟩ := (mov_r32_imm32_effect_step 0x10e18c 0xb9 (by decide) 1).advances
    ra code ea.rip (boundary_ne_program outside (inProgram_of_textOffset 0xe191 (by decide)))
  have ft : AgreesExcept [.reg 1, .rip] a t := et.agrees
  refine ⟨t, ha.trans ht, rt, et.rip, et.writes, ?_, (fa.trans ft).mono (by simp)⟩
  rw [ft.external (by simp [Component.Covers])]
  exact zero

end P256.Proofs.Verifying.Core.Output
