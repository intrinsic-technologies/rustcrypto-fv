import P256.Proofs.Verifying.Combination.Naf.Iterator.Advance.Steps

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Iterator.Advance

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Proofs.Common.Instructions.CrossPageStore

def emptyEffect (s : RamState) : Effect :=
  { rip := 0x118246
    writes := [⟨(Operand.mem (s.regValue .rdi + 32) : Operand 64), 0⟩,
      ⟨(Operand.reg 2 : Operand 64), 0⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

theorem empty [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (rip : s.RIP = 0x11823c)
    (write : Writable s (s.regValue .rdi + 32) 8)
    (avoid : ∀ i < 8, ¬ InProgram (s.regValue .rdi + 32 + BitVec.ofNat 64 i))
    (outer : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 2 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧ (emptyEffect s).Holds s t := by
  have apart : RangeApart (s.regValue .rdi + 32) 8 0x11823c 8 := by
    intro i hi j hj he
    apply avoid i hi
    rw [he]
    have h := inProgram_of_textOffset (0x1823c+j) (by omega)
    simpa [BitVec.ofNat_add, ← BitVec.add_assoc, Extracted.textAddress] using h
  obtain ⟨a, runA, readyA, effectA⟩ :=
    (mov_m64_imm32_effect_step_any 0x11823c 0x48 (by simp [RexWPrefix])
      (.base 7 (.d8 32)) (by decide +kernel) rfl rfl 0).advances ready
      (programText_slice (programLoaded_codeIn loaded) 0x1823c _ (by decide) (by decide +kernel))
      ⟨rip, write, apart⟩
      (boundary_ne_program outer (inProgram_of_textOffset 0x18244 (by decide)))
  change (movM64Imm32Effect 0x11823c (.base 7 (.d8 32)) 0 s).Holds s a at effectA
  have eq : (movM64Imm32Effect 0x11823c (.base 7 (.d8 32)) 0 s).components =
      [.mem (s.regValue .rdi + 32) 8, .rip] := by
    simp only [movM64Imm32Effect_components]; congr 2
  have agA : AgreesExcept [.mem (s.regValue .rdi + 32) 8, .rip] s a := by rw [← eq]; exact effectA.agrees
  have loadedA := store_loaded loaded effectA eq avoid
  obtain ⟨t, runT, readyT, loadedT, effectT⟩ := step_nomem (offset := 0x18244)
    (xor_r32_r32_effect_step 0x118244 0xd2 rfl) readyA loadedA effectA.rip
    (by decide) (by decide +kernel)
    (boundary_ne_program outer (inProgram_of_textOffset 0x18246 (by decide)))
    (by simp [Component.Covers])
  change (xorR32R32Effect 0x118244 2 2 2 a).Holds a t at effectT
  have frameT : AgreesExcept [.reg 2, .flags, .rip] a t := effectT.agrees
  refine ⟨t, runA.trans runT, readyT, loadedT, effectT.rip, ?_, by repeat constructor, ?_⟩
  · change memLoad t.external (s.regValue .rdi + 32) 64 = 0 ∧ t.regValue .rdx = 0
    constructor
    · rw [frameT.external (by simp [Component.Covers])]
      exact effectA.writes
    · have h : t.regValue .rdx =
          (((Operand.reg 2 : Operand 32).read a) ^^^ ((Operand.reg 2 : Operand 32).read a)).setWidth 64 := effectT.writes
      simpa only [BitVec.xor_self, BitVec.setWidth_zero, BitVec.ofNat_eq_ofNat] using h
  · apply (agA.trans frameT).mono
    simp [emptyEffect, Effect.components]

end P256.Proofs.Verifying.Combination.Naf.Iterator.Advance
