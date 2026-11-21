import Hkdf.Proofs.Common.Machine.Code
import Hkdf.Proofs.Common.EffectCompose.Memory
import Hkdf.Proofs.Common.Field.Operations.Run.Compose
import Hkdf.Proofs.Common.Instructions.CrossPageStore.Compose
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.Mov.Triple

set_option autoImplicit false

namespace Hkdf.Proofs.Key.Tail.Copy

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Spec.Program Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.Field

theorem external_write_reg (s : RamState) (r : BitVec 5) (v : BitVec 64) :
    ((Operand.reg r : Operand 64).write s v).external = s.external := rfl

theorem external_write_mem (s : RamState) (a : BitVec 64) (v : BitVec 64) :
    ((Operand.mem a : Operand 64).write s v).external = memStore s.external a v := rfl

abbrev Writable := Hkdf.Proofs.Common.Instructions.CrossPageStore.Writable

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x116639
  readable : ∀ i : Nat, i < 8 → MemReadable s (rspOf s + BitVec.ofNat 64 (8 * i)) 8
  writable : ∀ i : Nat, i < 8 → Writable s (rbx.read s + BitVec.ofNat 64 (8 * i)) 8
  codeApart : ∀ i : Nat, i < 8 → ∀ offset len : Nat, offset + len ≤ 115149 →
    RangeApart (rbx.read s + BitVec.ofNat 64 (8 * i)) 8
      (Extracted.textAddress + BitVec.ofNat 64 offset) len
  stackApart : ∀ i ∈ ([0, 8, 16, 24, 32, 40, 48, 56] : List (BitVec 64)),
    ∀ j ∈ ([0, 8, 16, 24, 32, 40, 48, 56] : List (BitVec 64)),
      RangeApart (rbx.read s + i) 8 (rspOf s + j) 8

def bytes : List UInt8 :=
  [0x48, 0x8b, 0x44, 0x24, 0x38, 0x48, 0x89, 0x43, 0x38, 0x48, 0x8b, 0x44, 0x24, 0x30, 0x48, 0x89, 0x43, 0x30, 0x48, 0x8b, 0x44, 0x24, 0x28, 0x48, 0x89, 0x43, 0x28, 0x48, 0x8b, 0x44, 0x24, 0x20, 0x48, 0x89, 0x43, 0x20, 0x48, 0x8b, 0x44, 0x24, 0x18, 0x48, 0x89, 0x43, 0x18, 0x48, 0x8b, 0x44, 0x24, 0x10, 0x48, 0x89, 0x43, 0x10, 0x48, 0x8b, 0x4, 0x24, 0x48, 0x8b, 0x4c, 0x24, 0x8, 0x48, 0x89, 0x4b, 0x8, 0x48, 0x89, 0x3, 0x48, 0x89, 0xd8]

def effect (s : RamState) : Effect :=
  { rip := 0x116682
    writes := [
      ⟨(.reg 0 : Operand 64), rbx.read s⟩,
      ⟨(.reg 1 : Operand 64), memLoad s.external (rspOf s + 8) 64⟩,
      ⟨(.mem (rbx.read s + 0) : Operand 64), memLoad s.external (rspOf s + 0) 64⟩,
      ⟨(.mem (rbx.read s + 8) : Operand 64), memLoad s.external (rspOf s + 8) 64⟩,
      ⟨(.mem (rbx.read s + 16) : Operand 64), memLoad s.external (rspOf s + 16) 64⟩,
      ⟨(.mem (rbx.read s + 24) : Operand 64), memLoad s.external (rspOf s + 24) 64⟩,
      ⟨(.mem (rbx.read s + 32) : Operand 64), memLoad s.external (rspOf s + 32) 64⟩,
      ⟨(.mem (rbx.read s + 40) : Operand 64), memLoad s.external (rspOf s + 40) 64⟩,
      ⟨(.mem (rbx.read s + 48) : Operand 64), memLoad s.external (rspOf s + 48) 64⟩,
      ⟨(.mem (rbx.read s + 56) : Operand 64), memLoad s.external (rspOf s + 56) 64⟩] }

theorem code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x116639 bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0x16639 bytes
    (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 4000000 in
theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x116639 bytes) (Effect.post effect) := by
  have step1 := mov_r64_m64_effect_step 0x116639 0x48 (by constructor <;> decide +kernel) 0 (.sib 4 none 0 (.d8 56)) (by decide +kernel) rfl rfl
  change StepEffect _ _ (movR64M64Effect 0x116639 0 (.sib 4 none 0 (.d8 56))) at step1
  have step2 := Hkdf.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x11663e 0x48 (by constructor <;> decide +kernel) 0 (.base 3 (.d8 56)) (by decide +kernel) rfl rfl
  change StepEffect _ _ (movM64R64Effect 0x11663e 0 (.base 3 (.d8 56))) at step2
  have step3 := mov_r64_m64_effect_step 0x116642 0x48 (by constructor <;> decide +kernel) 0 (.sib 4 none 0 (.d8 48)) (by decide +kernel) rfl rfl
  change StepEffect _ _ (movR64M64Effect 0x116642 0 (.sib 4 none 0 (.d8 48))) at step3
  have step4 := Hkdf.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x116647 0x48 (by constructor <;> decide +kernel) 0 (.base 3 (.d8 48)) (by decide +kernel) rfl rfl
  change StepEffect _ _ (movM64R64Effect 0x116647 0 (.base 3 (.d8 48))) at step4
  have step5 := mov_r64_m64_effect_step 0x11664b 0x48 (by constructor <;> decide +kernel) 0 (.sib 4 none 0 (.d8 40)) (by decide +kernel) rfl rfl
  change StepEffect _ _ (movR64M64Effect 0x11664b 0 (.sib 4 none 0 (.d8 40))) at step5
  have step6 := Hkdf.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x116650 0x48 (by constructor <;> decide +kernel) 0 (.base 3 (.d8 40)) (by decide +kernel) rfl rfl
  change StepEffect _ _ (movM64R64Effect 0x116650 0 (.base 3 (.d8 40))) at step6
  have step7 := mov_r64_m64_effect_step 0x116654 0x48 (by constructor <;> decide +kernel) 0 (.sib 4 none 0 (.d8 32)) (by decide +kernel) rfl rfl
  change StepEffect _ _ (movR64M64Effect 0x116654 0 (.sib 4 none 0 (.d8 32))) at step7
  have step8 := Hkdf.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x116659 0x48 (by constructor <;> decide +kernel) 0 (.base 3 (.d8 32)) (by decide +kernel) rfl rfl
  change StepEffect _ _ (movM64R64Effect 0x116659 0 (.base 3 (.d8 32))) at step8
  have step9 := mov_r64_m64_effect_step 0x11665d 0x48 (by constructor <;> decide +kernel) 0 (.sib 4 none 0 (.d8 24)) (by decide +kernel) rfl rfl
  change StepEffect _ _ (movR64M64Effect 0x11665d 0 (.sib 4 none 0 (.d8 24))) at step9
  have step10 := Hkdf.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x116662 0x48 (by constructor <;> decide +kernel) 0 (.base 3 (.d8 24)) (by decide +kernel) rfl rfl
  change StepEffect _ _ (movM64R64Effect 0x116662 0 (.base 3 (.d8 24))) at step10
  have step11 := mov_r64_m64_effect_step 0x116666 0x48 (by constructor <;> decide +kernel) 0 (.sib 4 none 0 (.d8 16)) (by decide +kernel) rfl rfl
  change StepEffect _ _ (movR64M64Effect 0x116666 0 (.sib 4 none 0 (.d8 16))) at step11
  have step12 := Hkdf.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x11666b 0x48 (by constructor <;> decide +kernel) 0 (.base 3 (.d8 16)) (by decide +kernel) rfl rfl
  change StepEffect _ _ (movM64R64Effect 0x11666b 0 (.base 3 (.d8 16))) at step12
  have step13 := mov_r64_m64_effect_step 0x11666f 0x48 (by constructor <;> decide +kernel) 0 (.sib 4 none 0 .none) (by decide +kernel) rfl rfl
  change StepEffect _ _ (movR64M64Effect 0x11666f 0 (.sib 4 none 0 .none)) at step13
  have step14 := mov_r64_m64_effect_step 0x116673 0x48 (by constructor <;> decide +kernel) 1 (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl
  change StepEffect _ _ (movR64M64Effect 0x116673 1 (.sib 4 none 0 (.d8 8))) at step14
  have step15 := Hkdf.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x116678 0x48 (by constructor <;> decide +kernel) 1 (.base 3 (.d8 8)) (by decide +kernel) rfl rfl
  change StepEffect _ _ (movM64R64Effect 0x116678 1 (.base 3 (.d8 8))) at step15
  have step16 := Hkdf.Proofs.Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x11667c 0x48 (by constructor <;> decide +kernel) 0 (.base 3 .none) (by decide +kernel) rfl rfl
  change StepEffect _ _ (movM64R64Effect 0x11667c 0 (.base 3 .none)) at step16
  have step17 := mov_r64_r64_effect_step 0x11667f 0x48 0xd8 (by constructor <;> decide +kernel) (by decide +kernel)
  change StepEffect _ _ (movR64R64Effect 0x11667f 0 3) at step17
  advance_begin step1
  case pre =>
    intro s h
    refine ⟨h.rip, ?_⟩
    x86_norm
    exact h.readable 7 (by decide)
  case next => intro s h; exact boundary_ne_program outside (inProgram_of_textOffset 0x1663e (by decide))
  advance_then step2
  case sub => exact codeRange_slice_subset 0x116639 bytes 5 4
  case mid =>
    intro s t hP hH hO
    refine ⟨Hkdf.Proofs.Common.Instructions.CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 7 (by decide)
    · x86_norm
      exact hP.codeApart 7 (by decide) 0x1663e 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 7 (by decide) 0x16639 73 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x16642 (by decide))
  advance_then step3
  case sub => exact codeRange_slice_subset 0x116639 bytes 9 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 6 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x16647 (by decide))
  advance_then step4
  case sub => exact codeRange_slice_subset 0x116639 bytes 14 4
  case mid =>
    intro s t hP hH hO
    refine ⟨Hkdf.Proofs.Common.Instructions.CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 6 (by decide)
    · x86_norm
      exact hP.codeApart 6 (by decide) 0x16647 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 6 (by decide) 0x16639 73 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1664b (by decide))
  advance_then step5
  case sub => exact codeRange_slice_subset 0x116639 bytes 18 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 5 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x16650 (by decide))
  advance_then step6
  case sub => exact codeRange_slice_subset 0x116639 bytes 23 4
  case mid =>
    intro s t hP hH hO
    refine ⟨Hkdf.Proofs.Common.Instructions.CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 5 (by decide)
    · x86_norm
      exact hP.codeApart 5 (by decide) 0x16650 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 5 (by decide) 0x16639 73 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x16654 (by decide))
  advance_then step7
  case sub => exact codeRange_slice_subset 0x116639 bytes 27 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 4 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x16659 (by decide))
  advance_then step8
  case sub => exact codeRange_slice_subset 0x116639 bytes 32 4
  case mid =>
    intro s t hP hH hO
    refine ⟨Hkdf.Proofs.Common.Instructions.CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 4 (by decide)
    · x86_norm
      exact hP.codeApart 4 (by decide) 0x16659 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 4 (by decide) 0x16639 73 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1665d (by decide))
  advance_then step9
  case sub => exact codeRange_slice_subset 0x116639 bytes 36 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 3 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x16662 (by decide))
  advance_then step10
  case sub => exact codeRange_slice_subset 0x116639 bytes 41 4
  case mid =>
    intro s t hP hH hO
    refine ⟨Hkdf.Proofs.Common.Instructions.CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 3 (by decide)
    · x86_norm
      exact hP.codeApart 3 (by decide) 0x16662 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 3 (by decide) 0x16639 73 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x16666 (by decide))
  advance_then step11
  case sub => exact codeRange_slice_subset 0x116639 bytes 45 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 2 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1666b (by decide))
  advance_then step12
  case sub => exact codeRange_slice_subset 0x116639 bytes 50 4
  case mid =>
    intro s t hP hH hO
    refine ⟨Hkdf.Proofs.Common.Instructions.CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 2 (by decide)
    · x86_norm
      exact hP.codeApart 2 (by decide) 0x1666b 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 2 (by decide) 0x16639 73 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1666f (by decide))
  advance_then step13
  case sub => exact codeRange_slice_subset 0x116639 bytes 54 4
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 0 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x16673 (by decide))
  advance_then step14
  case sub => exact codeRange_slice_subset 0x116639 bytes 58 5
  case mid =>
    intro s t hP hH hO
    refine ⟨LoadPre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_, ?_, ?_⟩
    · x86_norm
      exact hP.readable 1 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x16678 (by decide))
  advance_then step15
  case sub => exact codeRange_slice_subset 0x116639 bytes 63 4
  case mid =>
    intro s t hP hH hO
    refine ⟨Hkdf.Proofs.Common.Instructions.CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 1 (by decide)
    · x86_norm
      exact hP.codeApart 1 (by decide) 0x16678 4 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 1 (by decide) 0x16639 73 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1667c (by decide))
  advance_then step16
  case sub => exact codeRange_slice_subset 0x116639 bytes 67 3
  case mid =>
    intro s t hP hH hO
    refine ⟨Hkdf.Proofs.Common.Instructions.CrossPageStore.storePre_of_holds hH (hO true) (by x86_norm) ?_ ?_, ?_, ?_⟩
    · x86_norm
      exact hP.writable 0 (by decide)
    · x86_norm
      exact hP.codeApart 0 (by decide) 0x1667c 3 (by decide)
    · apply Effect.Local.avoids (by x86_local) (hO true)
      apply Effect.avoids_codeRange
      x86_norm
      exact hP.codeApart 0 (by decide) 0x16639 73 (by decide)
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1667f (by decide))
  advance_then step17
  case sub => exact codeRange_slice_subset 0x116639 bytes 70 3
  case mid =>
    intro s t hP hH hO
    refine ⟨hH.rip_of (by x86_norm), ?_, ?_⟩
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x16682 (by decide))
  apply AdvanceTriple.block_end
  intro s t hp hh
  have apart := hp.stackApart
  x86_norm at apart
  apply hh.weaken
  · x86_norm [effect, external_write_reg, external_write_mem, memLoad_memStore_of_rangeApart, apart, BitVec.ofNat_eq_ofNat]
  · x86_norm [effect, external_write_reg, external_write_mem, memLoad_memStore_of_rangeApart, apart, BitVec.ofNat_eq_ofNat]
  · intro i; cases i <;> x86_norm [effect, external_write_reg, external_write_mem, memLoad_memStore_of_rangeApart, apart, BitVec.ofNat_eq_ofNat]
  · x86_norm [effect, external_write_reg, external_write_mem, memLoad_memStore_of_rangeApart, apart, BitVec.ofNat_eq_ofNat]

end Hkdf.Proofs.Key.Tail.Copy
