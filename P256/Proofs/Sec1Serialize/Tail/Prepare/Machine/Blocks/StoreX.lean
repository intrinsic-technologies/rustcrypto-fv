import P256.Proofs.Sec1Serialize.Tail.Prepare.Machine.Frame
import P256.Proofs.Program.Code
import X86Proofs.Instructions.MovStore.Triple

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Sec1Serialize.Prepare

open P256.Spec.Program P256.Spec.Program.Routines X86 X86.Machine X86.UserProcess X86Proofs

def prepareStoreXBytes : List UInt8 :=
  [0x4c, 0x89, 0xac, 0x24, 0xc8, 0x0, 0x0, 0x0, 0x4c, 0x89, 0xa4, 0x24,
   0xd0, 0x0, 0x0, 0x0, 0x4c, 0x89, 0xbc, 0x24, 0xd8, 0x0, 0x0, 0x0,
   0x48, 0x89, 0x9c, 0x24, 0xe0, 0x0, 0x0, 0x0]

def prepareStoreXEffect (s : RamState) : Effect :=
  { rip := 0x111091
    writes := [
      ⟨(.mem (rspOf s + 200) : Operand 64), (Operand.reg 13 : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 208) : Operand 64), (Operand.reg 12 : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 216) : Operand 64), (Operand.reg 15 : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 224) : Operand 64), (Operand.reg 3 : Operand 64).read s⟩] }

set_option maxHeartbeats 1600000 in
theorem prepare_storex [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (EncodingPre 0x111071 32 0 264)
      (codeRange 0x111071 prepareStoreXBytes) (Effect.post prepareStoreXEffect) := by
  have next (i : Nat) (hi : i < 118431) :
      Extracted.textAddress + BitVec.ofNat 64 i ≠ boundary.rip :=
    boundary_ne_program hOutside (inProgram_of_textOffset i hi)
  have h0 := next 0x11079 (by decide)
  have h1 := next 0x11081 (by decide)
  have h2 := next 0x11089 (by decide)
  have h3 := next 0x11091 (by decide)
  unfold prepareStoreXBytes
  advance_begin mov_m64_r64_effect_step 0x111071 0x4c (by simp [RexWPrefix]) 5
    (.sib 4 none 0 (.d32 200)) (by simp [AddrMode.Valid]) rfl rfl
  advance_then mov_m64_r64_effect_step 0x111079 0x4c (by simp [RexWPrefix]) 4
    (.sib 4 none 0 (.d32 208)) (by simp [AddrMode.Valid]) rfl rfl
  advance_then mov_m64_r64_effect_step 0x111081 0x4c (by simp [RexWPrefix]) 7
    (.sib 4 none 0 (.d32 216)) (by simp [AddrMode.Valid]) rfl rfl
  advance_then mov_m64_r64_effect_step 0x111089 0x48 (by simp [RexWPrefix]) 3
    (.sib 4 none 0 (.d32 224)) (by simp [AddrMode.Valid]) rfl rfl
  apply AdvanceTriple.block_end
  intro s s' _ hH
  apply hH.weaken
  · x86_norm [prepareStoreXEffect]
  · x86_norm [prepareStoreXEffect]
    exact ⟨rfl, rfl, rfl, rfl⟩
  · intro i
    cases i <;> x86_norm [prepareStoreXEffect]
  · x86_norm [prepareStoreXEffect]
  all_goals try (first
    | exact codeRange_mem_of_drop (p := 0x111071) (all := prepareStoreXBytes) 8 (by decide +kernel)
    | exact codeRange_mem_of_drop (p := 0x111071) (all := prepareStoreXBytes) 16 (by decide +kernel)
    | exact codeRange_mem_of_drop (p := 0x111071) (all := prepareStoreXBytes) 24 (by decide +kernel))
  all_goals try (
    intro s hP
    refine StorePre.of_holds (Effect.start_holds s) (Effect.start_obs s) hP.rip (by x86_addr_obs) ?_ ?_
    · x86_norm; exact hP.writable _ (by decide +kernel)
    · x86_norm; exact hP.apart _ (by decide +kernel) 0 8 (by decide))
  all_goals try (
    intro s hP
    x86_avoid
    exact hP.apart _ (by decide +kernel) 0 32 (by decide))
  all_goals (
    intro s s' hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_
      · x86_norm
        exact hP.writable _ (by decide +kernel)
      · x86_norm
        first
        | exact hP.apart _ (by decide +kernel) 0 8 (by decide)
        | exact hP.apart _ (by decide +kernel) 8 8 (by decide)
        | exact hP.apart _ (by decide +kernel) 16 8 (by decide)
        | exact hP.apart _ (by decide +kernel) 24 8 (by decide)
    · x86_avoid
      exact hP.apart _ (by decide +kernel) 0 32 (by decide)
    · x86_norm
      assumption)

end P256.Proofs.Sec1Serialize.Prepare
