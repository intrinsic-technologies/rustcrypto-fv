import P256.Proofs.Sec1Serialize.Tail.Prepare.Machine.Frame
import P256.Proofs.Program.Code
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.MovLoad.Triple

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.Program (boundary_ne_program inProgram_of_textOffset)

namespace P256.Proofs.Sec1Serialize.Prepare

open P256.Spec.Program P256.Spec.Program.Routines X86 X86.Machine X86.UserProcess X86Proofs

def prepareStoreYBytes : List UInt8 :=
  [0x48, 0x8b, 0x44, 0x24, 0x10, 0x48, 0x8b, 0x4c, 0x24, 0x18, 0x48, 0x89,
   0x84, 0x24, 0xe8, 0x0, 0x0, 0x0, 0x48, 0x89, 0x8c, 0x24, 0xf0, 0x0,
   0x0, 0x0, 0x48, 0x8b, 0x44, 0x24, 0x20, 0x48, 0x89, 0x84, 0x24, 0xf8,
   0x0, 0x0, 0x0, 0x48, 0x8b, 0x44, 0x24, 0x28, 0x48, 0x89, 0x84, 0x24,
   0x0, 0x1, 0x0, 0x0]

def prepareStoreYEffect (s : RamState) : Effect :=
  { rip := 0x1110cc
    writes := [
      ⟨(.reg 1 : Operand 64), (Operand.mem (rspOf s + 24) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 232) : Operand 64), (Operand.mem (rspOf s + 16) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 240) : Operand 64), (Operand.mem (rspOf s + 24) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 248) : Operand 64), (Operand.mem (rspOf s + 32) : Operand 64).read s⟩,
      ⟨(.reg 0 : Operand 64), (Operand.mem (rspOf s + 40) : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 256) : Operand 64), (Operand.mem (rspOf s + 40) : Operand 64).read s⟩] }

set_option maxHeartbeats 1600000 in
theorem prepare_storey [Bindings] (boundary : ReturnBoundary)
    (hOutside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary (EncodingPre 0x111098 52 0 264)
      (codeRange 0x111098 prepareStoreYBytes) (Effect.post prepareStoreYEffect) := by
  have next (i : Nat) (hi : i < 118431) :
      Extracted.textAddress + BitVec.ofNat 64 i ≠ boundary.rip :=
    boundary_ne_program hOutside (inProgram_of_textOffset i hi)
  have h0 := next 0x1109d (by decide)
  have h1 := next 0x110a2 (by decide)
  have h2 := next 0x110aa (by decide)
  have h3 := next 0x110b2 (by decide)
  have h4 := next 0x110b7 (by decide)
  have h5 := next 0x110bf (by decide)
  have h6 := next 0x110c4 (by decide)
  have h7 := next 0x110cc (by decide)
  unfold prepareStoreYBytes
  advance_begin mov_r64_m64_effect_step 0x111098 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 16)) (by simp [AddrMode.Valid]) rfl rfl
  advance_then mov_r64_m64_effect_step 0x11109d 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d8 24)) (by simp [AddrMode.Valid]) rfl rfl
  advance_then mov_m64_r64_effect_step 0x1110a2 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 232)) (by simp [AddrMode.Valid]) rfl rfl
  advance_then mov_m64_r64_effect_step 0x1110aa 0x48 (by simp [RexWPrefix]) 1
    (.sib 4 none 0 (.d32 240)) (by simp [AddrMode.Valid]) rfl rfl
  advance_then mov_r64_m64_effect_step 0x1110b2 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 32)) (by simp [AddrMode.Valid]) rfl rfl
  advance_then mov_m64_r64_effect_step 0x1110b7 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 248)) (by simp [AddrMode.Valid]) rfl rfl
  advance_then mov_r64_m64_effect_step 0x1110bf 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d8 40)) (by simp [AddrMode.Valid]) rfl rfl
  advance_then mov_m64_r64_effect_step 0x1110c4 0x48 (by simp [RexWPrefix]) 0
    (.sib 4 none 0 (.d32 256)) (by simp [AddrMode.Valid]) rfl rfl
  advance_finish [prepareStoreYEffect]
  all_goals try (first
    | exact codeRange_mem_of_drop (p := 0x111098) (all := prepareStoreYBytes) 5 (by decide +kernel)
    | exact codeRange_mem_of_drop (p := 0x111098) (all := prepareStoreYBytes) 10 (by decide +kernel)
    | exact codeRange_mem_of_drop (p := 0x111098) (all := prepareStoreYBytes) 18 (by decide +kernel)
    | exact codeRange_mem_of_drop (p := 0x111098) (all := prepareStoreYBytes) 26 (by decide +kernel)
    | exact codeRange_mem_of_drop (p := 0x111098) (all := prepareStoreYBytes) 31 (by decide +kernel)
    | exact codeRange_mem_of_drop (p := 0x111098) (all := prepareStoreYBytes) 39 (by decide +kernel)
    | exact codeRange_mem_of_drop (p := 0x111098) (all := prepareStoreYBytes) 44 (by decide +kernel))
  all_goals (
    intro s s' hP hH hO
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_, ?_⟩
    · refine StorePre.of_holds hH (hO true) (by x86_norm) (by x86_addr_obs) ?_ ?_
      · x86_norm
        exact hP.writable _ (by decide +kernel)
      · x86_norm
        first
        | exact hP.apart _ (by decide +kernel) 10 8 (by decide)
        | exact hP.apart _ (by decide +kernel) 18 8 (by decide)
        | exact hP.apart _ (by decide +kernel) 31 8 (by decide)
        | exact hP.apart _ (by decide +kernel) 44 8 (by decide)
    · x86_avoid
      exact hP.apart _ (by decide +kernel) 0 52 (by decide)
    · x86_norm
      assumption)

end P256.Proofs.Sec1Serialize.Prepare
