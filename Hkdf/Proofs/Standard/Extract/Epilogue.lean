import Hkdf.Proofs.Common.Machine.Code
import Hkdf.Proofs.Common.Field.Operations.Run.Compose
import Hkdf.Proofs.Common.Encoding.Serialize.Tail.Epilogue
import X86Proofs.Instructions.Add.Generated.Imm32.Triple
import X86Proofs.Instructions.Call.Triple

set_option autoImplicit false

namespace Hkdf.Proofs.Standard.Extract.Epilogue

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Spec.Program Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.Field

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x101791
  readable : ∀ i : Nat, i < 6 → MemReadable s (rspOf s + BitVec.ofNat 64 (472 + 8 * i)) 8

def bytes : List UInt8 :=
  [0x48,0x81,0xc4,0xd8,0x1,0x0,0x0,0x5b,0x41,0x5c,0x41,0x5d,0x41,0x5e,0x41,0x5f,0x5d]

def effect (s : RamState) : Effect :=
  { rip := 0x1017a2
    writes := [
      ⟨(.reg 4 : Operand 64), rspOf s + 520⟩,
      ⟨(.reg 3 : Operand 64), memLoad s.external (rspOf s + 472) 64⟩,
      ⟨(.reg 12 : Operand 64), memLoad s.external (rspOf s + 480) 64⟩,
      ⟨(.reg 13 : Operand 64), memLoad s.external (rspOf s + 488) 64⟩,
      ⟨(.reg 14 : Operand 64), memLoad s.external (rspOf s + 496) 64⟩,
      ⟨(.reg 15 : Operand 64), memLoad s.external (rspOf s + 504) 64⟩,
      ⟨(.reg 5 : Operand 64), memLoad s.external (rspOf s + 512) 64⟩]
    flags := some (.ofStatusFlags (addSpec (rspOf s) (472 : BitVec 64)).2) }

theorem code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x101791 bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0x1791 bytes
    (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 1000000 in
theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x101791 bytes) (Effect.post effect) := by
  have add := add_r64_imm32_effect_step 0x101791 0x48 0xc4 472
    (by constructor <;> decide +kernel) (by decide +kernel) (by decide +kernel)
  change StepEffect _ _ (addR64Imm32Effect 0x101791 4 472) at add
  advance_begin add
  case next => intro s h; exact boundary_ne_program outside (inProgram_of_textOffset 0x1798 (by decide))
  advance_then (Hkdf.Proofs.Common.Encoding.Serialize.pop_register_effect_step 0x101798 3 (by decide +kernel))
  case sub => exact codeRange_slice_subset 0x101791 bytes 7 1
  case mid =>
    intro s t hP hH hO
    refine ⟨⟨hH.rip_of (by x86_norm), MemReadable.carry hH (hO true) (addr := rspOf) (by x86_addr_obs) ?_⟩, ?_, ?_⟩
    · x86_norm
      exact hP.readable 0 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1799 (by decide))
  advance_then (Hkdf.Proofs.Common.Encoding.Serialize.pop_register_effect_step 0x101799 12 (by decide +kernel))
  case sub => exact codeRange_slice_subset 0x101791 bytes 8 2
  case mid =>
    intro s t hP hH hO
    refine ⟨⟨hH.rip_of (by x86_norm), MemReadable.carry hH (hO true) (addr := rspOf) (by x86_addr_obs) ?_⟩, ?_, ?_⟩
    · x86_norm
      exact hP.readable 1 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x179b (by decide))
  advance_then (Hkdf.Proofs.Common.Encoding.Serialize.pop_register_effect_step 0x10179b 13 (by decide +kernel))
  case sub => exact codeRange_slice_subset 0x101791 bytes 10 2
  case mid =>
    intro s t hP hH hO
    refine ⟨⟨hH.rip_of (by x86_norm), MemReadable.carry hH (hO true) (addr := rspOf) (by x86_addr_obs) ?_⟩, ?_, ?_⟩
    · x86_norm
      exact hP.readable 2 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x179d (by decide))
  advance_then (Hkdf.Proofs.Common.Encoding.Serialize.pop_register_effect_step 0x10179d 14 (by decide +kernel))
  case sub => exact codeRange_slice_subset 0x101791 bytes 12 2
  case mid =>
    intro s t hP hH hO
    refine ⟨⟨hH.rip_of (by x86_norm), MemReadable.carry hH (hO true) (addr := rspOf) (by x86_addr_obs) ?_⟩, ?_, ?_⟩
    · x86_norm
      exact hP.readable 3 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x179f (by decide))
  advance_then (Hkdf.Proofs.Common.Encoding.Serialize.pop_register_effect_step 0x10179f 15 (by decide +kernel))
  case sub => exact codeRange_slice_subset 0x101791 bytes 14 2
  case mid =>
    intro s t hP hH hO
    refine ⟨⟨hH.rip_of (by x86_norm), MemReadable.carry hH (hO true) (addr := rspOf) (by x86_addr_obs) ?_⟩, ?_, ?_⟩
    · x86_norm
      exact hP.readable 4 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x17a1 (by decide))
  advance_then (Hkdf.Proofs.Common.Encoding.Serialize.pop_register_effect_step 0x1017a1 5 (by decide +kernel))
  case sub => exact codeRange_slice_subset 0x101791 bytes 16 1
  case mid =>
    intro s t hP hH hO
    refine ⟨⟨hH.rip_of (by x86_norm), MemReadable.carry hH (hO true)
      (addr := rspOf) (by x86_addr_obs) ?_⟩, ?_, ?_⟩
    · x86_norm
      exact hP.readable 5 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x17a2 (by decide))
  advance_finish [effect]

end Hkdf.Proofs.Standard.Extract.Epilogue
