import Hkdf.Proofs.Common.Machine.Code
import Hkdf.Proofs.Common.Field.Operations.Run.Compose
import Hkdf.Proofs.Common.Encoding.Serialize.Tail.Epilogue
import X86Proofs.Instructions.Add.Generated.Imm32.Triple
import X86Proofs.Instructions.Call.Triple

set_option autoImplicit false

namespace Hkdf.Proofs.Key.Tail.Epilogue

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Spec.Program Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.Field

theorem stackTop_obs {s t : RamState} (h : Obs s t) : stackTop s = stackTop t := by
  change (Operand.mem (rspOf s) : Operand 64).read s =
    (Operand.mem (rspOf t) : Operand 64).read t
  have rsp : rspOf s = rspOf t := h.read_reg 4
  rw [rsp]
  exact h.read_mem _

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x116682
  readable : ∀ i : Nat, i < 6 → MemReadable s (rspOf s + BitVec.ofNat 64 (336 + 8 * i)) 8
  returnLow : (memLoad s.external (rspOf s + 376) 64).toNat < 2^32
  returnInProgram : InProgram (memLoad s.external (rspOf s + 376) 64)

def bytes : List UInt8 :=
  [0x48, 0x81, 0xc4, 0x50, 0x01, 0, 0, 0x5b, 0x41, 0x5c, 0x41, 0x5d,
    0x41, 0x5e, 0x41, 0x5f, 0xc3]

def effect (s : RamState) : Effect :=
  { rip := memLoad s.external (rspOf s + 376) 64
    writes := [
      ⟨(.reg 4 : Operand 64), rspOf s + 384⟩,
      ⟨(.reg 3 : Operand 64), memLoad s.external (rspOf s + 336) 64⟩,
      ⟨(.reg 12 : Operand 64), memLoad s.external (rspOf s + 344) 64⟩,
      ⟨(.reg 13 : Operand 64), memLoad s.external (rspOf s + 352) 64⟩,
      ⟨(.reg 14 : Operand 64), memLoad s.external (rspOf s + 360) 64⟩,
      ⟨(.reg 15 : Operand 64), memLoad s.external (rspOf s + 368) 64⟩]
    flags := some (.ofStatusFlags (addSpec (rspOf s) (336 : BitVec 64)).2) }

theorem code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x116682 bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0x16682 bytes
    (by decide +kernel) (by decide +kernel)

set_option maxHeartbeats 1000000 in
theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x116682 bytes) (Effect.post effect) := by
  have add := add_r64_imm32_effect_step 0x116682 0x48 0xc4 336
    (by constructor <;> decide +kernel) (by decide +kernel) (by decide +kernel)
  change StepEffect _ _ (addR64Imm32Effect 0x116682 4 336) at add
  advance_begin add
  case next => intro s h; exact boundary_ne_program outside (inProgram_of_textOffset 0x16689 (by decide))
  advance_then (Hkdf.Proofs.Common.Encoding.Serialize.pop_register_effect_step 0x116689 3 (by decide +kernel))
  case sub => exact codeRange_slice_subset 0x116682 bytes 7 1
  case mid =>
    intro s t hP hH hO
    refine ⟨⟨hH.rip_of (by x86_norm), MemReadable.carry hH (hO true) (addr := rspOf) (by x86_addr_obs) ?_⟩, ?_, ?_⟩
    · x86_norm
      exact hP.readable 0 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1668a (by decide))
  advance_then (Hkdf.Proofs.Common.Encoding.Serialize.pop_register_effect_step 0x11668a 12 (by decide +kernel))
  case sub => exact codeRange_slice_subset 0x116682 bytes 8 2
  case mid =>
    intro s t hP hH hO
    refine ⟨⟨hH.rip_of (by x86_norm), MemReadable.carry hH (hO true) (addr := rspOf) (by x86_addr_obs) ?_⟩, ?_, ?_⟩
    · x86_norm
      exact hP.readable 1 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1668c (by decide))
  advance_then (Hkdf.Proofs.Common.Encoding.Serialize.pop_register_effect_step 0x11668c 13 (by decide +kernel))
  case sub => exact codeRange_slice_subset 0x116682 bytes 10 2
  case mid =>
    intro s t hP hH hO
    refine ⟨⟨hH.rip_of (by x86_norm), MemReadable.carry hH (hO true) (addr := rspOf) (by x86_addr_obs) ?_⟩, ?_, ?_⟩
    · x86_norm
      exact hP.readable 2 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x1668e (by decide))
  advance_then (Hkdf.Proofs.Common.Encoding.Serialize.pop_register_effect_step 0x11668e 14 (by decide +kernel))
  case sub => exact codeRange_slice_subset 0x116682 bytes 12 2
  case mid =>
    intro s t hP hH hO
    refine ⟨⟨hH.rip_of (by x86_norm), MemReadable.carry hH (hO true) (addr := rspOf) (by x86_addr_obs) ?_⟩, ?_, ?_⟩
    · x86_norm
      exact hP.readable 3 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x16690 (by decide))
  advance_then (Hkdf.Proofs.Common.Encoding.Serialize.pop_register_effect_step 0x116690 15 (by decide +kernel))
  case sub => exact codeRange_slice_subset 0x116682 bytes 14 2
  case mid =>
    intro s t hP hH hO
    refine ⟨⟨hH.rip_of (by x86_norm), MemReadable.carry hH (hO true) (addr := rspOf) (by x86_addr_obs) ?_⟩, ?_, ?_⟩
    · x86_norm
      exact hP.readable 4 (by decide)
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · exact boundary_ne_program outside (inProgram_of_textOffset 0x16692 (by decide))
  advance_then (ret_effect_step 0x116692)
  case sub => exact codeRange_slice_subset 0x116682 bytes 16 1
  case mid =>
    intro s t hP hH hO
    refine ⟨⟨⟨hH.rip_of (by x86_norm), MemReadable.carry hH (hO true) (addr := rspOf) (by x86_addr_obs) ?_⟩, ?_⟩, ?_, ?_⟩
    · x86_norm
      exact hP.readable 5 (by decide)
    · rw [← stackTop_obs (hO true)]
      x86_norm
      exact hP.returnLow
    · apply Effect.Avoids.of_noMem
      simp [Component.Covers]
    · change stackTop t ≠ boundary.rip
      rw [← stackTop_obs (hO true)]
      x86_norm
      exact boundary_ne_program outside hP.returnInProgram
  advance_finish [effect]

end Hkdf.Proofs.Key.Tail.Epilogue
