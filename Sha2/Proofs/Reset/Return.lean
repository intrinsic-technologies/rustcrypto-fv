import Sha2.Proofs.Reset.Prefix
import Sha2.Proofs.Common.Machine.Epilogue.ABI
import Sha2.Proofs.Common.Memory.ReadOutput

set_option autoImplicit false

namespace Sha2.Proofs.Reset

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

def resetReturnPC : Wrapper.Variant → BitVec 64
  | .sha224 => 0x1014b5
  | .sha256 => 0x103101

theorem reset_return_code (v : Wrapper.Variant) {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange (resetReturnPC v) (Epilogue.bytes .six200 ++ [0xc3])) s := by
  cases v with
  | sha224 =>
    exact programText_slice (programLoaded_codeIn loaded) 0x14b5 _
      (by decide +kernel) (by decide +kernel)
  | sha256 =>
    exact programText_slice (programLoaded_codeIn loaded) 0x3101 _
      (by decide +kernel) (by decide +kernel)

theorem reset_return_inside (v : Wrapper.Variant) :
    BlockInProgram (resetReturnPC v) Epilogue.Layout.six200.length := by
  cases v with
  | sha224 => exact blockInProgram_of_textOffset 0x14b5 _ (by decide +kernel)
  | sha256 => exact blockInProgram_of_textOffset 0x3101 _ (by decide +kernel)

theorem returned_at [bindings : Bindings] (routine : Routine)
    (layout : Epilogue.Layout) (pc : BitVec 64)
    (six : layout.six = true)
    (capacity : layout.allocation + 48 ≤ routine.minStackBytes)
    {initial s : RamState} {inputs : Array Input}
    (machine : SupportedMachine bindings initial)
    (call : TwoOutputs.ValidCall routine initial inputs)
    (state : ExecutionState initial s (regions routine initial))
    (rsp : rspOf s = stackPtr initial - BitVec.ofNat 64 (layout.allocation + 48))
    (rip : s.RIP = pc)
    (saved : ∀ (r : BitVec 5) (offset : Nat),
      (r, offset) ∈ [(3,0),(12,8),(13,16),(14,24),(15,32)] →
      memLoad s.external (rspOf s + BitVec.ofNat 64 (layout.allocation + offset)) 64 =
        (Operand.reg r : Operand 64).read initial)
    (savedRbp : memLoad s.external (rspOf s + BitVec.ofNat 64 (layout.allocation + 40)) 64 =
      (Operand.reg 5 : Operand 64).read initial)
    (inside : BlockInProgram pc layout.length)
    (code : CodeIn (codeRange pc (Epilogue.bytes layout ++ [0xc3])) s)
    (returnWord : memLoad s.external (stackPtr initial) 64 = (returnBoundary initial).rip) :
    ∃ fuel final, UniqueExecution initial fuel final ∧ SupportedMachine bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧ DirectionFlagUnset final ∧
      MemoryWriteFrame initial final (regions routine initial) ∧
      final.external = s.external := by
  have read (offset : Nat) (bound : offset + 8 ≤ layout.allocation + 48) :
      MemReadable s (rspOf s + BitVec.ofNat 64 offset) 8 := by
    rw [rsp]
    exact stack_frame_readable call.stack (frame := layout.allocation + 48) capacity state.allocated bound
  have pre : Epilogue.Pre pc layout s :=
    ⟨rip, read layout.allocation (by omega), read (layout.allocation + 8) (by omega),
      read (layout.allocation + 16) (by omega), read (layout.allocation + 24) (by omega),
      read (layout.allocation + 32) (by omega), by
        simpa only [six, ite_true] using read (layout.allocation + 40) (by omega)⟩
  have originalRSP : rspOf s + BitVec.ofNat 64 (layout.allocation + 48) = stackPtr initial := by
    rw [rsp]; exact BitVec.sub_add_cancel _ _
  have retRead : MemReadable s (rspOf s + BitVec.ofNat 64 (layout.allocation + 48)) 8 := by
    rw [originalRSP]
    have h := Common.Encoding.Serialize.readable_of_grow
      (stack_valid_sub_readable call.stack (offset := 0) (len := 8)
        (by omega) (by omega)) state.allocated
    simpa only [BitVec.sub_zero] using h
  obtain ⟨steps, final, restored, run, ready, restoreEffect, retEffect, memory⟩ :=
    Epilogue.finish pc layout (returnBoundary initial)
      (valid_return_boundary machine call.stack call.returnAddress).2.2
      inside s (supportedMachine_readyToStep state.machine)
      code pre (by simpa only [six, ite_true] using retRead)
      (by simp only [six, ite_true]
          change memLoad s.external (rspOf s + BitVec.ofNat 64 (layout.allocation + 48)) 64 = _
          rw [originalRSP]; exact returnWord)
      (by simp only [six, ite_true]
          change rspOf s + BitVec.ofNat 64 (layout.allocation + 48) + 8 = stackPtr initial + 8; rw [originalRSP])
      (valid_return_boundary machine call.stack call.returnAddress).2.1
  have abi := Epilogue.calleeSaved restoreEffect retEffect saved (by simpa only [six, ite_true] using savedRbp)
  have agrees := restoreEffect.agrees.trans retEffect.agrees
  have machineFinal := supportedMachine_of_ready_agrees state.machine ready agrees
  obtain ⟨prior, execution⟩ := state.execution
  obtain ⟨fuel, unique⟩ := (execution.returns run).unique_of_boundary
    (valid_return_boundary machine call.stack call.returnAddress).1
  refine ⟨fuel, final, unique, machineFinal, abi, ?_, ?_, memory⟩
  · exact agrees.directionFlagClear (by
      simp [Epilogue.effect, six, Effect.components, X86Proofs.retEffect])
      state.directionFlag
  · intro addr outside
    rw [memory]
    exact state.frame addr outside

theorem returned [bindings : Bindings] (v : Wrapper.Variant)
    {initial s : RamState} {inputs : Array Input}
    (machine : SupportedMachine bindings initial)
    (call : TwoOutputs.ValidCall (resetRoutine v) initial inputs)
    (state : ExecutionState initial s (regions (resetRoutine v) initial))
    (rsp : rspOf s = stackPtr initial - 248#64)
    (rip : s.RIP = resetReturnPC v)
    (saved : ∀ (r : BitVec 5) (offset : Nat),
      (r, offset) ∈ [(3,0),(12,8),(13,16),(14,24),(15,32)] →
      memLoad s.external (rspOf s + BitVec.ofNat 64 (200 + offset)) 64 =
        (Operand.reg r : Operand 64).read initial)
    (savedRbp : memLoad s.external (rspOf s + 240#64) 64 =
      (Operand.reg 5 : Operand 64).read initial)
    (returnWord : memLoad s.external (stackPtr initial) 64 = (returnBoundary initial).rip) :
    ∃ fuel final, UniqueExecution initial fuel final ∧ SupportedMachine bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧ DirectionFlagUnset final ∧
      MemoryWriteFrame initial final (regions (resetRoutine v) initial) ∧
      final.external = s.external := by
  exact returned_at (resetRoutine v) .six200 (resetReturnPC v) rfl
    (by rw [resetRoutine_stack]; decide) machine call state rsp rip saved savedRbp
    (reset_return_inside v) (reset_return_code v state.loaded) returnWord

theorem returned_outputs {routine : Routine} {initial s final : RamState}
    (first second : Vector UInt8 routine.outputBytes)
    (memory : final.external = s.external)
    (firstBytes : (TwoOutputs.outputRegion routine initial).HasBytes s.external ⟨first.toArray⟩)
    (secondBytes : (TwoOutputs.secondOutputRegion routine initial).HasBytes s.external
      ⟨second.toArray⟩) :
    TwoOutputs.readOutput routine initial final = .ok first ∧
      TwoOutputs.readSecondOutput routine initial final = .ok second := by
  constructor
  · apply Common.Memory.readBytes_of_hasBytes
    simpa only [memory] using firstBytes
  · apply Common.Memory.readBytes_of_hasBytes
    simpa only [memory] using secondBytes

end Sha2.Proofs.Reset
