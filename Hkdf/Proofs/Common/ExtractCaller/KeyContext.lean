import Hkdf.Proofs.Common.Machine.Boundary
import Hkdf.Proofs.Common.CallFrame.Stack
import Hkdf.Proofs.Common.CallFrame.Stack
import Hkdf.Proofs.Key.State
import Hkdf.Proofs.Standard.State

set_option autoImplicit false

namespace Hkdf.Proofs.Common.ExtractCaller.KeyContext

open Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.CallFrame

abbrev standardLayout :
    Hkdf.Proofs.Common.CallFrame.StackCallLayout hkdfSha256Extract.minStackBytes 32 64 720 :=
  ⟨528, 224, 400, by decide, by decide +kernel, by decide, by decide, by decide,
    by decide, by decide⟩

abbrev simpleLayout :
    Hkdf.Proofs.Common.CallFrame.StackCallLayout simpleHkdfSha256Extract.minStackBytes 32 64 720 :=
  ⟨544, 280, 536, by decide, by decide +kernel, by decide, by decide, by decide,
    by decide, by decide⟩

theorem key_context [bindings : Bindings] {initial s : RamState}
    {routine : Routine} {salt : Option ByteArray} {inputs : Array Input}
    (environment : MachineRamUnitStrideDecodable bindings initial)
    (call : ValidExtractCall routine initial salt inputs)
    (running : Running initial (returnBoundary initial)
      #v[Stack.region initial routine.minStackBytes] s)
    (layout : Hkdf.Proofs.Common.CallFrame.StackCallLayout routine.minStackBytes 32 64 720)
    (rip : s.RIP = Key.entryAddress)
    (rsp : stackPtr s = stackPtr initial - BitVec.ofNat 64 layout.stackOffset)
    (output : s.regValue .rdi = stackPtr initial - BitVec.ofNat 64 layout.outputOffset)
    (ret : InProgram (returnBoundary s).rip)
    (length : (s.regValue .rdx).toNat = (Standard.saltKey salt).size)
    (input : s.regValue .rsi = match salt with
      | none => stackPtr initial - BitVec.ofNat 64 layout.inputOffset
      | some _ => initial.regValue .rcx)
    (zeros : salt = none →
      MemoryRegion.HasBytes
        ⟨(stackPtr initial - BitVec.ofNat 64 layout.inputOffset).toNat, 32⟩
        s.external ⟨Array.replicate 32 0⟩) :
    Key.Context s (returnBoundary initial) (Standard.saltKey salt) := by
  have avoid : (Stack.region initial routine.minStackBytes).Avoids
      (fun a ↦ InProgram a ∨ Hkdf.Proofs.Program.InPageTables a) :=
    (call.stackSeparation.2 _ (by simp)).2
  have outside : ¬ InProgram (returnBoundary initial).rip := by
    obtain ⟨address, stored, _, outside⟩ := call.returnAddress
    have value : (returnBoundary initial).rip = address := by
      change memLoad initial.external (initial.regValue .rsp) 64 = address
      apply Hkdf.Proofs.Common.Memory.memLoad_of_loadBytes64
      simpa only [Stack.returnSlot, BitVec.ofNat_toNat, BitVec.setWidth_eq] using stored.2
    rwa [value]
  cases salt with
  | none =>
    refine ⟨callee_pre_of_stack environment.stringStride call.stack avoid outside
      running.machine running.directionFlag running.loaded running.allocated
      layout rip rsp input output ret, length, ?_⟩
    change (⟨(s.regValue .rsi).toNat, 32⟩ : MemoryRegion).HasBytes s.external
      ⟨Array.replicate 32 0⟩
    rw [input]
    exact zeros rfl
  | some bytes =>
    have member : extractSaltRegion initial bytes ∈
        (pointerTable initial inputs.size :: lengthTable initial inputs.size ::
          (inputs.map Input.region).toList ++ (some bytes).toList.map
            (extractSaltRegion initial)) := by simp
    have valid := Common.validInput_of_frame call.stackSeparation running.frame member
      (call.saltInMemory bytes (by simp))
    have apart : (extractSaltRegion initial bytes).Disjoint
        (Stack.region initial routine.minStackBytes) :=
      (call.stackSeparation.2 _ (by simp)).1 _ member
    have region : registerRegion s .rsi bytes.size = extractSaltRegion initial bytes := by
      simp only [registerRegion, extractSaltRegion, input]
    let outputLayout :
        Hkdf.Proofs.Common.CallFrame.StackCallLayout routine.minStackBytes 0 64 720 :=
      ⟨layout.stackOffset, layout.inputOffset, layout.outputOffset, layout.aligned,
        layout.capacity, layout.inputAbove, layout.outputAbove, by omega, layout.outputEnd, by
          rcases layout.separation with h | h
          · left; omega
          · exact .inr h⟩
    refine ⟨callee_pre_of_stack_output environment.stringStride call.stack avoid outside
      running.machine running.directionFlag running.loaded running.allocated
      outputLayout rip rsp output ret ?_ ?_ ?_, length, ?_⟩
    · change (registerRegion s .rsi bytes.size).Bounded
      rw [region]
      exact valid.1
    · change (registerRegion s .rsi bytes.size).Allocated s.external
      rw [region]
      exact Hkdf.Proofs.Common.Machine.allocated_of_hasBytes valid.2
    · change (registerRegion s .rsi bytes.size).Disjoint _
      rw [region]
      exact apart
    · change (registerRegion s .rsi bytes.size).HasBytes s.external bytes
      rw [region]
      exact valid.2

end Hkdf.Proofs.Common.ExtractCaller.KeyContext
