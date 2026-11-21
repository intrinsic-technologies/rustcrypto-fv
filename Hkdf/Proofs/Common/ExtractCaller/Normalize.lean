import Hkdf.Proofs.Common.Machine.Boundary
import Hkdf.Proofs.Common.CallFrame.Stack
import Hkdf.Proofs.Common.ExtractCaller.KeyContext
import Hkdf.Proofs.Common.ExtractCaller.PadEntry
import Hkdf.Proofs.Common.Pad.Interface
import Hkdf.Proofs.Key
import Hkdf.Proofs.Common.Refine

set_option autoImplicit false

namespace Hkdf.Proofs.Common.ExtractCaller.Normalize

open Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.CallFrame

theorem to_pad [bindings : Bindings] {initial s : RamState}
    {routine : Routine} {salt : Option ByteArray} {inputs : Array Input}
    {v : Pad.Variant} {returnPC : BitVec 64}
    (call : ValidExtractCall routine initial salt inputs)
    (running : Running initial (returnBoundary initial)
      #v[Stack.region initial routine.minStackBytes] s)
    (ctx : Key.Context s (returnBoundary initial) (Standard.saltKey salt))
    (layout : Hkdf.Proofs.Common.CallFrame.StackCallLayout routine.minStackBytes 32 64 720)
    (rsp : stackPtr s = stackPtr initial - BitVec.ofNat 64 layout.stackOffset)
    (output : s.regValue .rdi = stackPtr initial - BitVec.ofNat 64 layout.outputOffset)
    (ret : returnBoundary s =
      ⟨returnPC, stackPtr initial - BitVec.ofNat 64 (layout.stackOffset - 8)⟩)
    (first : (Pad.layout v).first = 3)
    (buffer : layout.stackOffset = layout.outputOffset + (Pad.layout v).bufferOffset + 8)
    (entry : ∀ u, Running initial (returnBoundary initial)
        #v[Stack.region initial routine.minStackBytes] u → u.RIP = returnPC →
      ∃ t, Advances (returnBoundary initial) 2 u t ∧ ReadyToStep t ∧
        t.RIP = v.entry ∧ t.regValue .rax = 3 ∧
        AgreesExcept [.reg 0, .rip] u t ∧ t.external = u.external) :
    ∃ fuel t, Advances (returnBoundary initial) fuel initial t ∧ ReadyToStep t ∧
      Running initial (returnBoundary initial)
        #v[Stack.region initial routine.minStackBytes] t ∧
      t.regValue .rsp = stackPtr initial - BitVec.ofNat 64 (layout.stackOffset - 8) ∧
      Pad.Pre v (returnBoundary initial) t
        (stackPtr initial - BitVec.ofNat 64 layout.outputOffset)
        (HMAC.keyBlock (Standard.saltKey salt)) ∧
      MemoryWriteFrame s t #v[registerRegion s .rdi 64, Stack.region s 720] ∧
      Hkdf.Proofs.Program.PreservesABI s t := by
  obtain ⟨u, result, stored⟩ := Key.normalize_correct ctx
  have current : Running initial (returnBoundary initial)
      #v[Stack.region initial routine.minStackBytes] u :=
    running.of_callee result (by
      intro region member a contains
      exact ⟨Stack.region initial routine.minStackBytes, by simp,
        stack_layout_within call.stack layout rsp output region member a contains⟩)
  have ripU : u.RIP = returnPC := by
    rw [result.rip, ret]
  have rspU : u.regValue .rsp =
      stackPtr initial - BitVec.ofNat 64 (layout.stackOffset - 8) := by
    rw [result.rsp, ret]
  obtain ⟨t, run, ready, ripT, index, frame, memory⟩ := entry u current ripU
  have avoid : (Stack.region initial routine.minStackBytes).Avoids
      (fun a ↦ InProgram a ∨ Hkdf.Proofs.Program.InPageTables a) :=
    (call.stackSeparation.2 _ (by simp)).2
  have final : Running initial (returnBoundary initial)
      #v[Stack.region initial routine.minStackBytes] t :=
    current.of_agrees run ready frame (by
      intro c hc a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> exact ha.elim) (by
      intro region member a contains inside
      have equal : region = Stack.region initial routine.minStackBytes := by simpa using member
      subst region
      exact avoid a contains (.inl inside)) (by simp)
  have rspT : t.regValue .rsp =
      stackPtr initial - BitVec.ofNat 64 (layout.stackOffset - 8) :=
    (frame.read (n := 64) (r := 4) (by simp)).trans rspU
  have writable := Common.Machine.stack_writable call.stack
    (used := layout.outputOffset) (by
      have := layout.outputAbove
      have := layout.capacity
      omega) avoid
  have bufferWritable : Hkdf.Proofs.Refine.Writable Extracted.programImage initial.external
      (stackPtr initial - BitVec.ofNat 64 layout.outputOffset) 64 :=
    writable.sub (Nat.le_refl _) (by have := layout.outputEnd; omega)
  have bytes : (⟨(stackPtr initial - BitVec.ofNat 64 layout.outputOffset).toNat, 64⟩ :
      MemoryRegion).HasBytes t.external (HMAC.keyBlock (Standard.saltKey salt)) := by
    rw [memory]
    simpa only [registerRegion, output] using stored
  have relation : layout.outputOffset + (Pad.layout v).bufferOffset =
      layout.stackOffset - 8 := by omega
  have pre : Pad.Pre v (returnBoundary initial) t
      (stackPtr initial - BitVec.ofNat 64 layout.outputOffset)
      (HMAC.keyBlock (Standard.saltKey salt)) := {
    machine := final.machine
    loaded := final.loaded
    directionFlag := final.directionFlag
    outside := ctx.outerBoundary
    rip := ripT
    index := by rw [first]; exact index
    base := by
      rw [rspT, ← relation, BitVec.ofNat_add]
      bv_omega
    bytes := bytes
    writable := ⟨⟨bufferWritable.readable.low,
      fun i hi ↦ final.allocated _ (bufferWritable.readable.present i hi)⟩,
      bufferWritable.tables, bufferWritable.notCode⟩
  }
  obtain ⟨fuel, execution⟩ := final.execution
  have abi : Hkdf.Proofs.Program.PreservesABI u t :=
    Hkdf.Proofs.Common.Machine.preservesABI_of_agrees frame current.directionFlag (by
      intro register member
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first
        | exact frame.read (n := 64) (r := 3) (by simp)
        | exact frame.read (n := 64) (r := 5) (by simp)
        | exact frame.read (n := 64) (r := 12) (by simp)
        | exact frame.read (n := 64) (r := 13) (by simp)
        | exact frame.read (n := 64) (r := 14) (by simp)
        | exact frame.read (n := 64) (r := 15) (by simp)) (by simp) (by simp) (by simp)
  refine ⟨fuel, t, execution, ready, final, rspT, pre, ?_,
    Common.Machine.preservesABI_trans result.abi abi⟩
  intro address outside
  rw [memory]
  exact result.frame address outside

theorem standard [bindings : Bindings] {initial s : RamState}
    {salt : Option ByteArray} {inputs : Array Input}
    (call : ValidExtractCall hkdfSha256Extract initial salt inputs)
    (running : Running initial (returnBoundary initial)
      #v[Stack.region initial hkdfSha256Extract.minStackBytes] s)
    (ctx : Key.Context s (returnBoundary initial) (Standard.saltKey salt))
    (rsp : stackPtr s = stackPtr initial - 528)
    (output : s.regValue .rdi = stackPtr initial - 400)
    (ret : returnBoundary s = ⟨0x101497, stackPtr initial - 520⟩) :
    ∃ fuel t, Advances (returnBoundary initial) fuel initial t ∧ ReadyToStep t ∧
      Running initial (returnBoundary initial)
        #v[Stack.region initial hkdfSha256Extract.minStackBytes] t ∧
      t.regValue .rsp = stackPtr initial - 520 ∧
      Pad.Pre .v1014a0 (returnBoundary initial) t (stackPtr initial - 400)
        (HMAC.keyBlock (Standard.saltKey salt)) ∧
      MemoryWriteFrame s t #v[registerRegion s .rdi 64, Stack.region s 720] ∧
      Hkdf.Proofs.Program.PreservesABI s t := by
  apply to_pad call running ctx KeyContext.standardLayout rsp output ret (by rfl) (by rfl)
  intro u current ripU
  obtain ⟨t, run, ready, _, _, ripT, index, frame, memory⟩ := PadEntry.standard
    (Hkdf.Proofs.Common.Machine.supportedMachine_readyToStep current.machine)
    current.machine current.loaded ctx.outerBoundary ripU
  exact ⟨t, run, ready, ripT, index, frame, memory⟩

theorem simple [bindings : Bindings] {initial s : RamState}
    {salt : Option ByteArray} {inputs : Array Input}
    (call : ValidExtractCall simpleHkdfSha256Extract initial salt inputs)
    (running : Running initial (returnBoundary initial)
      #v[Stack.region initial simpleHkdfSha256Extract.minStackBytes] s)
    (ctx : Key.Context s (returnBoundary initial) (Standard.saltKey salt))
    (rsp : stackPtr s = stackPtr initial - 544)
    (output : s.regValue .rdi = stackPtr initial - 536)
    (ret : returnBoundary s = ⟨0x105cec, stackPtr initial - 536⟩) :
    ∃ fuel t, Advances (returnBoundary initial) fuel initial t ∧ ReadyToStep t ∧
      Running initial (returnBoundary initial)
        #v[Stack.region initial simpleHkdfSha256Extract.minStackBytes] t ∧
      t.regValue .rsp = stackPtr initial - 536 ∧
      Pad.Pre .v105d00 (returnBoundary initial) t (stackPtr initial - 536)
        (HMAC.keyBlock (Standard.saltKey salt)) ∧
      MemoryWriteFrame s t #v[registerRegion s .rdi 64, Stack.region s 720] ∧
      Hkdf.Proofs.Program.PreservesABI s t := by
  apply to_pad call running ctx KeyContext.simpleLayout rsp output ret (by rfl) (by rfl)
  intro u current ripU
  obtain ⟨t, run, ready, _, _, ripT, index, frame, memory⟩ := PadEntry.simple
    (Hkdf.Proofs.Common.Machine.supportedMachine_readyToStep current.machine)
    current.machine current.loaded ctx.outerBoundary ripU
  exact ⟨t, run, ready, ripT, index, frame, memory⟩

end Hkdf.Proofs.Common.ExtractCaller.Normalize
