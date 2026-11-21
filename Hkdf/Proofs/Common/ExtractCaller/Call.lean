import Hkdf.Proofs.Common.CallFrame.Stack
import Hkdf.Proofs.Common.Machine.StackRegion

set_option autoImplicit false

namespace Hkdf.Proofs.Common.ExtractCaller.Call

open Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.CallFrame

theorem key_call [bindings : Bindings] {initial s : RamState}
    {routine : Routine} {salt : Option ByteArray} {inputs : Array Input}
    {used codeOffset : Nat} {displacement : BitVec 32}
    (call : ValidExtractCall routine initial salt inputs)
    (running : Running initial (returnBoundary initial)
      #v[Stack.region initial routine.minStackBytes] s)
    (outside : ¬ InProgram (returnBoundary initial).rip)
    (rsp : stackPtr s = stackPtr initial - BitVec.ofNat 64 used)
    (rip : s.RIP = Extracted.textAddress + BitVec.ofNat 64 codeOffset)
    (capacity : used + 8 ≤ routine.minStackBytes) (aligned : (used + 8) % 8 = 0)
    (bounded : codeOffset + 5 ≤ 115149)
    (bytes : Extracted.textBytes.toListFrom codeOffset 5 = encodeCallRel32 displacement)
    (target : branchTarget (Extracted.textAddress + BitVec.ofNat 64 codeOffset) 5
      (displacement.signExtend 64) = 0x116320) :
    ∃ t, Running initial (returnBoundary initial)
        #v[Stack.region initial routine.minStackBytes] t ∧
      (callEffect (fun _ ↦ 0x116320)
        (Extracted.textAddress + BitVec.ofNat 64 codeOffset + 5) s).Holds s t ∧
      t.RIP = 0x116320 ∧
      stackPtr t = stackPtr initial - BitVec.ofNat 64 (used + 8) ∧
      returnBoundary t =
        ⟨Extracted.textAddress + BitVec.ofNat 64 codeOffset + 5,
          stackPtr initial - BitVec.ofNat 64 used⟩ := by
  have avoid : (Stack.region initial routine.minStackBytes).Avoids
      (fun a ↦ InProgram a ∨ Hkdf.Proofs.Program.InPageTables a) :=
    (call.stackSeparation.2 _ (by simp)).2
  have avoidCode : (Stack.region initial routine.minStackBytes).Avoids InProgram :=
    fun a ha hp ↦ avoid a ha (.inl hp)
  have pushed : pushAddr s = stackPtr initial - BitVec.ofNat 64 (used + 8) := by
    rw [pushAddr, rsp, BitVec.sub_sub, BitVec.ofNat_add]
    rfl
  have writable : MemWritable s (pushAddr s) 8 := by
    rw [pushed]
    exact stack_writable8 call.stack avoid running.allocated capacity aligned
  have apart : RangeApart (pushAddr s) 8
      (Extracted.textAddress + BitVec.ofNat 64 codeOffset) 5 := by
    rw [pushed]
    exact stack_codeApart call.stack avoidCode capacity (by omega) bounded
  have writes : WritesWithin
      (callEffect (fun _ ↦ (0x116320 : BitVec 64))
        (Extracted.textAddress + BitVec.ofNat 64 codeOffset + 5) s).components
      #v[Stack.region initial routine.minStackBytes] := by
    intro c hc a ha
    simp only [callEffect, pushEffect_components, pushed,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact ha.elim
    · exact ⟨Stack.region initial routine.minStackBytes, by simp,
        Hkdf.Proofs.Common.Machine.stackRegion_contains_sub
          call.stack.2.2.1 capacity (by omega) ha⟩
    · exact ha.elim
  have step := call_rel32_effect_step
    (Extracted.textAddress + BitVec.ofNat 64 codeOffset) displacement
    (by rw [target]; decide)
  simp only [target] at step
  have instruction := programText_slice (programLoaded_codeIn running.loaded) codeOffset
    (encodeCallRel32 displacement) (by
      change codeOffset + 5 ≤ 115149
      exact bounded) (by
      change Extracted.textBytes.toListFrom codeOffset 5 = _
      exact bytes)
  obtain ⟨t, runningT, effect, boundaryT⟩ := running.call step instruction
    ⟨rip, writable, apart⟩
    (boundary_ne_program outside (inProgram_of_textOffset 0x16320 (by decide)))
    writes (by
      intro region member
      have equal : region = Stack.region initial routine.minStackBytes := by simpa using member
      subst region
      exact avoidCode)
  refine ⟨t, runningT, effect, effect.rip, effect.writes.1.trans pushed, ?_⟩
  rw [rsp] at boundaryT
  exact boundaryT

theorem standard [bindings : Bindings] {initial s : RamState}
    {salt : Option ByteArray} {inputs : Array Input}
    (call : ValidExtractCall hkdfSha256Extract initial salt inputs)
    (running : Running initial (returnBoundary initial)
      #v[Stack.region initial hkdfSha256Extract.minStackBytes] s)
    (outside : ¬ InProgram (returnBoundary initial).rip)
    (rsp : stackPtr s = stackPtr initial - 520) (rip : s.RIP = 0x101492) :
    ∃ t, Running initial (returnBoundary initial)
        #v[Stack.region initial hkdfSha256Extract.minStackBytes] t ∧
      (callEffect (fun _ ↦ 0x116320) 0x101497 s).Holds s t ∧
      t.RIP = 0x116320 ∧ stackPtr t = stackPtr initial - 528 ∧
      returnBoundary t = ⟨0x101497, stackPtr initial - 520⟩ := by
  exact key_call (used := 520) (codeOffset := 0x1492) (displacement := 0x14e89)
    call running outside rsp rip (by decide +kernel) (by decide) (by decide)
    (by decide +kernel) (by decide)

theorem simple [bindings : Bindings] {initial s : RamState}
    {salt : Option ByteArray} {inputs : Array Input}
    (call : ValidExtractCall simpleHkdfSha256Extract initial salt inputs)
    (running : Running initial (returnBoundary initial)
      #v[Stack.region initial simpleHkdfSha256Extract.minStackBytes] s)
    (outside : ¬ InProgram (returnBoundary initial).rip)
    (rsp : stackPtr s = stackPtr initial - 536) (rip : s.RIP = 0x105ce7) :
    ∃ t, Running initial (returnBoundary initial)
        #v[Stack.region initial simpleHkdfSha256Extract.minStackBytes] t ∧
      (callEffect (fun _ ↦ 0x116320) 0x105cec s).Holds s t ∧
      t.RIP = 0x116320 ∧ stackPtr t = stackPtr initial - 544 ∧
      returnBoundary t = ⟨0x105cec, stackPtr initial - 536⟩ := by
  exact key_call (used := 536) (codeOffset := 0x5ce7) (displacement := 0x10634)
    call running outside rsp rip (by decide +kernel) (by decide) (by decide)
    (by decide +kernel) (by decide)

end Hkdf.Proofs.Common.ExtractCaller.Call
