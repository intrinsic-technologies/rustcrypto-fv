import Hkdf.Proofs.Common.Encoding.Serialize.PushStack
import Hkdf.Proofs.Common.Machine.Boundary
import Hkdf.Proofs.Standard.State
import Hkdf.Proofs.Common.ExtractCaller.EnterKey
import Hkdf.Proofs.Common.ExtractCaller.Normalize
import Hkdf.Proofs.Common.ExtractCaller.Spill
import Hkdf.Proofs.Common.ExtractCaller.Prepare
import Hkdf.Proofs.Common.Machine.StackRegion
import Hkdf.Proofs.Common.ExtractCaller.Allocate
import Hkdf.Proofs.Common.Encoding.Serialize.Prologue
import Hkdf.Proofs.Common.CallFrame
import Hkdf.Proofs.Common.Machine.Code

set_option autoImplicit false

namespace Hkdf.Proofs.Common.ExtractCaller

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Spec.Program
open Hkdf.Proofs.Common
open Hkdf.Proofs.Common.Machine

structure SimpleContext [bindings : Bindings]
    (initial : RamState) (salt : Option ByteArray) (inputs : Array Input) : Prop where
  environment : MachineRamUnitStrideDecodable bindings initial
  machine : SupportedIntegerMachineState bindings.processor initial
  call : ValidExtractCall simpleHkdfSha256Extract initial salt inputs

theorem save_registers [bindings : Bindings]
    {initial : RamState} {salt : Option ByteArray} {inputs : Array Input}
    {routine : Routine} {codeOffset : Nat}
    (environment : MachineRamUnitStrideDecodable bindings initial)
    (machine : SupportedIntegerMachineState bindings.processor initial)
    (call : ValidExtractCall routine initial salt inputs)
    (reserve : 48 ≤ routine.minStackBytes)
    (entry : routine.entryAddress = Extracted.textAddress + BitVec.ofNat 64 codeOffset)
    (code : Hkdf.Proofs.Common.Encoding.Serialize.SaveCode codeOffset) :
    ∃ s, Advances (returnBoundary initial) 6 initial s ∧ ReadyToStep s ∧
      CallFrame.Running initial (returnBoundary initial)
        #v[Stack.region initial routine.minStackBytes] s ∧
      s.RIP = Extracted.textAddress + BitVec.ofNat 64 (codeOffset + 10) ∧
      stackPtr s = stackPtr initial - 48 ∧
      s.external = Hkdf.Proofs.Common.Encoding.Serialize.saveMemory initial ∧
      AgreesExcept (Hkdf.Proofs.Common.Encoding.Serialize.saveFrame initial) initial s := by
  have ready := (Hkdf.Proofs.Common.Machine.entryReady bindings environment machine
    call.programLoaded).ready
  have outside := (Hkdf.Proofs.Common.Machine.returnBoundary_valid
    ready call.stack call.returnAddress).2.2
  have push : Hkdf.Proofs.Common.Encoding.Serialize.PushSteps initial (returnBoundary initial) := by
    constructor
    intro s ready loaded grow src offset codeOffset rsp rip bound align size bytes
    exact Hkdf.Proofs.Common.Encoding.Serialize.push_exists_of_stack call.stack
      (call.stackSeparation.2 _ (by simp)).2 outside ready loaded grow src offset codeOffset
      rsp rip (by omega) align size bytes
  obtain ⟨s, run, readyS, loaded, rip, rsp, memory, agrees⟩ :=
    Hkdf.Proofs.Common.Encoding.Serialize.save_registers_of_push push ready call.programLoaded
      (call.entry.trans entry) code
  have initialRunning : CallFrame.Running initial (returnBoundary initial)
      #v[Stack.region initial routine.minStackBytes] initial :=
    CallFrame.Running.initial (Hkdf.Proofs.Program.SupportedMachine.of_root
      bindings initial machine environment) call.programLoaded call.directionFlagUnset
  have within {offset : BitVec 64} (bound : offset.toNat ≤ routine.minStackBytes)
      (lower : 8 ≤ offset.toNat) {address : BitVec 64}
      (covered : (Component.mem (stackPtr initial - offset) 8).Covers address) :
      (Stack.region initial routine.minStackBytes).Contains address.toNat := by
    apply Hkdf.Proofs.Common.Machine.stackRegion_contains_sub call.stack.2.2.1 bound lower
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using covered
  have writes : WritesWithin (Hkdf.Proofs.Common.Encoding.Serialize.saveFrame initial)
      #v[Stack.region initial routine.minStackBytes] := by
    intro component member address covered
    simp only [Hkdf.Proofs.Common.Encoding.Serialize.saveFrame, List.mem_cons,
      List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact covered.elim
    · exact covered.elim
    all_goals exact ⟨Stack.region initial routine.minStackBytes, by simp,
      within (by simp only [BitVec.reduceToNat]; omega) (by decide) covered⟩
  have running := initialRunning.of_agrees run readyS agrees writes
    (fun region member address contained inProgram ↦
      (call.stackSeparation.2 region member).2 address contained (.inl inProgram))
    (by simp only [Hkdf.Proofs.Common.Encoding.Serialize.saveFrame, List.mem_cons,
      List.not_mem_nil, or_false, reduceCtorEq, not_false_eq_true])
  exact ⟨s, run, readyS, running, rip, rsp, memory, agrees⟩

theorem prologue [bindings : Bindings]
    {initial : RamState} {salt : Option ByteArray} {inputs : Array Input}
    {routine : Routine} {codeOffset : Nat} {amount : BitVec 32}
    (environment : MachineRamUnitStrideDecodable bindings initial)
    (machine : SupportedIntegerMachineState bindings.processor initial)
    (call : ValidExtractCall routine initial salt inputs)
    (reserve : 48 ≤ routine.minStackBytes)
    (entry : routine.entryAddress = Extracted.textAddress + BitVec.ofNat 64 codeOffset)
    (code : Hkdf.Proofs.Common.Encoding.Serialize.SaveCode codeOffset)
    (bounded : codeOffset + 17 < 115149)
    (bytes : Extracted.textBytes.toListFrom (codeOffset + 10) 7 =
      0x48 :: 0x81 :: 0xec :: immBytes 32 amount) :
    ∃ s, Advances (returnBoundary initial) 7 initial s ∧ ReadyToStep s ∧
      CallFrame.Running initial (returnBoundary initial)
        #v[Stack.region initial routine.minStackBytes] s ∧
      s.RIP = Extracted.textAddress + BitVec.ofNat 64 (codeOffset + 17) ∧
      stackPtr s = stackPtr initial - 48 - amount.signExtend 64 ∧
      s.external = Hkdf.Proofs.Common.Encoding.Serialize.saveMemory initial ∧
      AgreesExcept (Hkdf.Proofs.Common.Encoding.Serialize.saveFrame initial ++
        [.reg 4, .flags, .rip]) initial s := by
  obtain ⟨s, run, ready, running, rip, rsp, memory, agrees⟩ :=
    save_registers environment machine call reserve entry code
  have initialReady := (Hkdf.Proofs.Common.Machine.entryReady bindings environment machine
    call.programLoaded).ready
  have outside := (Hkdf.Proofs.Common.Machine.returnBoundary_valid
    initialReady call.stack call.returnAddress).2.2
  obtain ⟨t, runSub, readyT, _, _, ripT, rspT, frame, memoryT⟩ :=
    Allocate.sub_rsp ready running.machine running.loaded outside rip bounded bytes
  have writes : WritesWithin [.reg 4, .flags, .rip]
      #v[Stack.region initial routine.minStackBytes] := by
    intro component member address covered
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> exact covered.elim
  have runningT := running.of_agrees runSub readyT frame writes
    (fun region member address contained inProgram ↦
      (call.stackSeparation.2 region member).2 address contained (.inl inProgram))
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, reduceCtorEq,
      not_false_eq_true])
  exact ⟨t, run.trans runSub, readyT, runningT, ripT,
    rspT.trans (congrArg (fun p ↦ p - amount.signExtend 64) rsp),
    memoryT.trans memory, agrees.trans frame⟩

theorem standard_prologue [bindings : Bindings]
    {initial : RamState} {salt : Option ByteArray} {inputs : Array Input}
    (context : Hkdf.Proofs.Standard.Context initial salt inputs) :
    ∃ s, Advances (returnBoundary initial) 7 initial s ∧ ReadyToStep s ∧
      CallFrame.Running initial (returnBoundary initial)
        #v[Stack.region initial hkdfSha256Extract.minStackBytes] s ∧
      s.RIP = 0x101431 ∧ stackPtr s = stackPtr initial - 520 ∧
      s.external = Hkdf.Proofs.Common.Encoding.Serialize.saveMemory initial ∧
      AgreesExcept (Hkdf.Proofs.Common.Encoding.Serialize.saveFrame initial ++
        [.reg 4, .flags, .rip]) initial s := by
  obtain ⟨s, run, ready, running, rip, rsp, memory, agrees⟩ :=
    prologue (codeOffset := 0x1420) (amount := 472)
      context.environment context.machine context.call (by decide +kernel)
      (by decide +kernel) (by constructor <;> decide +kernel) (by decide +kernel)
      (by decide +kernel)
  refine ⟨s, run, ready, running, rip.trans (by decide +kernel), ?_, memory, agrees⟩
  rw [BitVec.sub_sub,
    show (48 : BitVec 64) + (BitVec.signExtend 64 (472 : BitVec 32)) = 520
      by decide +kernel] at rsp
  exact rsp

theorem simple_prologue [bindings : Bindings]
    {initial : RamState} {salt : Option ByteArray} {inputs : Array Input}
    (context : SimpleContext initial salt inputs) :
    ∃ s, Advances (returnBoundary initial) 7 initial s ∧ ReadyToStep s ∧
      CallFrame.Running initial (returnBoundary initial)
        #v[Stack.region initial simpleHkdfSha256Extract.minStackBytes] s ∧
      s.RIP = 0x105c81 ∧ stackPtr s = stackPtr initial - 536 ∧
      s.external = Hkdf.Proofs.Common.Encoding.Serialize.saveMemory initial ∧
      AgreesExcept (Hkdf.Proofs.Common.Encoding.Serialize.saveFrame initial ++
        [.reg 4, .flags, .rip]) initial s := by
  obtain ⟨s, run, ready, running, rip, rsp, memory, agrees⟩ :=
    prologue (codeOffset := 0x5c70) (amount := 488)
      context.environment context.machine context.call (by decide +kernel)
      (by decide +kernel) (by constructor <;> decide +kernel) (by decide +kernel)
      (by decide +kernel)
  refine ⟨s, run, ready, running, rip.trans (by decide +kernel), ?_, memory, agrees⟩
  rw [BitVec.sub_sub,
    show (48 : BitVec 64) + (BitVec.signExtend 64 (488 : BitVec 32)) = 536
      by decide +kernel] at rsp
  exact rsp

theorem middle_state [bindings : Bindings] (simple : Bool)
    {initial : RamState} {salt : Option ByteArray} {inputs : Array Input}
    (environment : MachineRamUnitStrideDecodable bindings initial)
    (machine : SupportedIntegerMachineState bindings.processor initial)
    (call : ValidExtractCall (if simple then simpleHkdfSha256Extract else hkdfSha256Extract)
      initial salt inputs) :
    ∃ s, CallFrame.Running initial (returnBoundary initial)
        #v[Stack.region initial
          (if simple then simpleHkdfSha256Extract else hkdfSha256Extract).minStackBytes] s ∧
      s.RIP = Extracted.textAddress + BitVec.ofNat 64 (Prepare.middleOffset simple) ∧
      stackPtr s = stackPtr initial - BitVec.ofNat 64 (Prepare.allocation simple) ∧
      s.regValue .rcx = initial.regValue .rcx ∧ s.regValue .r8 = initial.regValue .r8 := by
  have ready := (Hkdf.Proofs.Common.Machine.entryReady bindings environment machine
    call.programLoaded).ready
  have outside := (Hkdf.Proofs.Common.Machine.returnBoundary_valid
    ready call.stack call.returnAddress).2.2
  cases simple
  · obtain ⟨p, _, _, running, rip, rsp, _, frame⟩ :=
      standard_prologue ⟨environment, machine, call⟩
    obtain ⟨s, _, _, current, _, rspS, ripS, rcxS, r8S⟩ :=
      Spill.standard call running outside rsp rip
    refine ⟨s, current, ripS.trans (by decide +kernel), ?_, ?_, ?_⟩
    · exact rspS.trans rsp
    · exact rcxS.trans (frame.read (n := 64) (r := 1)
        (by simp [Hkdf.Proofs.Common.Encoding.Serialize.saveFrame]))
    · exact r8S.trans (frame.read (n := 64) (r := 8)
        (by simp [Hkdf.Proofs.Common.Encoding.Serialize.saveFrame]))
  · obtain ⟨p, _, _, running, rip, rsp, _, frame⟩ :=
      simple_prologue ⟨environment, machine, call⟩
    obtain ⟨s, _, _, current, _, rspS, ripS, rcxS, r8S⟩ :=
      Spill.simple call running outside rsp rip
    refine ⟨s, current, ripS.trans (by decide +kernel), ?_, ?_, ?_⟩
    · exact rspS.trans rsp
    · exact rcxS.trans (frame.read (n := 64) (r := 1)
        (by simp [Hkdf.Proofs.Common.Encoding.Serialize.saveFrame]))
    · exact r8S.trans (frame.read (n := 64) (r := 8)
        (by simp [Hkdf.Proofs.Common.Encoding.Serialize.saveFrame]))

theorem pad_pre [bindings : Bindings] (simple : Bool)
    {initial : RamState} {salt : Option ByteArray} {inputs : Array Input}
    (environment : MachineRamUnitStrideDecodable bindings initial)
    (machine : SupportedIntegerMachineState bindings.processor initial)
    (call : ValidExtractCall (EnterKey.routine simple) initial salt inputs) :
    ∃ fuel s, Advances (returnBoundary initial) fuel initial s ∧ ReadyToStep s ∧
      CallFrame.Running initial (returnBoundary initial)
        #v[Stack.region initial (EnterKey.routine simple).minStackBytes] s ∧
      s.regValue .rsp = stackPtr initial - BitVec.ofNat 64 (Prepare.allocation simple) ∧
      Pad.Pre (if simple then .v105d00 else .v1014a0) (returnBoundary initial) s
        (stackPtr initial - BitVec.ofNat 64 (EnterKey.layout simple).outputOffset)
        (HMAC.keyBlock (Hkdf.Proofs.Standard.saltKey salt)) := by
  obtain ⟨s, running, rip, rsp, rcx, r8⟩ := middle_state simple environment machine call
  obtain ⟨key, runningKey, context, keyRsp, output, ret, _, _⟩ :=
    EnterKey.run simple environment call running rip rsp rcx r8
  cases simple
  · obtain ⟨fuel, t, run, ready, final, rspT, pre, _, _⟩ :=
      Normalize.standard call runningKey context keyRsp output ret
    exact ⟨fuel, t, run, ready, final, rspT, pre⟩
  · obtain ⟨fuel, t, run, ready, final, rspT, pre, _, _⟩ :=
      Normalize.simple call runningKey context keyRsp output ret
    exact ⟨fuel, t, run, ready, final, rspT, pre⟩

theorem standard_pad_pre [bindings : Bindings]
    {initial : RamState} {salt : Option ByteArray} {inputs : Array Input}
    (context : Hkdf.Proofs.Standard.Context initial salt inputs) :
    ∃ fuel s, Advances (returnBoundary initial) fuel initial s ∧ ReadyToStep s ∧
      CallFrame.Running initial (returnBoundary initial)
        #v[Stack.region initial hkdfSha256Extract.minStackBytes] s ∧
      s.regValue .rsp = stackPtr initial - 520 ∧
      Pad.Pre .v1014a0 (returnBoundary initial) s (stackPtr initial - 400)
        (HMAC.keyBlock (Hkdf.Proofs.Standard.saltKey salt)) :=
  pad_pre false context.environment context.machine context.call

theorem simple_pad_pre [bindings : Bindings]
    {initial : RamState} {salt : Option ByteArray} {inputs : Array Input}
    (context : SimpleContext initial salt inputs) :
    ∃ fuel s, Advances (returnBoundary initial) fuel initial s ∧ ReadyToStep s ∧
      CallFrame.Running initial (returnBoundary initial)
        #v[Stack.region initial simpleHkdfSha256Extract.minStackBytes] s ∧
      s.regValue .rsp = stackPtr initial - 536 ∧
      Pad.Pre .v105d00 (returnBoundary initial) s (stackPtr initial - 536)
        (HMAC.keyBlock (Hkdf.Proofs.Standard.saltKey salt)) :=
  pad_pre true context.environment context.machine context.call

end Hkdf.Proofs.Common.ExtractCaller
