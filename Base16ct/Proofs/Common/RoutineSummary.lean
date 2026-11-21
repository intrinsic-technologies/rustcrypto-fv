import Base16ct.Proofs.Correctness

namespace Base16ct.Proofs.Common

open Base16ct.Spec Base16ct.Spec.Program Prelude X86 X86Proofs

structure RoutineABI where
  entry : BitVec 64
  argumentRegisters : List (Fin 16)
  resultRegisters : List (Fin 16)
  stackBytes : Nat
  callbackTarget : Option (BitVec 64)
  codeBytes : Nat

structure RoutineValues where
  output : Option ByteArray
  decoded : Option ByteArray
  length : Option Nat
  status : Option (BitVec 64)
  sinkCount : Option Nat

structure RoutineCodeFacts [bindings : Machine.Bindings]
    (abi : RoutineABI) (code : UserProcess.CodeMap)
    (boundary : UserProcess.ReturnBoundary) (initial phaseState : Machine.RamState) : Prop where
  entry : CodeIn code initial
  phase : CodeIn code phaseState
  apart : RangeApart abi.entry abi.codeBytes boundary.rip 1
  phaseRip : phaseState.RIP = abi.entry + BitVec.ofNat 64 abi.codeBytes

structure RoutineContinuation [bindings : Machine.Bindings]
    (boundary : UserProcess.ReturnBoundary) (state : Machine.RamState) : Prop where
  ready : ReadyToStep state
  returnAddress : boundary.rip.toNat < userAddressLimit ∧ ¬ InProgram boundary.rip
  returnSlot : MemReadable state (stackPtr state) 8
  returnTop : stackTop state = boundary.rip
  stackPointer : stackPtr state + 8#64 = boundary.rsp

structure RoutineSummary [bindings : Machine.Bindings]
    (abi : RoutineABI) (code : UserProcess.CodeMap)
    (boundary : UserProcess.ReturnBoundary)
    {n : Nat} (regions : Vector MemoryRegion n)
    (initial phase : Machine.RamState) (fuel : Nat)
    (changes : List Component) (values : RoutineValues) (valueEffect : Prop) : Prop where
  advances : Advances boundary fuel initial phase
  code : RoutineCodeFacts abi code boundary initial phase
  continuation : RoutineContinuation boundary phase
  writes : MemoryWriteFrame initial phase regions
  agrees : AgreesExcept changes initial phase
  calleeSaved : CalleeSavedRegistersUnchanged initial phase
  direction : DirectionFlagUnset phase
  value : valueEffect

structure RoutineReturn [bindings : Machine.Bindings]
    (boundary : UserProcess.ReturnBoundary)
    {n : Nat} (regions : Vector MemoryRegion n)
    (initial final : Machine.RamState) (fuel : Nat)
    (changes : List Component) (values : RoutineValues) (valueEffect : Prop) : Prop where
  returns : Returns boundary fuel initial final
  continuation : RoutineContinuation boundary final
  writes : MemoryWriteFrame initial final regions
  agrees : AgreesExcept changes initial final
  calleeSaved : CalleeSavedRegistersUnchanged initial final
  direction : DirectionFlagUnset final
  value : valueEffect

theorem RoutineSummary.compose_advances
    [bindings : Machine.Bindings]
    {abi : RoutineABI} {code : UserProcess.CodeMap}
    {boundary : UserProcess.ReturnBoundary} {n : Nat}
    {regions : Vector MemoryRegion n}
    {initial middle final : Machine.RamState}
    {fuel₁ fuel₂ : Nat} {values₁ values₂ : RoutineValues}
    {effect₁ effect₂ : Prop} {changes : List Component}
    (first : RoutineSummary abi code boundary regions initial middle fuel₁ changes values₁ effect₁)
    (second : RoutineSummary abi code boundary regions middle final fuel₂ changes values₂ effect₂) :
    Advances boundary (fuel₁ + fuel₂) initial final := by
  exact first.advances.trans second.advances

theorem RoutineSummary.continuation_ready
    [bindings : Machine.Bindings]
    {abi : RoutineABI} {code : UserProcess.CodeMap}
    {boundary : UserProcess.ReturnBoundary} {n : Nat}
    {regions : Vector MemoryRegion n}
    {initial phase : Machine.RamState} {fuel : Nat}
    {changes : List Component} {values : RoutineValues} {valueEffect : Prop}
    (summary : RoutineSummary abi code boundary regions initial phase fuel changes values valueEffect) :
    ReadyToStep phase := by
  exact summary.continuation.ready

end Base16ct.Proofs.Common
