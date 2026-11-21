import Sha2.Proofs.Common.SHA256.Absorb.Contract

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Absorb.Direct

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field Sha2.Proofs.Common.Machine

inductive Stage where
  | select | smallSetup | smallStore | bulkSetup | bulkTail | tailSetup
  deriving DecidableEq

structure Layout where
  initialHash : Array UInt32 := NIST.SHA256.initialHash
  frameBytes : Nat
  bufferOffset : Nat
  pc : Stage → BitVec 64
  bytes : Stage → List UInt8
  smallCall : CallSite
  bulkCall : CallSite
  tailCall : CallSite
  exit : BitVec 64

def Layout.sp (l : Layout) (initial : RamState) : BitVec 64 :=
  stackPtr initial - BitVec.ofNat 64 l.frameBytes

def Layout.buffer (l : Layout) (sp : BitVec 64) : BitVec 64 := sp + BitVec.ofNat 64 l.bufferOffset

def footprint (l : Layout) (sp : BitVec 64) : Vector MemoryRegion 2 :=
  #v[⟨(l.buffer sp).toNat, 104⟩, ⟨(sp - 344).toNat, 344⟩]

def clobbered : List (BitVec 5) := [0, 1, 2, 6, 7, 8, 9, 10, 11, 14, 15]

def Stage.effect (stage : Stage) (l : Layout) (sp : BitVec 64) (s : RamState) : Effect :=
  let buffer := l.buffer sp
  match stage with
  | .select =>
      { rip := if (s.regValue .r14).toNat ≤ 63 then l.pc .smallSetup else l.pc .bulkSetup
        flags := some ⟨none, none, none, none, none, none⟩ }
  | .smallSetup =>
      { rip := l.smallCall.pc
        writes := [⟨(.reg 7 : Operand 64), buffer⟩, ⟨(.reg 2 : Operand 64), s.regValue .r14⟩] }
  | .smallStore =>
      { rip := l.exit
        writes := [⟨(.mem (buffer + 63) : Operand 8), (s.regValue .r14).setWidth 8⟩] }
  | .bulkSetup =>
      { rip := l.bulkCall.pc
        writes := [⟨(.reg 7 : Operand 64), buffer + 64⟩,
          ⟨(.reg 2 : Operand 64), s.regValue .r14 >>> 6⟩,
          ⟨(.reg 15 : Operand 64), s.regValue .rsi + (s.regValue .r14 &&& 0x7fffffffffffffc0)⟩,
          ⟨(.reg 14 : Operand 64), ((s.regValue .r14).setWidth 32 &&& 63).setWidth 64⟩,
          ⟨(.mem (buffer + 96) : Operand 64), s.regValue .r14 >>> 6⟩]
        flags := some ⟨none, none, none, none, none, none⟩ }
  | .bulkTail =>
      { rip := l.pc .tailSetup
        writes := [⟨(.mem (buffer + 63) : Operand 8), (s.regValue .r14).setWidth 8⟩] }
  | .tailSetup =>
      { rip := l.tailCall.pc
        writes := [⟨(.reg 7 : Operand 64), buffer⟩, ⟨(.reg 6 : Operand 64), s.regValue .r15⟩,
          ⟨(.reg 2 : Operand 64), s.regValue .r14⟩] }

structure Stage.Pre (stage : Stage) (l : Layout) (sp : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = l.pc stage
  rsp : stackPtr s = sp
  tailWritable : Common.Instructions.CrossPageStore.Writable s (l.buffer sp + 63) 1
  counterWritable : Common.Instructions.CrossPageStore.Writable s (l.buffer sp + 96) 8
  tailApart : RangeApart (l.buffer sp + 63) 1 (l.pc stage) (l.bytes stage).length
  counterApart : RangeApart (l.buffer sp + 96) 8 (l.pc stage) (l.bytes stage).length

structure WellFormed (l : Layout) (reserve : Nat) : Prop where
  capacity : l.frameBytes + 344 ≤ reserve
  aligned : (l.frameBytes + 8) % 16 = 0
  bufferFits : l.bufferOffset + 104 ≤ l.frameBytes
  hashAligned : (l.bufferOffset + 64) % 4 = 0

structure Flow (l : Layout) : Prop where
  smallReturn : l.smallCall.pc + BitVec.ofNat 64 l.smallCall.encoding.bytes.length = l.pc .smallStore
  bulkReturn : l.bulkCall.pc + BitVec.ofNat 64 l.bulkCall.encoding.bytes.length = l.pc .bulkTail
  tailReturn : l.tailCall.pc + BitVec.ofNat 64 l.tailCall.encoding.bytes.length = l.exit
  copyTargets : ∀ call ∈ [l.smallCall, l.tailCall],
    ∃ disp, call.encoding = .memory (.rip disp) ∧ call.pc + 6 + disp.signExtend 64 = 0x200280
  compressionTarget : ∃ disp, l.bulkCall.encoding = .relative disp ∧
    branchTarget l.bulkCall.pc 5 (disp.signExtend 64) = 0x10b4e0

structure CodeFacts (l : Layout) : Prop where
  blocks : ∀ stage s, ProgramLoaded s → CodeIn (codeRange (l.pc stage) (l.bytes stage)) s
  calls : ∀ call ∈ [l.smallCall, l.bulkCall, l.tailCall], ∀ s,
    ProgramLoaded s → CodeIn (codeRange call.pc call.encoding.bytes) s
  inside : ∀ stage, InProgram (l.pc stage)
  callsInside : ∀ call ∈ [l.smallCall, l.bulkCall, l.tailCall], InProgram call.pc
  exitInside : InProgram l.exit

structure BlockContracts [Bindings] (l : Layout) (boundary : ReturnBoundary) : Prop where
  run : ∀ stage sp, AdvanceTriple boundary (stage.Pre l sp)
    (codeRange (l.pc stage) (l.bytes stage)) (Effect.post (stage.effect l sp))

structure Prepared (l : Layout) (sp : BitVec 64) (input : Input) (s : RamState) : Prop where
  rip : s.RIP = l.pc .select
  rsp : stackPtr s = sp
  hasher : HasherAt s (l.buffer sp) ByteArray.empty l.initialHash
  source : s.regValue .rsi = input.address
  length : s.regValue .r14 = BitVec.ofNat 64 input.bytes.size
  bytes : input.region.HasBytes s.external input.bytes
  bounded : input.region.Bounded
  lengthBound : input.bytes.size < 2^61

structure Finished [Bindings] (l : Layout) (initial before current : RamState)
    {n : Nat} (regions : Vector MemoryRegion n) (input : Input) : Prop where
  state : ExecutionState initial current regions
  rip : current.RIP = l.exit
  rsp : stackPtr current = l.sp initial
  hasher : HasherAt current (l.buffer (l.sp initial)) input.bytes l.initialHash
  memory : MemoryWriteFrame before current (footprint l (l.sp initial))
  registers : ∀ r : BitVec 5, r.toNat < 16 → r ∉ clobbered →
    (.reg r : Operand 64).read current = (.reg r : Operand 64).read before

def Contract [bindings : Bindings] (l : Layout) : Prop :=
  ∀ {initial s : RamState} {n reserve : Nat} {regions : Vector MemoryRegion n} {input : Input},
    WellFormed l reserve → Flow l → CodeFacts l → BlockContracts l (returnBoundary initial) →
    UnitStringStride bindings → SupportedMachine bindings initial → Stack.Valid initial reserve →
    (Stack.region initial reserve).Avoids (fun a => InProgram a ∨ InPageTables a) →
    ValidReturnAddress initial → ExecutionState initial s regions → Prepared l (l.sp initial) input s →
    input.region.Disjoint (Stack.region initial reserve) →
    (∀ region ∈ footprint l (l.sp initial), ∀ a, region.Contains a →
      ∃ outer ∈ regions, outer.Contains a) →
    ∃ t, Finished l initial s t regions input

end Sha2.Proofs.Common.SHA256.Absorb.Direct
