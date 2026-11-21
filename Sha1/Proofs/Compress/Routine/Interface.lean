import Sha1.Proofs.Compress.Machine.Frame
import Sha1.Proofs.Compress.Machine.Code
import Sha1.Proofs.Compress.Input
import Sha1.Proofs.Compress.Stores
import Sha1.Proofs.Common.OutputFrame
import Sha1.Proofs.Common.Refine
import X86Proofs.Step.Sse

namespace Sha1.Proofs.Compress.Routine

open Prelude X86 X86.Machine X86.UserProcess X86Proofs Sha1.Proofs.Refine
open Sha1.Spec Sha1.Spec.Program Standards.NIST

structure Context where
  initial : RamState
  H : Vector (BitVec 32) 5
  blocks : ByteArray

structure CallData (c : Context) : Prop where
  directionFlagUnset : DirectionFlagUnset c.initial
  programLoaded : ProgramLoaded c.initial
  blockCountArgumentMatchesBlocks : 64 * (c.initial.regValue .rdx).toNat = c.blocks.size
  inputInMemory : ValidInput c.initial (Compress.inputRegion c.initial c.blocks) c.blocks
  outputInMemory : Compress.ValidOutput c.initial c.H
  stackAvailable : Stack.Valid c.initial Compress.minStackBytes
  separation : MemorySeparation [Compress.inputRegion c.initial c.blocks]
    (Compress.outputRegion c.initial) (Stack.region c.initial Compress.minStackBytes)

structure Context.Valid (c : Context) (bindings : Bindings) : Prop where
  environment : MachineRamUnitStrideDecodable bindings c.initial
  machine : SupportedIntegerCPU bindings.processor c.initial
  ready : ReadyToStep c.initial
  code : CodeIn Extracted.programImage c.initial
  call : CallData c
  entry : c.initial.RIP = 0x100000 ∨ c.initial.RIP = 0x1024e0
  returnLow : (returnBoundary c.initial).rip.toNat < userAddressLimit
  outside : Machine.OutsideCompression (returnBoundary c.initial).rip

def Context.sp (c : Context) : BitVec 64 := stackPtr c.initial

def Context.stack (c : Context) : BitVec 64 := c.sp - 208

def Context.stackRegion (c : Context) : MemoryRegion := Stack.region c.initial Compress.minStackBytes

def Context.input (c : Context) (k : Nat) : BitVec 64 :=
  c.initial.regValue .rsi + BitVec.ofNat 64 (64 * k)

def Context.count (c : Context) : Nat := c.blocks.size / 64

def Context.message (c : Context) (k : Nat) : Vector (BitVec 32) 16 :=
  (SHA2.SHA256.parse (SHA2.bytesToBits c.blocks))[k]?.getD (Vector.replicate 16 0)

def Context.state (c : Context) (k : Nat) : Vector (BitVec 32) 5 :=
  ((SHA2.SHA256.parse (SHA2.bytesToBits c.blocks)).toList.take k).foldl SHA1.compress c.H

structure Frame (c : Context) (s : RamState) : Prop where
  stackPointer : stackPtr s = c.stack
  writable : Machine.MemWritable s c.stack 216
  memory : RamWriteFrame c.initial.external s.external [c.stackRegion]
  saved : ∀ i : Fin 6,
    memLoad s.external (c.stack + BitVec.ofNat 64 (160 + 8 * i.val)) 64 =
      (Operand.reg (#[3, 12, 13, 14, 15, 5][i.val]) : Operand 64).read c.initial
  output : memLoad s.external (c.stack + 128) 64 = c.initial.regValue .rdi
  inputEnd : memLoad s.external (c.stack + 136) 64 = c.input c.count
  callerReturn : memLoad s.external c.sp 64 = memLoad c.initial.external c.sp 64
  controls : fixedPart s = fixedPart c.initial
  directionFlag : DirectionFlagUnset s

def frameComponents (stack : BitVec 64) : List Component :=
  Machine.scratchComponents stack ++ [.reg 4, .mem stack 208]

structure AtBlock (c : Context) (k : Nat) (H : Vector (BitVec 32) 5) (s : RamState) : Prop where
  frame : Frame c s
  registers : Machine.LoopRegisters H s
  inputPointer : s.regValue .rsi = c.input k
  agrees : AgreesExcept (frameComponents c.stack) c.initial s

def compressionChanges (c : Context) : List Component :=
  frameComponents c.stack ++
  [.reg 0, .reg 1, .reg 2, .reg 4, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10, .reg 11,
    .flags, .rip, .mem (c.initial.regValue .rdi) 20,
    .mem (c.initial.regValue .rdi) 4,
    .mem (c.initial.regValue .rdi) 4,
    .mem (Stack.region c.initial Compress.minStackBytes).start
      (Stack.region c.initial Compress.minStackBytes).size,
    .mem (c.initial.regValue .rdi + 4) 4,
    .mem (c.initial.regValue .rdi + 8) 4,
    .mem (c.initial.regValue .rdi + 12) 4,
    .mem (c.initial.regValue .rdi + 16) 4]

def Result (c : Context) (final : RamState) : Prop :=
  CalleeSavedRegistersUnchanged c.initial final ∧
  DirectionFlagUnset final ∧
  MemoryWriteFrame c.initial final #v[Compress.outputRegion c.initial, c.stackRegion] ∧
  Compress.readOutput c.initial final = .ok (Hasher.stateBytes (c.state c.count)) ∧
  fixedPart final = fixedPart c.initial ∧
  AgreesExcept (compressionChanges c) c.initial final ∧
  final.RIP = (returnBoundary c.initial).rip ∧
  stackPtr final = (returnBoundary c.initial).rsp ∧
  (Compress.outputRegion c.initial).HasBytes final.external
    ⟨(Hasher.stateBytes (c.state c.count)).toArray⟩

def PrologueCorrect : Prop :=
  ∀ (bindings : Bindings) (c : Context), c.Valid bindings → 0 < c.count →
    ∃ n s, @Advances bindings (returnBoundary c.initial) n c.initial s ∧
      @ReadyToStep bindings s ∧ CodeIn Extracted.programImage s ∧ s.RIP = 0x102530 ∧
      AtBlock c 0 c.H s

def PrologueAdvanceCorrect : Prop :=
  ∀ (bindings : Bindings) (boundary : ReturnBoundary) (c : Context),
    c.Valid bindings → Machine.OutsideCompression boundary.rip → 0 < c.count →
    ∃ n s, @Advances bindings boundary n c.initial s ∧
      @ReadyToStep bindings s ∧ CodeIn Extracted.programImage s ∧ s.RIP = 0x102530 ∧
      AtBlock c 0 c.H s
      ∧ AgreesExcept (frameComponents c.stack) c.initial s

def NextCorrect : Prop :=
  ∀ (bindings : Bindings) (c : Context), c.Valid bindings →
    ∀ k H s, k < c.count → @ReadyToStep bindings s →
      CodeIn Extracted.programImage s → s.RIP = 0x1036a2 → AtBlock c k H s →
      ∃ n t, @Advances bindings (returnBoundary c.initial) n s t ∧
        @ReadyToStep bindings t ∧ CodeIn Extracted.programImage t ∧
        t.RIP = (if k + 1 < c.count then 0x102530 else 0x1036b4) ∧ AtBlock c (k + 1) H t
        ∧ AgreesExcept (frameComponents c.stack) c.initial t

def NextAdvanceCorrect : Prop :=
  ∀ (bindings : Bindings) (boundary : ReturnBoundary) (c : Context), c.Valid bindings →
    Machine.OutsideCompression boundary.rip →
    ∀ k H s, k < c.count → @ReadyToStep bindings s →
      CodeIn Extracted.programImage s → s.RIP = 0x1036a2 → AtBlock c k H s →
      ∃ n t, @Advances bindings boundary n s t ∧
        @ReadyToStep bindings t ∧ CodeIn Extracted.programImage t ∧
        t.RIP = (if k + 1 < c.count then 0x102530 else 0x1036b4) ∧ AtBlock c (k + 1) H t
      ∧ AgreesExcept (frameComponents c.stack) c.initial t

def FinishCorrect : Prop :=
  ∀ (bindings : Bindings) (c : Context), c.Valid bindings →
    ∀ s, @ReadyToStep bindings s → CodeIn Extracted.programImage s →
      s.RIP = 0x1036b4 → AtBlock c c.count (c.state c.count) s →
      ∃ n t, @Returns bindings (returnBoundary c.initial) n s t ∧
      @ReadyToStep bindings t ∧ Result c t

def FinishAdvanceCorrect : Prop :=
  ∀ (bindings : Bindings) (boundary : ReturnBoundary) (c : Context), c.Valid bindings →
    Machine.OutsideCompression boundary.rip →
    boundary.rip ≠ (returnBoundary c.initial).rip →
    ∀ s, @ReadyToStep bindings s → CodeIn Extracted.programImage s →
      s.RIP = 0x1036b4 → AtBlock c c.count (c.state c.count) s →
      ∃ n t, @Advances bindings boundary n s t ∧
      @ReadyToStep bindings t ∧ Result c t

end Sha1.Proofs.Compress.Routine
