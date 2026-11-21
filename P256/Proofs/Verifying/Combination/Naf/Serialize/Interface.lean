import P256.Proofs.Verifying.Combination.Naf.Interface
import P256.Proofs.Program.Interface
import P256.Proofs.SecretKeyFromBytes.Scalar.Representation

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Serialize

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines

def cursorRegion (cursor : BitVec 64) : MemoryRegion := ⟨cursor.toNat, 8⟩

def pairRegion (point : BitVec 64) : MemoryRegion := ⟨point.toNat, 128⟩

structure ScalarPre [Bindings] (s : RamState) (boundary : ReturnBoundary)
    (cursor point : BitVec 64) : Prop extends CalleePre s boundary 0x10b170 8 272 536 where
  cursorPointer : memLoad s.external (s.regValue .rsi) 64 = cursor
  pointPointer : memLoad s.external cursor 64 = point
  cursorBounded : (cursorRegion cursor).Bounded
  cursorAllocated : (cursorRegion cursor).Allocated s.external
  cursorAvoids : (cursorRegion cursor).Avoids (fun a => InProgram a ∨ InPageTables a)
  cursorApart : ∀ region ∈ [registerRegion s .rsi 8, pairRegion point,
    registerRegion s .rdi 272, Stack.region s 536], (cursorRegion cursor).Disjoint region
  pointBounded : (pairRegion point).Bounded
  pointAllocated : (pairRegion point).Allocated s.external
  pointOutput : (pairRegion point).Disjoint (registerRegion s .rdi 272)
  pointStack : (pairRegion point).Disjoint (Stack.region s 536)

structure ScalarResult [Bindings] (s t : RamState) (boundary : ReturnBoundary)
    (cursor point : BitVec 64) : Prop where
  execution : ∃ fuel, Advances boundary fuel s t
  rip : t.RIP = (returnBoundary s).rip
  rsp : t.regValue .rsp = (returnBoundary s).rsp
  bindingsSupported : MachineRamUnitStrideDecodable inferInstance t
  machine : SupportedIntegerMachineState (inferInstance : Bindings).processor t
  calleeSaved : CalleeSavedRegistersUnchanged s t
  directionFlag : DirectionFlagUnset t
  mxcsr : t.MXCSR = s.MXCSR
  fp87 : t.FP87_Control = s.FP87_Control
  frame : MemoryWriteFrame s t
    #v[registerRegion s .rdi 272, cursorRegion cursor, Stack.region s 536]
  loaded : ProgramLoaded t
  allocated : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome
  cursorValue : memLoad t.external cursor 64 = point + 128
  outputPointer : t.regValue .rax = s.regValue .rdi

def ScalarCorrect : Prop :=
  ∀ [Bindings] (s : RamState) (boundary : ReturnBoundary)
    (cursor point : BitVec 64) (n : Nat),
    ScalarPre s boundary cursor point → Nat256At s (point + 96) n →
      ∃ t, ScalarResult s t boundary cursor point ∧ NafAt t (s.regValue .rdi) n

end P256.Proofs.Verifying.Combination.Naf.Serialize
