import P256.Proofs.Projective.Preserve
import P256.Proofs.Projective.Multiply.Operations
import P256.Proofs.Program.Stack

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Table

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

def cursorRegion (cursor : BitVec 64) : MemoryRegion := ⟨cursor.toNat, 8⟩

def pointRegion (point : BitVec 64) : MemoryRegion := ⟨point.toNat, 96⟩

structure TablePre [Bindings] (s : RamState) (boundary : ReturnBoundary)
    (cursor point : BitVec 64) : Prop extends CalleePre s boundary 0x10aff0 8 768 2120 where
  cursorPointer : memLoad s.external (s.regValue .rsi) 64 = cursor
  pointPointer : memLoad s.external cursor 64 = point
  cursorBounded : (cursorRegion cursor).Bounded
  cursorAllocated : (cursorRegion cursor).Allocated s.external
  cursorAvoids : (cursorRegion cursor).Avoids (fun a => InProgram a ∨ InPageTables a)
  cursorApart : ∀ region ∈ [registerRegion s .rsi 8, pointRegion point,
    registerRegion s .rdi 768, Stack.region s 2120], (cursorRegion cursor).Disjoint region
  pointBounded : (pointRegion point).Bounded
  pointAllocated : (pointRegion point).Allocated s.external
  pointOutput : (pointRegion point).Disjoint (registerRegion s .rdi 768)
  pointStack : (pointRegion point).Disjoint (Stack.region s 2120)

structure TableResult [Bindings] (s t : RamState) (boundary : ReturnBoundary)
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
    #v[registerRegion s .rdi 768, cursorRegion cursor, Stack.region s 2120]
  loaded : ProgramLoaded t
  allocated : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome
  cursorValue : memLoad t.external cursor 64 = point + 128
  outputPointer : t.regValue .rax = s.regValue .rdi

def TableAt (s : RamState) (address : BitVec 64) (values : Fin 8 → Projective) : Prop :=
  ∀ i, ProjectiveAt s (address + BitVec.ofNat 64 (96 * i.val)) (values i)

theorem TableAt.of_copy {s t : RamState} {source destination : BitVec 64}
    {values : Fin 8 → Projective} (h : TableAt s source values)
    (bytes : ∀ i < 768, t.external[destination + BitVec.ofNat 64 i]? =
      s.external[source + BitVec.ofNat 64 i]?) : TableAt t destination values := by
  intro slot
  apply (h slot).of_bytes_eq
  intro i hi
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, bytes _ (by have := slot.isLt; omega)]
  rw [BitVec.ofNat_add, ← BitVec.add_assoc]


def oddTableEntry (point : Projective) : Nat → Projective
  | 0 => point
  | i + 1 => (oddTableEntry point i).add point.double

def oddTable (point : Projective) (i : Fin 8) : Projective := oddTableEntry point i.val

def Correct : Prop :=
  ∀ [Bindings] (s : RamState) (boundary : ReturnBoundary)
    (cursor point : BitVec 64) (value : Projective),
    TablePre s boundary cursor point → ProjectiveAt s point value →
      ∃ t, TableResult s t boundary cursor point ∧
        TableAt t (s.regValue .rdi) (oddTable value)

end P256.Proofs.Verifying.Combination.Table
