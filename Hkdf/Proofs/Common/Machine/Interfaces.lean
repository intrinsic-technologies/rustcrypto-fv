import Hkdf.Proofs.Program
import X86Proofs.Program.Execution
import X86Proofs.Program.ReadWrite.WriteFrame

set_option autoImplicit false

namespace Hkdf.Proofs.Common.Machine

open Hkdf.Spec Hkdf.Proofs.Program Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess

structure CalleePre [bindings : Bindings] (s : RamState) (boundary : ReturnBoundary)
    (entry : BitVec 64) (inputBytes outputBytes : Nat) (stackReserve : Nat := 32768) : Prop where
  stride : UnitStringStride bindings
  machine : SupportedMachine bindings s
  directionFlag : Prelude.RFLAGS.DirectionFlagClear s.RFLAGS
  loaded : ProgramLoaded s
  rip : s.RIP = entry
  inputBounded : (registerRegion s .rsi inputBytes).Bounded
  inputAllocated : (registerRegion s .rsi inputBytes).Allocated s.external
  outputBounded : (registerRegion s .rdi outputBytes).Bounded
  outputAllocated : (registerRegion s .rdi outputBytes).Allocated s.external
  stack : Stack.Valid s stackReserve
  separation : MemoryRegion.PairwiseDisjoint
    #v[registerRegion s .rsi inputBytes, registerRegion s .rdi outputBytes, Stack.region s stackReserve]
  avoids : ∀ region ∈ [registerRegion s .rdi outputBytes, Stack.region s stackReserve],
    region.Avoids (fun a => InProgram a ∨ InPageTables a)
  outerBoundary : ¬ InProgram boundary.rip
  returnInProgram : InProgram (X86Proofs.returnBoundary s).rip

structure CalleeResult [bindings : Bindings] (s t : RamState)
    (boundary : ReturnBoundary) (outputBytes : Nat) (stackReserve : Nat := 32768) : Prop where
  execution : ∃ fuel, X86Proofs.Advances boundary fuel s t
  rip : t.RIP = (X86Proofs.returnBoundary s).rip
  rsp : t.regValue .rsp = (X86Proofs.returnBoundary s).rsp
  machine : SupportedMachine bindings t
  abi : PreservesABI s t
  frame : MemoryWriteFrame s t #v[registerRegion s .rdi outputBytes, Stack.region s stackReserve]
  loaded : ProgramLoaded t
  allocated : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome

structure CallPre [bindings : Bindings] (s : RamState) (boundary : ReturnBoundary)
    (entry : BitVec 64) {readCount writeCount : Nat}
    (reads : Vector MemoryRegion readCount) (writes : Vector MemoryRegion writeCount)
    (stackReserve : Nat := 32768) : Prop where
  stride : UnitStringStride bindings
  machine : SupportedMachine bindings s
  directionFlag : Prelude.RFLAGS.DirectionFlagClear s.RFLAGS
  loaded : ProgramLoaded s
  rip : s.RIP = entry
  readsBounded : ∀ region ∈ reads, region.Bounded
  readsAllocated : ∀ region ∈ reads, region.Allocated s.external
  writesBounded : ∀ region ∈ writes, region.Bounded
  writesAllocated : ∀ region ∈ writes, region.Allocated s.external
  stack : Stack.Valid s stackReserve
  writesDisjoint : MemoryRegion.PairwiseDisjoint writes
  writesStackDisjoint : ∀ i : Fin writeCount,
    writes[i].Disjoint (Stack.region s stackReserve)
  writesAvoid : ∀ region ∈ writes, region.Avoids (fun a => InProgram a ∨ InPageTables a)
  stackAvoid : (Stack.region s stackReserve).Avoids (fun a => InProgram a ∨ InPageTables a)
  outerBoundary : ¬ InProgram boundary.rip
  returnInProgram : InProgram (X86Proofs.returnBoundary s).rip

structure CallResult [bindings : Bindings] (s t : RamState)
    (boundary : ReturnBoundary) {writeCount : Nat}
    (writes : Vector MemoryRegion writeCount) (stackReserve : Nat := 32768) : Prop where
  execution : ∃ fuel, X86Proofs.Advances boundary fuel s t
  rip : t.RIP = (X86Proofs.returnBoundary s).rip
  rsp : t.regValue .rsp = (X86Proofs.returnBoundary s).rsp
  machine : SupportedMachine bindings t
  abi : PreservesABI s t
  frame : MemoryWriteFrame s t writes
  stackFrame : MemoryWriteFrame s t #v[Stack.region s stackReserve]
  loaded : ProgramLoaded t
  allocated : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome

theorem CalleePre.toCallPre [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {entry : BitVec 64} {inputBytes outputBytes stackReserve : Nat}
    (pre : CalleePre s boundary entry inputBytes outputBytes stackReserve) :
    CallPre s boundary entry #v[registerRegion s .rsi inputBytes]
      #v[registerRegion s .rdi outputBytes] stackReserve := by
  refine {
    stride := pre.stride
    machine := pre.machine
    directionFlag := pre.directionFlag
    loaded := pre.loaded
    rip := pre.rip
    readsBounded := ?_
    readsAllocated := ?_
    writesBounded := ?_
    writesAllocated := ?_
    stack := pre.stack
    writesDisjoint := by simp [MemoryRegion.PairwiseDisjoint]
    writesStackDisjoint := ?_
    writesAvoid := ?_
    stackAvoid := pre.avoids _ (by simp)
    outerBoundary := pre.outerBoundary
    returnInProgram := pre.returnInProgram }
  · intro region h
    rcases (Vector.mem_singleton.mp h) with rfl
    exact pre.inputBounded
  · intro region h
    rcases (Vector.mem_singleton.mp h) with rfl
    exact pre.inputAllocated
  · intro region h
    rcases (Vector.mem_singleton.mp h) with rfl
    exact pre.outputBounded
  · intro region h
    rcases (Vector.mem_singleton.mp h) with rfl
    exact pre.outputAllocated
  · intro i
    cases i with
    | mk value bound =>
      have hv : value = 0 := by omega
      subst value
      have hb : bound = (by decide) := Subsingleton.elim _ _
      subst bound
      change (registerRegion s .rdi outputBytes).Disjoint (Stack.region s stackReserve)
      exact pre.separation ⟨1, by decide⟩ ⟨2, by decide⟩ (by decide)
  · intro region h
    rcases (Vector.mem_singleton.mp h) with rfl
    exact pre.avoids _ (by simp)

theorem preserve_region_over_call {s t : RamState} {caller callee : MemoryRegion}
    {bytes : ByteArray} (bounded : caller.Bounded) (disjoint : caller.Disjoint callee)
    (frame : MemoryWriteFrame s t #v[callee])
    (contents : caller.HasBytes s.external bytes) :
    caller.HasBytes t.external bytes := by
  refine ⟨contents.1, ?_⟩
  intro i
  have hsize := contents.1
  change bytes.size = caller.size at hsize
  have hi : i.val < caller.size := by omega
  have haddr : caller.start + i.val < 2^64 := by
    change caller.start + caller.size < 2^32 at bounded
    have hsum : caller.start + i.val < 2^32 := by omega
    omega
  have outside : ¬ callee.Contains (caller.start + i.val) := by
    intro inside
    exact disjoint (caller.start + i.val) ⟨by simp, by omega⟩ inside
  have hf := frame (BitVec.ofNat 64 (caller.start + i.val)) (by
    intro region hregion hcontains
    rcases Vector.mem_singleton.mp hregion with rfl
    apply outside
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt haddr] using hcontains)
  exact hf.trans (contents.2 i)

theorem frames_of_not_reserved {addr : BitVec 64} {len : Nat} (hpos : 0 < len)
    (hlow : addr.toNat + len ≤ 2^32)
    (havoid : ∀ i < len, ¬ X86Proofs.PageTableReserved (addr + BitVec.ofNat 64 i)) :
    addr.toNat + len ≤ 0x1000 ∨ 0x3000 ≤ addr.toNat := by
  have byte : ∀ i < len, ¬ (0x1000 ≤ addr.toNat + i ∧ addr.toNat + i < 0x3000) := fun i hi => by
    have h := havoid i hi
    unfold X86Proofs.PageTableReserved at h
    rwa [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i < 2^64 by omega),
      Nat.mod_eq_of_lt (show addr.toNat + i < 2^64 by omega)] at h
  have h₀ := byte 0 hpos
  have h₁ := byte (0x1000 - addr.toNat)
  omega

end Hkdf.Proofs.Common.Machine
