import Sha2.Proofs.Program
import X86Proofs.Program.Execution
import X86Proofs.Program.ReadWrite.WriteFrame

set_option autoImplicit false

namespace Sha2.Proofs.Common.Machine

open Sha2.Spec Sha2.Proofs.Program Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess

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

structure CalleeResult [bindings : Bindings] (s t : RamState)
    (boundary : ReturnBoundary) (outputBytes : Nat) (stackReserve : Nat := 32768)
    (resultBoundary : ReturnBoundary := X86Proofs.returnBoundary s) : Prop where
  execution : ∃ fuel, X86Proofs.Advances boundary fuel s t
  rip : t.RIP = resultBoundary.rip
  rsp : t.regValue .rsp = resultBoundary.rsp
  machine : SupportedMachine bindings t
  abi : PreservesABI s t
  frame : MemoryWriteFrame s t #v[registerRegion s .rdi outputBytes, Stack.region s stackReserve]
  loaded : ProgramLoaded t
  allocated : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome

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

end Sha2.Proofs.Common.Machine
