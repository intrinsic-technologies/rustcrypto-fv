import P256.Proofs.Program.Code
import P256.Proofs.Program.Memory
import P256.Proofs.Common.Instructions.CrossPageStore

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Copy

open P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

structure CopyPre (input : ByteArray) (s : RamState)
    (sourceRegister : Syntax.Reg := .rcx) (entry : BitVec 64 := 0x10683d) : Prop where
  rip : s.RIP = entry
  sourceBounded : (registerRegion s sourceRegister 32).Bounded
  sourceBytes : (registerRegion s sourceRegister 32).HasBytes s.external input
  writable : CrossPageStore.Writable s (stackPtr s + 112) 32
  apart : RangeApart (stackPtr s + 112) 32 (s.regValue sourceRegister) 32
  avoids : (MemoryRegion.mk (stackPtr s + 112).toNat 32).Avoids
    (fun a => InProgram a ∨ InPageTables a)

def copyComponents (s : RamState) : List Component :=
  [.reg 0, .reg 1, .reg 2, .rip, .mem (stackPtr s + 112) 32]

structure CopyResult [Bindings] (boundary : ReturnBoundary) (input : ByteArray)
    (s t : RamState) (exit : BitVec 64 := 0x10687d) : Prop where
  execution : ∃ fuel, Advances boundary fuel s t
  ready : ReadyToStep t
  loaded : ProgramLoaded t
  rip : t.RIP = exit
  rsp : stackPtr t = stackPtr s
  agrees : AgreesExcept (copyComponents s) s t
  bytes : (MemoryRegion.mk (stackPtr s + 112).toNat 32).HasBytes t.external input
  allocated : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome

end P256.Proofs.EcdhWrapper.Copy
