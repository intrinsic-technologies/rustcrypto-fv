import Md5.Proofs.Buffered.FinalizeReset.Contracts
import Md5.Proofs.Buffered.Update.Calls
import Md5.Proofs.Buffered.Finalize.Algebra

namespace Md5.Proofs.Buffered.FinalizeReset.Prepare

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

def position (s : RamState) : BitVec 64 := ((.reg 0 : Operand 8).read s).setWidth 64

def copyEffect (s : RamState) (variant : Variant := .saved) : Effect :=
  { rip := (variant.address 0x1007c6)
    writes := [⟨(.reg 15 : Operand 64), position s⟩,
      ⟨(.reg 0 : Operand 64), (.mem (stackPtr s + 0x48) : Operand 64).read s⟩,
      ⟨(.reg 1 : Operand 64), (.mem (stackPtr s + 0x50) : Operand 64).read s⟩,
      ⟨(.mem (stackPtr s + 0xf0) : Operand 64),
        (.mem (stackPtr s + 0x50) : Operand 64).read s⟩,
      ⟨(.mem (stackPtr s + 0xe8) : Operand 64),
        (.mem (stackPtr s + 0x48) : Operand 64).read s⟩] }

def setupEffect (s : RamState) (variant : Variant := .saved) : Effect :=
  let pos := (.reg 15 : Operand 64).read s
  { rip := (variant.address 0x1007e0)
    writes := [⟨(.reg 3 : Operand 64), pos ^^^ 63⟩,
      ⟨(.mem (stackPtr s + pos + 8) : Operand 8), 128⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + pos + 9⟩,
      ⟨(.reg 6 : Operand 64), 0⟩,
      ⟨(.reg 2 : Operand 64), pos ^^^ 63⟩]
    flags := some ⟨none, none, none, none, none, none⟩ }

abbrev firstBlock := Finalize.firstBlock

def prepareChanges (s : RamState) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 3, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10,
    .reg 11, .reg 15, .flags, .rip,
    .mem (stackPtr s - 8) 8, .mem (context s) 64, .mem (stackPtr s + 0xe8) 16]

structure Result [Bindings] (boundary : ReturnBoundary) (message : ByteArray)
    (s t : RamState) (variant : Variant := .saved) : Prop where
  advances : ∃ fuel, Advances boundary fuel s t
  ready : ReadyToStep t
  code : CodeIn Extracted.programImage t
  rip : t.RIP = (variant.address 0x1007e6)
  storage : Storage t variant
  rsp : stackPtr t = stackPtr s
  position : (.reg 15 : Operand 64).read t = BitVec.ofNat 64 (message.size % 64)
  remaining : (.reg 3 : Operand 64).read t = BitVec.ofNat 64 (63 - message.size % 64)
  copied : (⟨(stackPtr s + 0xe8).toNat, 16⟩ : MemoryRegion).HasBytes t.external
    ⟨(absorbedBuffer message).toBytes.toArray⟩
  padded : (⟨(context s).toNat, 64⟩ : MemoryRegion).HasBytes t.external (firstBlock message)
  output : outputAddress t = outputAddress s
  agrees : AgreesExcept (prepareChanges s) s t

end Md5.Proofs.Buffered.FinalizeReset.Prepare
