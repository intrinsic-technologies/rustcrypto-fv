import X86Proofs.Instructions.Movs.RepStep
import X86Proofs.Instructions.Movs.RepTriple

namespace Sha1.Proofs.MemoryRoutines.Stos

open X86 X86.Machine X86.UserProcess X86Proofs

inductive Kind where
  | byte
  | qword

def Kind.bytes : Kind → Nat
  | .byte => 1
  | .qword => 8

def Kind.code : Kind → List UInt8
  | .byte => [0xf3, 0xaa]
  | .qword => [0xf3, 0x48, 0xab]

def stosSpec (n : Nat) (s : RamState) : RamState :=
  rdi.write ((Operand.mem (rdi.read s) : Operand n).write (dataAccess s "store")
    ((Operand.reg 0 : Operand n).read s)) (rdi.read s + BitVec.ofNat 64 (n / 8))

def repStosAfter (kind : Kind) (s : RamState) : RamState :=
  afterStep s kind.code.length fun t ↦
    repCount (stosSpec (8 * kind.bytes)
      { t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 kind.code.length) })

def repStosZeroAfter (kind : Kind) (s : RamState) : RamState :=
  afterStep s kind.code.length fun t ↦
    { t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 kind.code.length), Repeat_String_Operation := false }

end Sha1.Proofs.MemoryRoutines.Stos
