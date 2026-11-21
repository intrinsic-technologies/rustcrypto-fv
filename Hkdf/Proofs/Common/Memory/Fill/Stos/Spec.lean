import X86Proofs.Instructions.Movs.RepTriple

namespace Hkdf.Proofs.Common.Memory.Fill.Stos

open X86Proofs X86 X86.Machine X86.UserProcess

def stosSpec (bytes : Nat) (t : RamState) : RamState :=
  let dst : Operand (8 * bytes) := .mem (rdi.read t)
  let src : Operand (8 * bytes) := .reg 0
  let u := dst.write (dataAccess t "store") (src.read t)
  rdi.write u (rdi.read t + BitVec.ofNat 64 bytes)

def repStosAfter (bytes len : Nat) (s : RamState) : RamState :=
  afterStep s len fun t =>
    repCount (stosSpec bytes { t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 len) })

def repStosZeroAfter (len : Nat) (s : RamState) : RamState :=
  afterStep s len fun t =>
    { t with Next_IP := BitVec.add s.RIP (BitVec.ofNat 64 len), Repeat_String_Operation := false }

end Hkdf.Proofs.Common.Memory.Fill.Stos
