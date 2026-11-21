import AesGcm.Proofs.Machine.Entry.InPlaceEncrypt.Call
import AesGcm.Proofs.Machine.Runtime.Contracts

namespace AesGcm.Proofs.Machine.Entry.InPlaceEncrypt

open AesGcm.Spec AesGcm.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

def corePost (initial : RamState) (ret : BitVec 64) (bytes : ByteArray) (capacity : Nat)
    (ciphertext : ByteArray) (tag : Vector UInt8 16) (args : Values Value Reg.count) (mem : Ram) :=
  let fr := entryActivation initial ret
  Atom.All Extracted.programImage args mem (LIR.Aes128gcmEncryptInPlace.frameAt .l101409 fr) ∧
  GPRsTyped args ∧ (args[5].get 64).toNat = capacity ∧
  RamWriteFrame fr.original mem [fr.region, span fr.r8 bytes.size] ∧
  mem[args[4].get 64 + 15]? = some 0 ∧
  (span fr.r8 bytes.size).HasBytes mem ciphertext ∧
  (span (args[4].get 64 + 16) 16).HasBytes mem ⟨tag.toArray⟩

end AesGcm.Proofs.Machine.Entry.InPlaceEncrypt
