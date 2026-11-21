import AesGcm.Proofs.GCM.Initialization
import AesGcm.Proofs.Machine.Runtime.Contracts
import AesGcm.Spec.Program
import AesGcm.Proofs.Machine.Entry.InPlaceEncrypt.Aes256.Frame

namespace AesGcm.Proofs.Machine.Entry.InPlaceEncrypt.Aes256

open AesGcm.Spec.Program Prelude X86 X86.Machine X86Proofs.Refine

def ValidCall (initial : RamState) (key : Vector UInt8 32) (nonce : Vector UInt8 12)
    (aad bytes : ByteArray) (capacity : Nat) : Prop :=
  InPlace.ValidCapacityCall aes256gcmEncryptInPlace initial key nonce aad bytes capacity ∨
    bytes = ByteArray.empty ∧
    InPlace.ValidOverCapacityCall aes256gcmEncryptInPlace initial key nonce aad capacity

abbrev entryActivation (initial : RamState) (ret : BitVec 64) :=
  Activation.ofEntry initial aes256gcmEncryptInPlace.minStackBytes ret

open AesGcm.Spec X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift
open AesGcm.Proofs.Machine.Runtime

def initializationPost (code : CodeMap) (key : Vector UInt8 32)
    (fr : Activation) (args : Values Value Reg.count) (mem : Ram) : Prop :=
  Atom.All code args mem (LIR.Aes256gcmEncryptInPlace.frameAt .l1016a8 fr) ∧
  args[15].get 64 = fr.rcx ∧
  args[5].get 64 = memLoad fr.original (fr.rsp + 8) 64 ∧
  GcmContext.ContextIn .aes256 key (fr.rsp - 328) mem ∧
  Readable mem (fr.rsp + 8) 8 ∧
  memLoad mem (fr.rsp + 8) 64 = memLoad fr.original (fr.rsp + 8) 64 ∧
  RamWriteFrame fr.original mem [fr.region] ∧
  GPRsTyped args

def corePost (initial : RamState) (ret : BitVec 64) (bytes : ByteArray) (capacity : Nat)
    (ciphertext : ByteArray) (tag : Vector UInt8 16) (args : Values Value Reg.count) (mem : Ram) :=
  let fr := entryActivation initial ret
  Atom.All Extracted.programImage args mem (LIR.Aes256gcmEncryptInPlace.frameAt .l1016e9 fr) ∧
  GPRsTyped args ∧ (args[5].get 64).toNat = capacity ∧
  RamWriteFrame fr.original mem [fr.region, span fr.r8 bytes.size] ∧
  mem[args[4].get 64 + 15]? = some 0 ∧
  (span fr.r8 bytes.size).HasBytes mem ciphertext ∧
  (span (args[4].get 64 + 16) 16).HasBytes mem ⟨tag.toArray⟩

end AesGcm.Proofs.Machine.Entry.InPlaceEncrypt.Aes256
