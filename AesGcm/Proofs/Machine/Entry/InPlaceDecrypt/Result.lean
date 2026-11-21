import AesGcm.Proofs.Machine.LIR.Aes128gcmDecryptInPlace.Frame
import AesGcm.Proofs.Machine.Runtime.Contracts

namespace AesGcm.Proofs.Machine.Entry.InPlaceDecrypt

open X86 X86.Machine X86.UserProcess X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

def resultPost (code : CodeMap) (fr : Activation) (size : Nat) (result : Option ByteArray)
    (output : Output Value Ram Reg.count) : Prop :=
  output.tag = some ⟨64, fr.ret⟩ ∧
  Atom.All code output.values output.store (LIR.Aes128gcmDecryptInPlace.frameInfo.doneAtoms fr) ∧
  match result with
  | some plaintext =>
    output.values[0] = ⟨64, 0⟩ ∧
    RamWriteFrame fr.original output.store [fr.region, span fr.r8 size] ∧
    (span fr.r8 size).HasBytes output.store plaintext
  | none =>
    output.values[0] = ⟨64, 1⟩ ∧ RamWriteFrame fr.original output.store [fr.region]

end AesGcm.Proofs.Machine.Entry.InPlaceDecrypt
