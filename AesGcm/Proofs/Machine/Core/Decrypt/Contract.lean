import AesGcm.Proofs.Machine.Core.Interface
import AesGcm.Proofs.Machine.Runtime.Result
import AesGcm.Proofs.Machine.LIR.Fn1022c0.Frame
import AesGcm.Proofs.Machine.LIR.Fn102720.Frame

namespace AesGcm.Proofs.Machine.Core

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

def DecryptCall (use256 : Bool) (code : CodeMap)
    (key : Vector UInt8 (AES16.variant use256).keyBytes) (nonce : Vector UInt8 12)
    (associatedData ciphertext : ByteArray) (tag : Vector UInt8 16)
    (source destination : BitVec 64) : Prop :=
  CallResultContract LIR.lifted code (if use256 then .l102720 else .l1022c0)
      (if use256 then LIR.Fn102720.frameInfo else LIR.Fn1022c0.frameInfo)
      (fun fr ↦ [span destination ciphertext.size, span (fr.r8 + 8) 8])
      (fun fr mem ↦
        InputsIn use256 key nonce associatedData mem fr.rdi fr.rsi fr.rdx fr.rcx ∧
        BufferIn mem fr.r8 source destination ciphertext ∧ Writable code mem fr.r8 24 ∧
        Readable mem fr.r9 16 ∧ (span fr.r9 16).HasBytes mem ⟨tag.toArray⟩ ∧
        (0 < ciphertext.size → Writable code mem destination ciphertext.size) ∧
        (∀ slot ∈ ([0x201208, 0x201210, 0x201228, 0x201230] : List (BitVec 64)),
          (span destination ciphertext.size).Disjoint (span slot 8) ∧
          (span fr.r8 24).Disjoint (span slot 8)) ∧
        (∀ region ∈ [span fr.rdi (GcmContext.size (AES16.variant use256)),
          span fr.rsi 12, span fr.rdx associatedData.size, span fr.r8 24, span fr.r9 16,
          span source ciphertext.size, span destination ciphertext.size],
          (callStack fr).Disjoint region) ∧
        (∀ region ∈ [span fr.rdi (GcmContext.size (AES16.variant use256)),
          span fr.rsi 12, span fr.rdx associatedData.size, span fr.r8 24, span fr.r9 16],
          (span destination ciphertext.size).Disjoint region) ∧
        (∀ region ∈ [span fr.rdi (GcmContext.size (AES16.variant use256)),
          span fr.rsi 12, span fr.rdx associatedData.size, span fr.r9 16,
          span source ciphertext.size, span destination ciphertext.size],
          (span fr.r8 24).Disjoint region))
      (fun fr output ↦
        match AesGcm.Spec.GCM.authenticPlaintext (AES16.variant use256) key nonce
          associatedData ciphertext tag with
        | some plaintext => output.values[0].get 8 = 0 ∧
          (span destination ciphertext.size).HasBytes output.store plaintext ∧
          memLoad output.store (fr.r8 + 8) 64 = destination +
            BitVec.ofNat 64 (if 17 ≤ ciphertext.size then 16 * (ciphertext.size / 16) else 0)
        | none => output.values[0].get 8 = 1 ∧
          RamWriteFrame fr.original output.store [fr.region])

end AesGcm.Proofs.Machine.Core
