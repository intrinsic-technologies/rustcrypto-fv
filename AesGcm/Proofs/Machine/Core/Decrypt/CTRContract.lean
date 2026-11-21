import AesGcm.Proofs.AES16.Layout
import AesGcm.Proofs.Machine.CTR.InitialCounter
import AesGcm.Proofs.Machine.LIR.Fn107050.Frame
import AesGcm.Proofs.Machine.LIR.Fn1084e0.Frame

namespace AesGcm.Proofs.Machine.CTR

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

def CryptCall (use256 : Bool) (code : CodeMap)
    (key : Vector UInt8 (AES16.variant use256).keyBytes) : Prop :=
  ∀ (input : ByteArray) (blockCount : Nat), input.size = 16 * blockCount →
    ∀ (schedule counter source destination : BitVec 64),
    CallContract LIR.lifted code (if use256 then .l1084e0 else .l107050)
      (if use256 then LIR.Fn1084e0.frameInfo else LIR.Fn107050.frameInfo)
      (fun _ ↦ [span (counter + 16) 4, span destination input.size])
      (fun fr mem ↦
        Readable mem fr.rdi 8 ∧ memLoad mem fr.rdi 64 = schedule ∧
        AES16.ScheduleIn (AES16.variant use256) key schedule mem ∧
        Readable mem schedule (16 * ((AES16.variant use256).Nr + 1)) ∧
        Readable mem fr.rsi 32 ∧ memLoad mem fr.rsi 64 = counter ∧
        memLoad mem (fr.rsi + 8) 64 = source ∧ memLoad mem (fr.rsi + 16) 64 = destination ∧
        (memLoad mem (fr.rsi + 24) 64).toNat = blockCount ∧
        Writable code mem counter 20 ∧ Readable mem source input.size ∧
        (span source input.size).HasBytes mem input ∧ Writable code mem destination input.size ∧
        (source = destination ∨ (span source input.size).Disjoint (span destination input.size)) ∧
        (∀ slot ∈ ([0x201208, 0x201210, 0x201230] : List (BitVec 64)),
          (span destination input.size).Disjoint (span slot 8) ∧
          (span counter 20).Disjoint (span slot 8)) ∧
        (∀ region ∈ [span fr.rdi 8, span fr.rsi 32,
          span schedule (16 * ((AES16.variant use256).Nr + 1)), span counter 20,
          span source input.size, span destination input.size],
          (callStack fr).Disjoint region) ∧
        (∀ region ∈ [span fr.rdi 8, span fr.rsi 32,
          span schedule (16 * ((AES16.variant use256).Nr + 1)), span counter 20],
          (span destination input.size).Disjoint region) ∧
        (∀ region ∈ [span fr.rdi 8, span fr.rsi 32,
          span schedule (16 * ((AES16.variant use256).Nr + 1)),
          span source input.size, span destination input.size],
          (span counter 20).Disjoint region))
      (fun fr mem ↦ memLoad mem (counter + 16) 32 =
          memLoad fr.original (counter + 16) 32 + BitVec.ofNat 32 blockCount ∧
        (span destination input.size).HasBytes mem
          (AesGcm.Spec.GCM.byteArrayOfBits
            (Standards.NIST.GCM.GCTR (AesGcm.Spec.GCM.forwardCipher (AES16.variant use256) key)
              (Standards.NIST.GCM.bitsOfBytes (initialCounterBlock fr.original counter))
              (AesGcm.Spec.GCM.bitsOfByteArray input))))

end AesGcm.Proofs.Machine.CTR
