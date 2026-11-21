import P256.Proofs.Signing.Wrapper.Hash.Call.Entry
import P256.Proofs.Signing.Wrapper.Hash.Call.Return
import P256.Proofs.Common.Machine.Divergence

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Hash.Call

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Program
open SecretKeyFromBytes.Scalar (Nat256At)
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Result [Bindings] (initial start s : RamState)
    (signature : Nat × Nat) : Prop extends Frame initial start s where
  rip : s.RIP = 0x102a3e
  first : Nat256At s (stackPtr initial - 456) signature.1
  second : Nat256At s (stackPtr initial - 424) signature.2
  status : s.regValue .rbp = 0
  savedOutput : memLoad s.external (stackPtr initial - 208) 64 = initial.regValue .rcx
  savedCapacity : memLoad s.external (stackPtr initial - 200) 64 = initial.regValue .r8

theorem run_core (core : CoreContract) [Bindings]
    {initial start s : RamState} {secret message : ByteArray}
    (pre : HashEntry initial start secret message) (state : Prepared initial start s message) :
    (∀ attempts signature,
      Ecdsa.rfc6979Within attempts (Ecdsa.secretValue secret) (Operations.hash message) .empty = some signature →
      ∃ t, Result initial start t signature) ∧
    ((∀ attempts, Ecdsa.rfc6979Within attempts (Ecdsa.secretValue secret)
      (Operations.hash message) .empty = none) →
      Prelude.Diverges (returnBoundary initial) start []) := by
  obtain ⟨entry, entered⟩ := enter_core pre state
  have proved := core entered.pre entered.input
  constructor
  · intro attempts signature found
    obtain ⟨t, result, first, second⟩ := proved.1 attempts signature found
    have frame := after_core pre entered.toFrame entered.output result
    refine ⟨t, {
      toFrame := frame
      rip := result.rip.trans entered.returnRip
      first := ?_
      second := ?_
      status := (result.calleeSaved .rbp (by simp)).trans entered.status
      savedOutput := (Finalize.Compress.work_read pre frame.stackFrame
        (offset := 208) (by decide)).trans pre.output
      savedCapacity := (Finalize.Compress.work_read pre frame.stackFrame
        (offset := 200) (by decide)).trans pre.capacity
    }⟩
    · simpa only [entered.output] using first
    · simpa only [entered.output, BitVec.sub_eq_add_neg, BitVec.add_assoc,
        BitVec.reduceNeg, BitVec.reduceAdd] using second
  · intro exhausted
    obtain ⟨fuel, run⟩ := entered.run
    exact Common.Machine.diverges_of_advances run (proved.2 exhausted)

end P256.Proofs.Signing.Wrapper.Hash.Call
