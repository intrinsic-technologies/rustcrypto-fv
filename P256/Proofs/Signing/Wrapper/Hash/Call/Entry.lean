import P256.Proofs.Signing.Wrapper.Hash.Call.Prepare
import P256.Proofs.Signing.Wrapper.Hash.Call.Pre
import P256.Proofs.Program.ScalarFrame.Call
import P256.Proofs.Program.Frame

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Hash.Call

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Program ScalarFrame
open SecretKeyFromBytes.Scalar (Nat256At)
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure CoreEntry [Bindings] (initial start entry : RamState)
    (secret : Nat) (message : ByteArray) : Prop extends Frame initial start entry 528 where
  pre : SignPre entry (returnBoundary initial)
  input : SignInput entry secret (Operations.hash message)
  output : entry.regValue .rdi = stackPtr initial - 456
  returnRip : (returnBoundary entry).rip = 0x102a3e
  status : entry.regValue .rbp = 0
  savedOutput : memLoad entry.external (stackPtr initial - 208) 64 = initial.regValue .rcx
  savedCapacity : memLoad entry.external (stackPtr initial - 200) 64 = initial.regValue .r8

theorem enter_core [Bindings] {initial start s : RamState} {secret message : ByteArray}
    (pre : HashEntry initial start secret message)
    (state : Prepared initial start s message) :
    ∃ entry, CoreEntry initial start entry (Ecdsa.secretValue secret) message := by
  obtain ⟨entry, _, frame, effect⟩ := state.toFrame.call_rel32 pre.context
    0x2a39 0x9f82 state.rip (by decide) (by decide +kernel)
    (inProgram_of_textOffset 0xc9c0 (by decide))
  have ret : (returnBoundary entry).rip = 0x102a3e := (callEffect_stack effect).1
  have key : entry.regValue .rsi = stackPtr initial - 152 :=
    (effect.agrees.read (n := 64) (r := 6) (by simp)).trans state.input
  have output : entry.regValue .rdi = stackPtr initial - 456 :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans state.output
  have digest : entry.regValue .rdx = stackPtr initial - 520 :=
    (effect.agrees.read (n := 64) (r := 2) (by simp)).trans state.digestPointer
  have entryPre := core_pre pre frame effect.rip key output digest
    ((effect.agrees.read (n := 64) (r := 1) (by simp)).trans state.digestLength)
    ((effect.agrees.read (n := 64) (r := 8) (by simp)).trans state.entropyPointer)
    ((effect.agrees.read (n := 64) (r := 9) (by simp)).trans state.entropyLength)
    (by rw [ret]; exact inProgram_of_textOffset 0x2a3e (by decide))
  have coreInput : SignInput entry (Ecdsa.secretValue secret) (Operations.hash message) := by
    refine ⟨?_, ?_, pre.input.positive, pre.input.canonical⟩
    · rw [key]
      refine ⟨pre.input.scalar.1, fun i hi => ?_⟩
      rw [frame.stackFrame _]
      · exact pre.input.scalar.2 i hi
      · intro region hr hin
        have eq : region = Hash.workRegion initial := by simpa using hr
        subst region
        have bounds := stack_bounds (stack pre.context)
        have low := stack_sub_toNat (stack pre.context) (offset := 152) (by decide)
        change (stackPtr initial).toNat - 5112 ≤
          (stackPtr initial - 152#64 + BitVec.ofNat 64 i).toNat ∧
          (stackPtr initial - 152#64 + BitVec.ofNat 64 i).toNat <
          (stackPtr initial).toNat - 5112 + (5112 - 240) at hin
        rw [toNat_add_ofNat _ _ (by rw [low]; omega), low] at hin
        omega
    · change (MemoryRegion.mk (entry.regValue .rdx).toNat 32).HasBytes _ _
      rw [digest]
      refine ⟨state.digest.1, ?_⟩
      intro i
      have hi : i.val < 32 := by have size := state.digest.1; change _ = 32 at size; omega
      have bytes := ScalarFrame.call_byte (frameOffset := 520) (by decide) state.rsp effect
        (offset := 520) (len := 32) (by decide) (by decide) hi
      have h := state.digest.2 i
      change entry.external[BitVec.ofNat 64 ((stackPtr initial - 520).toNat + i.val)]? = _
      change s.external[BitVec.ofNat 64 ((stackPtr initial - 520).toNat + i.val)]? = _ at h
      simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at h ⊢
      exact bytes.trans h
  exact ⟨entry, frame, entryPre, coreInput, output, ret,
    (effect.agrees.read (n := 64) (r := 5) (by simp)).trans state.status,
    (Finalize.Compress.work_read pre frame.stackFrame (offset := 208) (by decide)).trans pre.output,
    (Finalize.Compress.work_read pre frame.stackFrame (offset := 200) (by decide)).trans pre.capacity⟩

end P256.Proofs.Signing.Wrapper.Hash.Call
