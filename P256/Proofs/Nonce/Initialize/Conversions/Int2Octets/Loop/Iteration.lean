import P256.Proofs.Nonce.Initialize.Conversions.Int2Octets.Loop.PrepareStage
import P256.Proofs.Nonce.Initialize.Conversions.Int2Octets.Loop.Words
import P256.Proofs.Nonce.Initialize.Conversions.Int2Octets.Loop.Next

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Conversions.Int2Octets.Loop

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Field P256.Proofs.SecretKeyFromBytes.Scalar P256.Proofs.Common.Instructions
open P256.Proofs.Projective.Multiply.Machine.Radix.Serialize (canonicalLimb)

theorem iteration [Bindings] {initial s : RamState} {boundary : ReturnBoundary} {value i : Nat}
    (pre : Pre initial boundary) (stage : Stage initial s boundary)
    (integer : Nat256At initial (initial.regValue .rdi) value)
    (registers : LoopRegisters initial s i) (words : Words initial s value i)
    (hi : i < 4) (rip : s.RIP = 0x107050) :
    ∃ t, Stage initial t boundary ∧ LoopRegisters initial t (i+1) ∧ Words initial t value (i+1) ∧
      t.RIP = (if i+1 < 4 then 0x107050 else 0x107093) := by
  obtain ⟨u,stageU,effect,kept⟩ := prepare_stage pre stage registers hi rip
  have writes := effect.writes
  change u.regValue .rax = _ ∧
    u.regValue .rbx = BitVec.ofNat 64 (24-8*i) ∧
    u.regValue .rdi = BitVec.ofNat 64 (24-8*i) + s.regValue .r14 ∧
    u.regValue .rdx = 8 ∧ u.regValue .rcx = 0 ∧
    memLoad u.external (rspOf s+16) 64 = _ ∧
    u.regValue .rsi = rspOf s+16 ∧ u.regValue .rbp = BitVec.ofNat 64 (i+1) at writes
  have stackAddress : rspOf s+16 = stackPtr initial-56 := by
    change stackPtr s+16 = _
    rw [stage.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have source : u.regValue .rsi = stackPtr initial-56 := writes.2.2.2.2.2.2.1.trans stackAddress
  have destination : u.regValue .rdi = initial.regValue .rdx + BitVec.ofNat 64 (24-8*i) := by
    rw [writes.2.2.1, registers.output, BitVec.add_comm]
  obtain ⟨v,stageV,ripV,agreesV,copied⟩ := copy pre stageU (by omega) effect.rip
    source destination writes.2.2.2.1
  have indexV : v.regValue .rbp = BitVec.ofNat 64 (i+1) :=
    (agreesV.read (n := 64) (r := 5) (by simp [copyFrame])).trans writes.2.2.2.2.2.2.2
  have countV : v.regValue .r15 = 4 :=
    (agreesV.read (n := 64) (r := 15) (by simp [copyFrame])).trans
      ((effect.agrees.read (n := 64) (r := 15)
        (by simp [prepareEffect, Effect.components, Write.component, Operand.component])).trans registers.count)
  obtain ⟨t,stageT,ripT,lengthT,agreesT⟩ := next pre stageV indexV countV (by omega) ripV
  have sameOutput : ∀ j < i,
      memLoad u.external (initial.regValue .rdx + BitVec.ofNat 64 (24-8*j)) 64 =
      memLoad s.external (initial.regValue .rdx + BitVec.ofNat 64 (24-8*j)) 64 := by
    intro j hj
    apply memLoad_congr
    intro k hk
    exact congrArg (fun o : Option UInt8 => o.getD 0)
      (kept _ (output_contains pre (by omega) ⟨k,hk,rfl⟩))
  have wordsV : Words initial v value (i+1) := by
    intro j hj
    by_cases old : j < i
    · rw [copy_keeps_word pre agreesV (by omega) (by omega), sameOutput j old]
      exact words j old
    · have eqn : j = i := by omega
      subst j
      have copiedWord : memLoad v.external (initial.regValue .rdx + BitVec.ofNat 64 (24-8*i)) 64 =
          memLoad u.external (stackPtr initial-56) 64 := by
        apply memLoad_congr
        intro k hk
        exact congrArg (fun o : Option UInt8 => o.getD 0) (copied k hk)
      rw [copiedWord, ← stackAddress, writes.2.2.2.2.2.1, input_address registers hi]
      rw [(stage.input_integer pre integer).memLoad_limb i hi]
      rfl
  have memoryT := agreesT.external (by simp [Component.Covers])
  have allAgrees := (effect.agrees.trans agreesV).trans agreesT
  have keepInput : t.regValue .r13 = s.regValue .r13 := allAgrees.read (n := 64) (r := 13)
    (by simp [prepareEffect, copyFrame, Effect.components, Write.component, Operand.component])
  have keepOutput : t.regValue .r14 = s.regValue .r14 := allAgrees.read (n := 64) (r := 14)
    (by simp [prepareEffect, copyFrame, Effect.components, Write.component, Operand.component])
  have keepZero : t.regValue .r12 = s.regValue .r12 := allAgrees.read (n := 64) (r := 12)
    (by simp [prepareEffect, copyFrame, Effect.components, Write.component, Operand.component])
  have remainingV : v.regValue .rbx = BitVec.ofNat 64 (32-8*(i+1)) := by
    have eqn : v.regValue .rbx = BitVec.ofNat 64 (24-8*i) :=
      (agreesV.read (n := 64) (r := 3) (by simp [copyFrame])).trans writes.2.1
    exact eqn.trans (congrArg (BitVec.ofNat 64) (by omega))
  refine ⟨t,stageT,⟨keepInput.trans registers.input,keepOutput.trans registers.output,
    keepZero.trans registers.zero,?_,?_,?_,lengthT.trans remainingV⟩,?_,ripT⟩
  · exact (agreesT.read (n := 64) (r := 15) (by simp)).trans countV
  · exact (agreesT.read (n := 64) (r := 5) (by simp)).trans indexV
  · exact (agreesT.read (n := 64) (r := 3) (by simp)).trans remainingV
  · intro j hj
    rw [memoryT]
    exact wordsV j hj

end P256.Proofs.Nonce.Initialize.Conversions.Int2Octets.Loop
