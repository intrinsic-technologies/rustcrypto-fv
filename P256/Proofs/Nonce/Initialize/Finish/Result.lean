import P256.Proofs.HMAC.Key.Output.Bytes
import P256.Proofs.Nonce.UpdateValue.Bytes
import P256.Proofs.Nonce.Initialize.Finish.Copy
import P256.Proofs.Nonce.Initialize.Finish.Frame

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)

variable [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
  {orderAddress : BitVec 64}

theorem copy_pre (pre : InitializePre initial boundary orderAddress)
    (stage : Stage initial s boundary) (rip : s.RIP = 0x107c1a)
    (output : outputPointer s = initial.regValue .rdi) : CopyPre s := by
  have source_bound (i : BitVec 64)
      (hi : i ∈ ([8, 16, 24, 32, 40, 48, 56, 64] : List (BitVec 64))) : i.toNat ≤ 64 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have output_bound (i : BitVec 64)
      (hi : i ∈ ([0, 8, 16, 24, 32, 40, 48, 56, 64] : List (BitVec 64))) : i.toNat ≤ 64 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  refine ⟨rip, ?_, ?_, ?_, ?_⟩
  · intro i hi
    change MemReadable s (stackPtr s + i) 8
    have bound := source_bound i hi
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      stack_readable pre stage (offset := i.toNat) (len := 8) (by omega) (by omega)
  · intro i hi
    have bound := output_bound i hi
    rw [output]
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      (output_writable pre stage).add i.toNat (len := 8) (by omega)
  · intro i hi offset len bound
    have ibound := output_bound i hi
    rw [output]
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      P256.Proofs.Common.Instructions.RangeApart.add_left (output_code pre bound) i.toNat (len := 8) (by omega)
  · intro i hi j hj k hk l hl eqn
    have ibound := output_bound i hi
    have jbound := source_bound j hj
    apply pre.separation (1 : Fin 3) (2 : Fin 3) (by decide)
      (outputPointer s + i + BitVec.ofNat 64 k).toNat
    · rw [output]
      apply output_contains pre (offset := i.toNat) (len := 8) (by omega)
      exact ⟨k, hk, by simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]⟩
    · rw [eqn]
      have hj : stackPtr s + j = stackPtr initial - BitVec.ofNat 64 (280 - j.toNat) := by
        simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using
          stack_address stage (offset := j.toNat) (by omega)
      change (Stack.region initial 2144).Contains ((stackPtr s + j) + BitVec.ofNat 64 l).toNat
      rw [hj]
      exact stack_sub_contains pre (offset := 280 - j.toNat) (len := 8)
        (by omega) (by omega) ⟨l, hl, rfl⟩

theorem copy_writes (pre : InitializePre initial boundary orderAddress)
    (output : outputPointer s = initial.regValue .rdi) :
    ∀ c ∈ (copyEffect s).components, ∀ a, c.Covers a →
      (registerRegion initial .rdi 72).Contains a.toNat := by
  intro c hc a ha
  simp only [copyEffect, Effect.components, List.map_cons, List.map_nil,
    Write.component_reg, Write.component_mem, Nat.reduceDiv, List.append_nil,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false, output] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  all_goals exact output_contains pre (by decide) ha

omit [Bindings] in
theorem copy_words (effect : (copyEffect s).Holds s t) :
    memLoad t.external (outputPointer s) 64 = s.regValue .r15 ∧
      ∀ i < 8, memLoad t.external (outputPointer s + BitVec.ofNat 64 (8 + 8 * i)) 64 =
        memLoad s.external (stackPtr s + BitVec.ofNat 64 (8 + 8 * i)) 64 := by
  obtain ⟨_, _, order, w0, w1, w2, w3, w4, w5, w6, w7⟩ := effect.writes
  refine ⟨?_, ?_⟩
  · change memLoad t.external (outputPointer s + 0) 64 = s.regValue .r15 at order
    exact (congrArg (fun a => memLoad t.external a 64) (BitVec.add_zero (outputPointer s))).symm.trans order
  · intro i hi
    have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact w0
    · exact w1
    · exact w2
    · exact w3
    · exact w4
    · exact w5
    · exact w6
    · exact w7

theorem copy_result (pre : InitializePre initial boundary orderAddress)
    (stage : Stage initial s boundary) (ready : ReadyToStep t) {fuel : Nat}
    (run : Advances boundary fuel s t) (effect : (copyEffect s).Holds s t)
    (order : s.regValue .r15 = orderAddress)
    (output : outputPointer s = initial.regValue .rdi) {state : Nonce.State}
    (drbg : DrbgAt s (stackPtr s + 8) state) :
    Stage initial t boundary ∧ GeneratorAt t (initial.regValue .rdi) orderAddress state := by
  have stage' := stage_of_output_agrees pre stage run ready effect.agrees (copy_writes pre output)
    (by simp [copyEffect, Effect.components])
  have words := copy_words effect
  refine ⟨stage', ?_, ?_, ?_⟩
  · simpa only [output] using words.1.trans order
  · refine ⟨pre.order.1, ?_⟩
    intro i hi
    apply Eq.trans (stage'.frame _ ?_) (pre.order.2 i hi)
    intro region hr ha
    have member : region = registerRegion initial .rdi 72 ∨ region = Stack.region initial 2144 := by
      simpa using hr
    have contains := memoryRegion_contains_add pre.orderBounded (Nat.le_refl _) (Nat.le_refl _) hi
    rcases member with rfl | rfl
    · exact pre.orderOutput _ contains ha
    · exact pre.orderStack _ contains ha
  · apply drbg.copy
    apply HMAC.Key.Output.bytes_of_words (count := 8) (stack_readable pre stage (offset := 8) (len := 64) (by decide) (by decide))
      ((output_writable pre stage').add 8 (len := 64) (by decide)).toMemReadable
    intro i hi
    simpa only [output, BitVec.add_assoc, ← BitVec.ofNat_add] using words.2 i hi

end P256.Proofs.Nonce.Initialize.Finish
