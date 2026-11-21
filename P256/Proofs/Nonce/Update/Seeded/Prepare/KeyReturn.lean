import P256.Proofs.Nonce.Update.Seeded.Prepare.KeyCall
import P256.Proofs.Nonce.Update.Seeded.Prepare.Memory
import P256.Proofs.HMAC.Key.Output.Bytes
import P256.Proofs.HMAC.Mathematics

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Seeded.Prepare

open P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

variable [Bindings] {initial s t : RamState} {boundary : ReturnBoundary} {original state : State}

set_option maxHeartbeats 800000 in
theorem key_return (pre : DrbgCalleePre initial boundary 0x109f30 1856 original)
    (input : KeyReady initial s state) (ready : ReadyToStep t)
    (effect : (KeySetup.effect s).Holds s t) : Keyed initial t state := by
  have writes : ∀ c ∈ (KeySetup.effect s).components, ∀ a, c.Covers a →
      (ScalarFrame.workRegion initial 1856).Contains a.toNat := by
    intro c member a covered
    simp only [KeySetup.effect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at member
    rcases member with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
    all_goals try exact covered.elim
    all_goals change (Component.mem (stackPtr s + _) _).Covers a at covered
    all_goals rw [show stackPtr s = scratch initial from input.rsp] at covered
    all_goals exact Update.Prepare.work_contains_scratch pre (by decide) covered
  have current := input.toContext.after_agrees pre ready effect.agrees
    (by intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl | rfl <;>
          simp [KeySetup.effect,Effect.components,Write.component,Operand.component]) writes (by
      intro i hi
      apply effect.agrees.byte
      intro c hc hcover
      simp only [KeySetup.effect, Effect.components, List.map_cons, List.map_nil,
        Write.component, Operand.component, List.mem_append, List.mem_cons,
        List.not_mem_nil, or_false] at hc
      rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
      all_goals try exact hcover.elim
      all_goals rcases hcover with ⟨j,hj,eq⟩
      all_goals rw [show rspOf s = scratch initial from input.rsp] at eq
      all_goals simp only [BitVec.add_assoc,← BitVec.ofNat_add,BitVec.add_right_inj,
        BitVec.ofNat_eq_ofNat] at eq
      all_goals have h := congrArg BitVec.toNat eq
      all_goals simp only [BitVec.toNat_ofNat] at h
      all_goals omega)
  have frame := current.toFrameState
  have stores := effect.writes
  change t.regValue .rax = memLoad s.external (s.regValue .rbx + 24) 64 ∧
    t.regValue .rcx = memLoad s.external (s.regValue .rbx + 16) 64 ∧
    t.regValue .rdx = memLoad s.external (s.regValue .rbx) 64 ∧
    t.regValue .rsi = memLoad s.external (s.regValue .rbx + 8) 64 ∧
    memLoad t.external (stackPtr s + 488) 64 = 0 ∧
    memLoad t.external (stackPtr s + 480) 64 = 0 ∧
    memLoad t.external (stackPtr s + 472) 64 = 0 ∧
    memLoad t.external (stackPtr s + 464) 64 = 0 ∧
    memLoad t.external (stackPtr s + 0) 64 = memLoad s.external (s.regValue .rbx) 64 ∧
    memLoad t.external (stackPtr s + 8) 64 = memLoad s.external (s.regValue .rbx + 8) 64 ∧
    memLoad t.external (stackPtr s + 16) 64 = memLoad s.external (s.regValue .rbx + 16) 64 ∧
    memLoad t.external (stackPtr s + 24) 64 = memLoad s.external (s.regValue .rbx + 24) 64 ∧
    memLoad t.external (stackPtr s + 32) 64 = 0 ∧
    memLoad t.external (stackPtr s + 40) 64 = 0 ∧
    memLoad t.external (stackPtr s + 48) 64 = 0 ∧
    memLoad t.external (stackPtr s + 56) 64 = 0 at stores
  rw [input.drbgPointer, show stackPtr s = scratch initial from input.rsp] at stores
  rcases stores with ⟨_, _, _, _, _, _, _, _, k0, k1, k2, k3, z0, z1, z2, z3⟩
  have allocated : MemReadable t (scratch initial) 64 := by
    rw [← show stackPtr t = scratch initial from frame.rsp]
    simpa only [BitVec.add_zero] using ScalarFrame.stack_readable (offset := 0) (len := 64) (frameOffset := 680) pre.callee frame (by decide) (by decide)
  have words (j : Nat) (hj : j < 4) :
      memLoad t.external (scratch initial + BitVec.ofNat 64 (8*j)) 64 =
      memLoad s.external (initial.regValue .rdi + BitVec.ofNat 64 (8*j)) 64 := by
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
    · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using k0
    · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using k1
    · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using k2
    · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using k3
  have src : MemReadable s (initial.regValue .rdi) 32 :=
    hasBytes_memReadable (by
      have h : (initial.regValue .rdi).toNat + 64 < 2^32 := pre.stateBounded
      change (initial.regValue .rdi).toNat + 32 < 2^32
      omega) input.drbg.1
  have copied := HMAC.Key.Output.bytes_of_words src
    ⟨by have h := allocated.low; omega, fun i hi => allocated.mem i (by omega)⟩ words
  refine ⟨current, effect.rip, HMAC.keyPad_size _ _, ?_⟩
  intro i
  have hi : i.val < 64 := by have h := i.isLt; simpa only [HMAC.keyPad_size] using h
  change t.external[BitVec.ofNat 64 ((scratch initial).toNat + i.val)]? = _
  simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  by_cases hk : i.val < 32
  · rw [HMAC.keyPad_getElem_key _ _ _ hi (by rw [input.drbg.key_size]; exact hk), UInt8.xor_zero]
    have hb := input.drbg.1.2 ⟨i.val, by rw [input.drbg.key_size]; exact hk⟩
    simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hb
    exact (copied i.val hk).trans hb
  · rw [HMAC.keyPad_getElem_padding _ _ _ hi (by rw [input.drbg.key_size]; omega)]
    have zero : memLoad t.external (scratch initial + BitVec.ofNat 64 (8*(i.val/8))) 64 = 0 := by
      rcases (by omega : i.val/8 = 4 ∨ i.val/8 = 5 ∨ i.val/8 = 6 ∨ i.val/8 = 7) with h | h | h | h
      all_goals rw [h]
      all_goals simp only [Nat.reduceMul, BitVec.ofNat_eq_ofNat]
      all_goals assumption
    have bytes := Bytes.of_memLoad (n := 64)
      (a := scratch initial + BitVec.ofNat 64 (8*(i.val/8))) (m := t.external) (by
        intro j hj
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]
        exact allocated.mem _ (by omega))
    rw [zero] at bytes
    have byte := bytes (i.val%8) (by omega)
    have hz : storedByte (0 : BitVec 64) (i.val%8) = 0 := by
      change UInt8.ofNat ((0 : Nat) >>> (8*(i.val%8))) = 0
      rw [Nat.zero_shiftRight]
      rfl
    rw [hz] at byte
    simpa only [BitVec.add_assoc, ← BitVec.ofNat_add,
      show 8*(i.val/8)+i.val%8=i.val by omega] using byte

end P256.Proofs.Nonce.Update.Seeded.Prepare
