import P256.Proofs.Nonce.Initialize.Conversions.Int2Octets.Loop.Prepare
import P256.Proofs.Nonce.Initialize.Conversions.Int2Octets.Loop.CopyPre
import P256.Proofs.Field.Representation

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Conversions.Int2Octets.Loop

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Field P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Proofs.Program (stack_sub_writable8 writable_of_grow readable_of_grow)

theorem input_address {initial s : RamState} {i : Nat} (registers : LoopRegisters initial s i)
    (hi : i < 4) :
    (Operand.reg 13 : Operand 64).read s + ((Operand.reg 5 : Operand 64).read s <<< 3) =
      initial.regValue .rdi + BitVec.ofNat 64 (8*i) := by
  change s.regValue .r13 + (s.regValue .rbp <<< 3) = _
  rw [registers.input, registers.index]
  have cases : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases cases with rfl | rfl | rfl | rfl <;> rfl

theorem prepare_stage [Bindings] {initial s : RamState} {boundary : ReturnBoundary} {i : Nat}
    (pre : Pre initial boundary) (stage : Stage initial s boundary)
    (registers : LoopRegisters initial s i) (hi : i < 4) (rip : s.RIP = 0x107050) :
    ∃ t, Stage initial t boundary ∧ (prepareEffect i s).Holds s t ∧
      (∀ a : BitVec 64, (registerRegion initial .rdx 32).Contains a.toNat →
        t.external[a]? = s.external[a]?) := by
  have address : rspOf s + 16 = stackPtr initial - 56 := by
    change stackPtr s + 16 = _
    rw [stage.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
  have input : MemReadable s
      ((Operand.reg 13 : Operand 64).read s + ((Operand.reg 5 : Operand 64).read s <<< 3)) 8 := by
    rw [input_address registers hi]
    apply readable_of_grow (t := s) _ stage.allocated
    apply memoryRegion_memReadable pre.inputBounded pre.inputAllocated
    · have bound := pre.inputBounded
      change (initial.regValue .rdi).toNat + 32 < 2^32 at bound
      rw [toNat_add_ofNat _ _ (by omega)]
      change (initial.regValue .rdi).toNat ≤ _
      omega
    · have bound := pre.inputBounded
      change (initial.regValue .rdi).toNat + 32 < 2^32 at bound
      rw [toNat_add_ofNat _ _ (by omega)]
      change _ ≤ (initial.regValue .rdi).toNat + 32
      omega
  have writable : MemWritable s (rspOf s+16) 8 := by
    rw [address]
    exact writable_of_grow (stack_sub_writable8 pre.stack (fun a ha ht => pre.avoids _ (by simp) a ha (.inr ht)) (by decide) (by decide)) stage.allocated
  have apart : RangeApart (rspOf s+16) 8 0x107050 53 := by
    rw [address]
    exact stack_apart_code pre 56 8 0x7050 53 (by decide) (by decide) (by decide)
  obtain ⟨fuel,t,run,ready,_,effect⟩ := prepare boundary pre.outerBoundary i hi s
    (readyToStep stage.machine stage.bindingsSupported)
    (programText_slice (programLoaded_codeIn stage.loaded) 0x7050 prepareBytes
      (by decide) (by decide +kernel))
    ⟨rip, registers.remaining, registers.length, registers.index, input, writable, apart⟩
  have onlyMemory : ∀ c ∈ (prepareEffect i s).components, ∀ a, c.Covers a →
      (Component.mem (stackPtr initial-56) 8).Covers a := by
    intro c hc a ha
    simp only [prepareEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.cons_append, List.nil_append,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact False.elim ha
    simpa only [address] using ha
  have writes : WritesWithin (prepareEffect i s).components
      #v[registerRegion initial .rdx 32, Stack.region initial 128] := by
    intro c hc a ha
    exact ⟨Stack.region initial 128, by simp,
      stackRegion_contains_sub pre.stack.2.2.1 (by decide) (by decide) (onlyMemory c hc a ha)⟩
  have saved : ∀ c ∈ (prepareEffect i s).components, ∀ a,
      (Component.mem (stackPtr initial-48) 56).Covers a → ¬ c.Covers a := by
    intro c hc a ha hb
    obtain ⟨j,hj,rfl⟩ := ha
    obtain ⟨k,hk,eqn⟩ := onlyMemory c hc _ hb
    have apart : OffsetsApart (-48) 56 (-56) 8 := by unfold OffsetsApart; decide
    exact apart.ne (stackPtr initial) hj hk (by decide) (by simpa only [BitVec.sub_eq_add_neg] using eqn)
  refine ⟨t, stage.of_agrees pre run ready effect.agrees writes saved
    (by simp [prepareEffect, Effect.components, Write.component, Operand.component]), effect, ?_⟩
  intro a ha
  apply effect.agrees.memory
  intro c hc hb
  exact pre.separation (1 : Fin 3) 2 (by decide) _ ha
    (stackRegion_contains_sub pre.stack.2.2.1 (by decide) (by decide) (onlyMemory c hc a hb))

end P256.Proofs.Nonce.Initialize.Conversions.Int2Octets.Loop
