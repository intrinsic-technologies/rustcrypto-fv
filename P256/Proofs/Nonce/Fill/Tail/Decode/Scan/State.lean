import P256.Proofs.Nonce.Fill.Tail.Decode.State
import P256.Proofs.Nonce.Fill.Work
import P256.Proofs.Nonce.Fill.Memory
import P256.Proofs.Common.Encoding.Serialize.Convert.SavePointer

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill.Tail.Decode

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Common.Encoding.Serialize (read_mem_of_agrees)

structure ScanState [Bindings] (initial s : RamState) (orderAddress : BitVec 64)
    (state : Nonce.State) : Prop extends Frame initial s, Slots initial s where
  generator : GeneratorAt s (initial.regValue .rdi) orderAddress (Signing.Search.nextState state)
  output : (registerRegion initial .rsi 32).HasBytes s.external (updateValue state).value

variable [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
  {orderAddress : BitVec 64} {original state : Nonce.State}

theorem ScanState.after_registers {components : List Component}
    (input : ScanState initial s orderAddress state) (ready : ReadyToStep t)
    (agrees : AgreesExcept components s t)
    (noMemory : ∀ c ∈ components, ∀ a, ¬ c.Covers a) (sp : .reg 4 ∉ components)
    (hdf : Component.df ∉ components := by component_not_mem)
    (hmxcsr : Component.mxcsr ∉ components := by component_not_mem)
    (hfcw : Component.fcw ∉ components := by component_not_mem) :
    ScanState initial t orderAddress state := by
  have memory := agrees.external noMemory
  refine ⟨input.toFrame.after_registers ready agrees noMemory sp hdf hmxcsr hfcw,
    input.toSlots.of_memory_eq memory, ?_, ?_⟩
  · simpa only [GeneratorAt, DrbgAt, SecretKeyFromBytes.Scalar.Nat256At, memory] using input.generator
  · simpa only [memory] using input.output

theorem ScanState.after_store {offset len : Nat}
    (pre : Pre initial boundary orderAddress original)
    (input : ScanState initial s orderAddress state) (ready : ReadyToStep t)
    (agrees : AgreesExcept [.mem (stackPtr s + BitVec.ofNat 64 offset) len, .rip] s t)
    (bound : offset + len ≤ 184)
    (apart : ∀ slot : Nat, slot ∈ [40, 48, 56, 64, 136, 144] →
      OffsetsApart (BitVec.ofNat 64 slot) 8 (BitVec.ofNat 64 offset) len) :
    ScanState initial t orderAddress state := by
  have writes : WritesWithin [.mem (stackPtr s + BitVec.ofNat 64 offset) len, .rip]
      #v[Stack.region initial 2096] := by
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · refine ⟨Stack.region initial 2096, by simp, ?_⟩
      rw [input.rsp, frameBase_add initial (by omega)] at ha
      exact ScalarFrame.stack_contains pre.toCalleePre (by omega) (by omega) ha
    · exact ha.elim
  have frame := input.toFrame.after_effect pre ready agrees (by
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · refine ⟨ScalarFrame.workRegion initial 2096, by simp [workRegions], ?_⟩
      rw [input.rsp, frameBase_add initial (by omega)] at ha
      exact ScalarFrame.work_contains pre.toCalleePre (by omega) (by omega) ha
    · exact ha.elim) (by simp)
  have word (slot n : Nat) (hs : slot ∈ [40, 48, 56, 64, 136, 144]) (hn : n / 8 ≤ 8) :
      memLoad t.external (frameBase initial + BitVec.ofNat 64 slot) n =
        memLoad s.external (frameBase initial + BitVec.ofNat 64 slot) n := by
    apply read_mem_of_agrees agrees
    intro i hi c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · rintro ⟨j, hj, eq⟩
      rw [input.rsp] at eq
      exact OffsetsApart.ne (apart slot hs) (base := frameBase initial) (hl := by omega) (hi := (by omega : i < 8)) (hj := hj) eq
    · exact id
  refine ⟨frame, ⟨(word 40 64 (by simp) (by decide)).trans input.outputSlot,
    (word 48 64 (by simp) (by decide)).trans input.lengthSlot,
    (word 56 32 (by simp) (by decide)).trans input.bitsSlot,
    (word 64 64 (by simp) (by decide)).trans input.statePointerSlot,
    (word 136 64 (by simp) (by decide)).trans input.valuePointerSlot,
    (word 144 64 (by simp) (by decide)).trans input.generatorPointerSlot⟩,
    ?_, ?_⟩
  · apply input.generator.of_frame pre.outputBounded pre.orderBounded
      (agrees.memoryWriteFrame writes)
    · intro region hr
      have eq : region = Stack.region initial 2096 := by simpa using hr
      subst region
      exact pre.separation 1 2 (by decide)
    · intro region hr
      have eq : region = Stack.region initial 2096 := by simpa using hr
      subst region
      exact pre.orderDisjoint _ (by simp)
  · apply frame_hasBytes (agrees.memoryWriteFrame writes) _ pre.inputBounded input.output
    intro region hr
    have eq : region = Stack.region initial 2096 := by simpa using hr
    subst region
    exact pre.separation 0 2 (by decide)

theorem ScanState.order_readable
    (pre : Pre initial boundary orderAddress original)
    (input : ScanState initial s orderAddress state) {offset : Nat} (bound : offset + 8 ≤ 32) :
    MemReadable s (orderAddress + BitVec.ofNat 64 offset) 8 := by
  apply readable_of_grow _ input.allocated
  apply memoryRegion_memReadable pre.orderBounded pre.orderAllocated
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : offset < 2^64),
      Nat.mod_eq_of_lt (by have h := pre.orderBounded; change orderAddress.toNat + 32 < 2^32 at h; omega)]
    exact Nat.le_add_right _ _
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : offset < 2^64),
      Nat.mod_eq_of_lt (by have h := pre.orderBounded; change orderAddress.toNat + 32 < 2^32 at h; omega)]
    exact Nat.add_le_add_left bound _

theorem ScanState.stack_writable1
    (pre : Pre initial boundary orderAddress original)
    (input : ScanState initial s orderAddress state) :
    MemWritable s (stackPtr s + 8) 1 := by
  have addr : stackPtr s + 8 = stackPtr initial - 224 := by
    rw [input.rsp]
    exact frameBase_add initial (offset := 8) (by decide)
  rw [addr]
  exact writable_of_grow (stack_sub_writable pre.stack
    (fun a ha hp => pre.avoids _ (by simp) a ha (.inr hp))
    (offset := 224) (len := 1) (by decide) (by decide) (by decide) (by omega)) input.allocated

end P256.Proofs.Nonce.Fill.Tail.Decode
