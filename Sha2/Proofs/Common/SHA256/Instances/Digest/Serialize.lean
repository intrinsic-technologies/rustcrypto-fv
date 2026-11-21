import Sha2.Proofs.Common.SHA256.Instances.Digest.Finalized
import Sha2.Proofs.Common.SHA256.Serialize.Payload

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Instances.Digest

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.Instructions

theorem store_pre {v : Wrapper.Variant} {s : RamState} {p : BitVec 64}
    {output : Serialize.OutputRegister}
    (rip : s.RIP = p)
    (writable : CrossPageStore.Writable s ((.reg output.value : Operand 64).read s) v.outputBytes)
    (apart : RangeApart ((.reg output.value : Operand 64).read s) v.outputBytes
      p (Serialize.bytes (.store output (v == .sha224))).length) :
    Serialize.StorePre p output s (v == .sha224) := by
  refine ⟨rip, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact writable.add 0 (by cases v <;> decide +kernel)
  · exact RangeApart.add_left apart 0 (by cases v <;> decide +kernel)
  · exact writable.add 4 (by cases v <;> decide +kernel)
  · exact RangeApart.add_left apart 4 (by cases v <;> decide +kernel)
  · exact writable.add 8 (by cases v <;> decide +kernel)
  · exact RangeApart.add_left apart 8 (by cases v <;> decide +kernel)
  · exact writable.add 12 (by cases v <;> decide +kernel)
  · exact RangeApart.add_left apart 12 (by cases v <;> decide +kernel)
  · exact writable.add 16 (by cases v <;> decide +kernel)
  · exact RangeApart.add_left apart 16 (by cases v <;> decide +kernel)
  · exact writable.add 20 (by cases v <;> decide +kernel)
  · exact RangeApart.add_left apart 20 (by cases v <;> decide +kernel)
  · exact writable.add 24 (by cases v <;> decide +kernel)
  · exact RangeApart.add_left apart 24 (by cases v <;> decide +kernel)
  · cases v with
    | sha224 => trivial
    | sha256 => exact writable.add 28 (by decide +kernel)
  · cases v with
    | sha224 => trivial
    | sha256 => exact RangeApart.add_left apart 28 (by decide +kernel)

theorem serialized {v : Wrapper.Variant} [bindings : Bindings] {initial before s : RamState} {data : ByteArray}
    (machine : SupportedMachine bindings initial)
    (call : OneShot.ValidCall (routine v) initial data)
    (finished : Finalize.Finalized (Finalization.digest.layout v) initial before s (regions initial v) data)
    (output : s.regValue .rbx = initial.regValue .rdx) :
    ∃ a t, ExecutionState initial t (regions initial v) ∧
      (Serialize.effect (Segment.loadSwap.pc v) (.loadSwap .at64 (v == .sha224)) s).Holds s a ∧
      (Serialize.effect (Segment.store.pc v) (.store .rbx (v == .sha224)) a).Holds a t ∧
      (OneShot.outputRegion (routine v) initial).HasBytes t.external (v.hash data) := by
  have sizeEqual : (if v == .sha224 then 28 else 32) = v.outputBytes := by
    cases v <;> rfl
  have outside := (valid_return_boundary machine call.stack call.returnAddress).2.2
  have avoidRegions : ∀ region ∈ regions initial v, region.Avoids InProgram := by
    intro region member addr ha h
    have mem : region ∈ [OneShot.outputRegion (routine v) initial,
        Stack.region initial (routine v).minStackBytes] := by
      have stackSize : (routine v).minStackBytes = 784 := rfl
      simpa [regions, stackSize] using member
    exact (call.separation.2 region mem).2 addr ha (.inl h)
  have rsp : rspOf s = stackPtr initial - 312 := finished.rsp
  have read (offset len : Nat) (bound : offset + len ≤ 312) :
      MemReadable s (rspOf s + BitVec.ofNat 64 offset) len := by
    rw [rsp]
    exact stack_frame_readable call.stack (frame := 312) (by (try dsimp only [routine]); decide +kernel) finished.state.allocated bound
  have pre : Serialize.LoadPre (Segment.loadSwap.pc v) .at64 s (v == .sha224) :=
    ⟨finished.rip.trans (by cases v <;> rfl), read 64 4 (by (try dsimp only [routine]); decide +kernel), read 68 4 (by (try dsimp only [routine]); decide +kernel), read 72 4 (by (try dsimp only [routine]); decide +kernel),
      read 76 4 (by (try dsimp only [routine]); decide +kernel), read 80 4 (by (try dsimp only [routine]); decide +kernel), read 84 4 (by (try dsimp only [routine]); decide +kernel),
      read 88 4 (by (try dsimp only [routine]); decide +kernel), by cases v with
        | sha224 => trivial
        | sha256 => exact read 92 4 (by (try dsimp only [routine]); decide +kernel)⟩
  obtain ⟨fuelA, a, runA, readyA, _, load⟩ := Serialize.run (Segment.loadSwap.pc v) (.loadSwap .at64 (v == .sha224))
    (returnBoundary initial) outside (Segment.inside .loadSwap (v := v)) s
    (supportedMachine_readyToStep finished.state.machine)
    (Segment.code .loadSwap finished.state.loaded (v := v)) pre
  have stateA : ExecutionState initial a (regions initial v) :=
    finished.state.of_agrees avoidRegions runA readyA load.agrees
      (by
        intro comp hc addr ha
        have nomem : ∀ comp ∈ (Serialize.effect (Segment.loadSwap.pc v) (.loadSwap .at64 (v == .sha224)) s).components,
            ∀ addr, ¬ comp.Covers addr := by
          cases v <;> simp [Serialize.effect, Effect.components, Component.Covers]
        exact (nomem comp hc addr ha).elim)
      (by cases v <;> simp [Serialize.effect, Effect.components])
  have outputA : (.reg 3 : Operand 64).read a = initial.regValue .rdx :=
    (load.agrees.read (n := 64) (r := 3) (by cases v <;> simp [Serialize.effect, Effect.components])).trans output
  have outputContains {addr : BitVec 64}
      (covered : (Component.mem (initial.regValue .rdx) v.outputBytes).Covers addr) :
      (OneShot.outputRegion (routine v) initial).Contains addr.toNat := by
    obtain ⟨i, hi, rfl⟩ := covered
    exact memoryRegion_contains_add call.outputInMemory.2.1 (Nat.le_refl _) (Nat.le_refl _) hi
  have readable : MemReadable a (initial.regValue .rdx) v.outputBytes :=
    Common.Encoding.Serialize.readable_of_grow
      (memoryRegion_memReadable call.outputInMemory.2.1 call.outputInMemory.2.2
        (Nat.le_refl _) (Nat.le_refl _)) stateA.allocated
  have writable : CrossPageStore.Writable a (initial.regValue .rdx) v.outputBytes := by
    refine ⟨readable, tables_of_not_reserved (by cases v <;> decide) readable.low ?_⟩
    intro i hi reserved
    exact (call.separation.2 _ (List.mem_cons_self)).2 _
      (outputContains ⟨i, hi, rfl⟩) (.inr reserved)
  have codeApart : RangeApart (initial.regValue .rdx) v.outputBytes (Segment.store.pc v)
      (Serialize.bytes (.store .rbx (v == .sha224))).length := by
    intro i hi j hj equal
    apply (call.separation.2 _ (List.mem_cons_self)).2 _ (outputContains ⟨i, hi, rfl⟩)
    left
    rw [equal]
    exact Segment.inside .store (v := v) j (Nat.le_of_lt hj)
  have storePre : Serialize.StorePre (Segment.store.pc v) .rbx a (v == .sha224) := by
    have nextPC : (Segment.loadSwap.pc v) + BitVec.ofNat 64
        (Serialize.bytes (.loadSwap .at64 (v == .sha224))).length = Segment.store.pc v := by
      cases v <;> decide +kernel
    apply store_pre (nextPC ▸ load.rip)
    · simpa only [Serialize.OutputRegister.value, outputA] using writable
    · simpa only [Serialize.OutputRegister.value, outputA] using codeApart
  obtain ⟨fuelT, t, runT, readyT, _, store⟩ := Serialize.run (Segment.store.pc v) (.store .rbx (v == .sha224))
    (returnBoundary initial) outside (Segment.inside .store (v := v)) a readyA
    (Segment.code .store stateA.loaded (v := v)) storePre
  have contained (offset : Nat) (bound : offset + 4 ≤ v.outputBytes) {addr : BitVec 64}
      (covered : (Component.mem ((.reg 3 : Operand 64).read a + BitVec.ofNat 64 offset) 4).Covers addr) :
      (OneShot.outputRegion (routine v) initial).Contains addr.toNat := by
    obtain ⟨i, hi, rfl⟩ := covered
    rw [outputA, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact outputContains ⟨offset+i, by omega, rfl⟩
  have stateT : ExecutionState initial t (regions initial v) :=
    stateA.of_agrees avoidRegions runT readyT store.agrees
      (by
        intro comp hc addr ha
        have membership : OneShot.outputRegion (routine v) initial ∈ regions initial v := by simp [regions]
        refine ⟨OneShot.outputRegion (routine v) initial, membership, ?_⟩
        cases v <;> simp only [Serialize.effect, Effect.components,
          show (Wrapper.Variant.sha224 == .sha224) = true from by decide,
          show (Wrapper.Variant.sha256 == .sha224) = false from by decide,
          Bool.false_eq_true, ite_false, ite_true, List.map_cons, List.map_nil,
          List.cons_append, List.nil_append, Write.component, Operand.component,
          Serialize.OutputRegister.value, List.mem_cons, List.not_mem_nil, or_false] at hc
        all_goals rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | hc
        all_goals try exact ha.elim
        all_goals try (rcases hc with rfl | rfl)
        all_goals try exact ha.elim
        all_goals first
          | exact contained 0 (by (try dsimp only [routine]); decide +kernel) ha
          | exact contained 4 (by (try dsimp only [routine]); decide +kernel) ha
          | exact contained 8 (by (try dsimp only [routine]); decide +kernel) ha
          | exact contained 12 (by (try dsimp only [routine]); decide +kernel) ha
          | exact contained 16 (by (try dsimp only [routine]); decide +kernel) ha
          | exact contained 20 (by (try dsimp only [routine]); decide +kernel) ha
          | exact contained 24 (by (try dsimp only [routine]); decide +kernel) ha
          | exact contained 28 (by (try dsimp only [routine]); decide +kernel) ha)
      (by cases v <;> simp [Serialize.effect, Effect.components])
  obtain ⟨hash, words, equal⟩ := finished.digest
  have wordsS : HashStateAt s (rspOf s + BitVec.ofNat 64 Serialize.HashOffset.at64.value) hash := by
    have zero : (Finalization.digest.layout v).buffer ((Finalization.digest.layout v).sp initial) =
        (Finalization.digest.layout v).sp initial := BitVec.add_zero _
    change HashStateAt s ((Finalization.digest.layout v).buffer _ + 64) hash at words
    rw [zero] at words
    exact rsp ▸ words
  have outputBytes := Serialize.store_hasBytes (Serialize.loadSwap_words pre wordsS load) store
    (fun i hi => by
      change (t.external[(.reg 3 : Operand 64).read a + BitVec.ofNat 64 i]?).isSome
      rw [outputA]
      exact store.agrees.grow _ (readable.mem i (by simpa only [sizeEqual] using hi)))
  have hashEqual : (if v == .sha224 then (serializeHash hash).extract 0 28
      else serializeHash hash) = v.hash data := by
    cases v <;> exact equal
  rw [hashEqual, sizeEqual] at outputBytes
  simp only [Serialize.OutputRegister.value] at outputBytes
  rw [outputA] at outputBytes
  exact ⟨a, t, stateT, load, store, outputBytes⟩

end Sha2.Proofs.Common.SHA256.Instances.Digest
