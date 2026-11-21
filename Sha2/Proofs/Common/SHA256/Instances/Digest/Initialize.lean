import Sha2.Proofs.Common.SHA256.Instances.Initialize
import Sha2.Proofs.Common.Machine.FrameMemory
import Sha2.Proofs.Common.SHA256.Instances.Digest.Entry
import Sha2.Proofs.Common.SHA256.Initialize.Correctness

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Instances.Digest

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.SHA256.Initialize
open Sha2.Proofs.Common.Instructions

theorem initialize_pre {v : Wrapper.Variant} {initial s : RamState}
    (stack : Stack.Valid initial 784)
    (avoids : (Stack.region initial 784).Avoids (fun a => InProgram a ∨ InPageTables a))
    (grow : ∀ a : BitVec 64, (initial.external[a]?).isSome → (s.external[a]?).isSome)
    (rsp : rspOf s = stackPtr initial - 312)
    (rip : s.RIP = (Initialization.digest.layout v).start) :
    Initialize.Pre (Initialization.digest.layout v) (rspOf s + 168) s := by
  have write (t : RamState) (memory : t.external = s.external) (offset len : Nat)
      (bound : offset + len ≤ 312) (pos : 0 < len) :
      MemWritable t (rspOf s + BitVec.ofNat 64 offset) len := by
    have growT : ∀ a : BitVec 64, (initial.external[a]?).isSome → (t.external[a]?).isSome := by
      simpa only [memory] using grow
    rw [rsp]
    exact stack_frame_writable stack (by (try dsimp only [routine]); decide +kernel) (fun a ha h => avoids a ha (.inr h)) growT bound pos
  have apart (offset len : Nat) (bound : offset + len ≤ 312)
      (p : BitVec 64) (size : Nat) (inside : BlockInProgram p size) :
      RangeApart (rspOf s + BitVec.ofNat 64 offset) len p size := by
    rw [rsp]
    exact stack_frame_codeApart stack (by (try dsimp only [routine]); decide +kernel) (fun a ha h => avoids a ha (.inl h))
      bound (fun j hj => inside j (Nat.le_of_lt hj))
  refine ⟨rip, Initialization.valid .digest v, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [rsp]
    exact stack_frame_readable stack (by (try dsimp only [routine]); decide +kernel) grow (by (try dsimp only [routine]); decide +kernel)
  · intro i
    rcases i with ⟨i, hi⟩
    obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    all_goals
      refine ⟨rfl, by cases v <;> decide +kernel +revert, by cases v <;> decide +kernel +revert,
        (fun h => Bool.noConfusion h), ?_, ?_⟩
    · change CrossPageStore.Writable {s with RIP := (Initialization.digest.layout v).wordPC 0}
        (rspOf s + 256) 8
      exact CrossPageStore.Writable.of_memWritable
        (write {s with RIP := (Initialization.digest.layout v).wordPC 0} rfl 256 8 (by (try dsimp only [routine]); decide +kernel) (by (try dsimp only [routine]); decide +kernel))
    · have pc : (Initialization.digest.layout v).wordPC 0 = Extracted.textAddress + BitVec.ofNat 64 ((if v = .sha224 then 0x19 else 0x1c09) + 0) := by
        cases v <;> decide +kernel +revert
      have len : ∀ i : Fin 4, ((Initialization.digest.layout v).words[i]).bytes.length = 18 := by
        cases v <;> decide +kernel +revert
      rw [pc, len]
      change RangeApart (rspOf s + 256) 8 (Extracted.textAddress + BitVec.ofNat 64 ((if v = .sha224 then 0x19 else 0x1c09) + 0)) 18
      exact apart 256 8 (by (try dsimp only [routine]); decide +kernel) _ _
        (blockInProgram_of_textOffset ((if v = .sha224 then 0x19 else 0x1c09) + 0) 18 (by cases v <;> decide))
    · change CrossPageStore.Writable {s with RIP := (Initialization.digest.layout v).wordPC 1}
        (rspOf s + 248) 8
      exact CrossPageStore.Writable.of_memWritable
        (write {s with RIP := (Initialization.digest.layout v).wordPC 1} rfl 248 8 (by (try dsimp only [routine]); decide +kernel) (by (try dsimp only [routine]); decide +kernel))
    · have pc : (Initialization.digest.layout v).wordPC 1 = Extracted.textAddress + BitVec.ofNat 64 ((if v = .sha224 then 0x19 else 0x1c09) + 18) := by
        cases v <;> decide +kernel +revert
      have len : ∀ i : Fin 4, ((Initialization.digest.layout v).words[i]).bytes.length = 18 := by
        cases v <;> decide +kernel +revert
      rw [pc, len]
      change RangeApart (rspOf s + 248) 8 (Extracted.textAddress + BitVec.ofNat 64 ((if v = .sha224 then 0x19 else 0x1c09) + 18)) 18
      exact apart 248 8 (by (try dsimp only [routine]); decide +kernel) _ _
        (blockInProgram_of_textOffset ((if v = .sha224 then 0x19 else 0x1c09) + 18) 18 (by cases v <;> decide))
    · change CrossPageStore.Writable {s with RIP := (Initialization.digest.layout v).wordPC 2}
        (rspOf s + 240) 8
      exact CrossPageStore.Writable.of_memWritable
        (write {s with RIP := (Initialization.digest.layout v).wordPC 2} rfl 240 8 (by (try dsimp only [routine]); decide +kernel) (by (try dsimp only [routine]); decide +kernel))
    · have pc : (Initialization.digest.layout v).wordPC 2 = Extracted.textAddress + BitVec.ofNat 64 ((if v = .sha224 then 0x19 else 0x1c09) + 36) := by
        cases v <;> decide +kernel +revert
      have len : ∀ i : Fin 4, ((Initialization.digest.layout v).words[i]).bytes.length = 18 := by
        cases v <;> decide +kernel +revert
      rw [pc, len]
      change RangeApart (rspOf s + 240) 8 (Extracted.textAddress + BitVec.ofNat 64 ((if v = .sha224 then 0x19 else 0x1c09) + 36)) 18
      exact apart 240 8 (by (try dsimp only [routine]); decide +kernel) _ _
        (blockInProgram_of_textOffset ((if v = .sha224 then 0x19 else 0x1c09) + 36) 18 (by cases v <;> decide))
    · change CrossPageStore.Writable {s with RIP := (Initialization.digest.layout v).wordPC 3}
        (rspOf s + 232) 8
      exact CrossPageStore.Writable.of_memWritable
        (write {s with RIP := (Initialization.digest.layout v).wordPC 3} rfl 232 8 (by (try dsimp only [routine]); decide +kernel) (by (try dsimp only [routine]); decide +kernel))
    · have pc : (Initialization.digest.layout v).wordPC 3 = Extracted.textAddress + BitVec.ofNat 64 ((if v = .sha224 then 0x19 else 0x1c09) + 54) := by
        cases v <;> decide +kernel +revert
      have len : ∀ i : Fin 4, ((Initialization.digest.layout v).words[i]).bytes.length = 18 := by
        cases v <;> decide +kernel +revert
      rw [pc, len]
      change RangeApart (rspOf s + 232) 8 (Extracted.textAddress + BitVec.ofNat 64 ((if v = .sha224 then 0x19 else 0x1c09) + 54)) 18
      exact apart 232 8 (by (try dsimp only [routine]); decide +kernel) _ _ (blockInProgram_of_textOffset ((if v = .sha224 then 0x19 else 0x1c09) + 54) 18 (by cases v <;> decide))
  · intro i
    rcases i with ⟨i, hi⟩
    obtain rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
    all_goals change rspOf s + _ = (rspOf s + 168) + 64 + _
    all_goals rw [BitVec.add_assoc, BitVec.add_assoc]
    all_goals congr 1
    all_goals cases v <;> decide +kernel +revert
  · change rspOf s + 264 = (rspOf s + 168) + 96
    simp only [BitVec.add_assoc, BitVec.reduceAdd]; rfl
  · change rspOf s + 231 = (rspOf s + 168) + 63
    simp only [BitVec.add_assoc, BitVec.reduceAdd]; rfl
  · refine ⟨rfl, by cases v <;> decide +kernel +revert, by cases v <;> decide +kernel +revert, by cases v <;> decide +kernel +revert,
      by cases v <;> decide +kernel +revert, ?_, ?_, ?_, ?_, ?_⟩
    · change CrossPageStore.Writable {s with RIP := (Initialization.digest.layout v).wordPC 4}
        (rspOf s + 264) 8
      exact CrossPageStore.Writable.of_memWritable
        (write {s with RIP := (Initialization.digest.layout v).wordPC 4} rfl 264 8 (by (try dsimp only [routine]); decide +kernel) (by (try dsimp only [routine]); decide +kernel))
    · have pc : (Initialization.digest.layout v).wordPC 4 = Extracted.textAddress +
          BitVec.ofNat 64 ((if v = .sha224 then 0x19 else 0x1c09) + 72) := by
        cases v <;> decide +kernel +revert
      rw [pc]
      exact apart 264 8 (by (try dsimp only [routine]); decide +kernel) _ _
        (blockInProgram_of_textOffset ((if v = .sha224 then 0x19 else 0x1c09) + 72) _
          (by cases v <;> decide))
    · change MemWritable {s with RIP := (Initialization.digest.layout v).wordPC 4} (rspOf s + 231) 1
      exact write {s with RIP := (Initialization.digest.layout v).wordPC 4} rfl 231 1 (by (try dsimp only [routine]); decide +kernel) (by (try dsimp only [routine]); decide +kernel)
    · have pc : (Initialization.digest.layout v).wordPC 4 = Extracted.textAddress +
          BitVec.ofNat 64 ((if v = .sha224 then 0x19 else 0x1c09) + 72) := by
        cases v <;> decide +kernel +revert
      rw [pc]
      exact apart 231 1 (by (try dsimp only [routine]); decide +kernel) _ _
        (blockInProgram_of_textOffset ((if v = .sha224 then 0x19 else 0x1c09) + 72) _
          (by cases v <;> decide))
    · intro i hi j hj he
      exact OffsetsApart.ne (c₁ := 264) (len₁ := 8) (c₂ := 231) (len₂ := 1)
        (by unfold OffsetsApart; decide +kernel) (rspOf s)
        hi hj (by (try dsimp only [routine]); decide +kernel) he
  · exact apart 168 104 (by (try dsimp only [routine]); decide +kernel) _ _ (Initialization.inside .digest v)

theorem initialized {v : Wrapper.Variant} [bindings : Bindings] {initial s : RamState} {data : ByteArray}
    (machine : SupportedMachine bindings initial)
    (call : OneShot.ValidCall (routine v) initial data)
    (state : ExecutionState initial s (regions initial v))
    (rsp : stackPtr s = stackPtr initial - 312)
    (rip : s.RIP = (Initialization.digest.layout v).start) :
    ∃ t, ExecutionState initial t (regions initial v) ∧
      Initialize.Post (Initialization.digest.layout v) (rspOf s + 168) s t := by
  have avoid : (Stack.region initial 784).Avoids (fun a => InProgram a ∨ InPageTables a) :=
    (call.separation.2 _ (by exact List.mem_cons_of_mem _ (List.mem_singleton_self _))).2
  have rsp' : rspOf s = stackPtr initial - 312 := by
    simpa [rspOf, stackPtr, Operand.read] using rsp
  obtain ⟨fuel, t, run, ready, _, result⟩ := Initialize.correct
    (returnBoundary initial) (Initialization.digest.layout v)
    (valid_return_boundary machine call.stack call.returnAddress).2.2
    (Initialization.inside .digest v) (rspOf s + 168) s
    (supportedMachine_readyToStep state.machine) (Initialization.code .digest state.loaded v)
    (initialize_pre (v := v) call.stack avoid state.allocated rsp' rip)
  refine ⟨t, state.of_agrees ?_ run ready result.frame ?_ ?_, result⟩
  · intro region member a ha h
    have mem : region ∈ [OneShot.outputRegion (routine v) initial,
        Stack.region initial (routine v).minStackBytes] := by
      have stackSize : (routine v).minStackBytes = 784 := rfl
      simpa [regions, stackSize] using member
    exact (call.separation.2 region mem).2 a ha (.inl h)
  · intro c hc a ha
    change c ∈ [.reg 0, .reg 0, .reg 0, .reg 0,
      .mem ((rspOf s + 168) + 64) 32, .mem ((rspOf s + 168) + 96) 8,
      .mem ((rspOf s + 168) + 63) 1, .rip] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    all_goals refine ⟨Stack.region initial 784, by simp [regions], ?_⟩
    all_goals rw [rsp', BitVec.add_assoc] at ha
    · exact stack_frame_contains call.stack (frame := 312) (offset := 232) (by (try dsimp only [routine]); decide +kernel) (by (try dsimp only [routine]); decide +kernel) ha
    · exact stack_frame_contains call.stack (frame := 312) (offset := 264) (by (try dsimp only [routine]); decide +kernel) (by (try dsimp only [routine]); decide +kernel) ha
    · exact stack_frame_contains call.stack (frame := 312) (offset := 231) (by (try dsimp only [routine]); decide +kernel) (by (try dsimp only [routine]); decide +kernel) ha
  · change .df ∉ ([.reg 0, .reg 0, .reg 0, .reg 0,
      .mem ((rspOf s + 168) + 64) 32, .mem ((rspOf s + 168) + 96) 8,
      .mem ((rspOf s + 168) + 63) 1, .rip] : List Component)
    simp

end Sha2.Proofs.Common.SHA256.Instances.Digest
