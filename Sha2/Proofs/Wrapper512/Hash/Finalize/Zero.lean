import Sha2.Proofs.Common.Machine.CallMemory
import Sha2.Proofs.Wrapper512.Hash.Finalize.State
import Sha2.Proofs.Wrapper512.Machine.Initialize
import Sha2.Proofs.Wrapper512.Absorb.Memory
import Sha2.Proofs.Wrapper.Memory
import Sha2.Proofs.Wrapper512.Hash.Finalize.Zero.Machine

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Hash.Finalize

open Sha2.Spec Sha2.Proofs.Program Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.SHA512 Sha2.Proofs.Common.Machine

set_option maxRecDepth 8192 in
theorem zero_address {form : Form} (last : Bool) {initial s : RamState}
    (rsp : stackPtr s = stackPtr initial - BitVec.ofNat 64 form.frameBytes) (k : Nat) :
    rspOf s + BitVec.ofNat 64 (Zero.base last form + k) =
      stackPtr initial - BitVec.ofNat 64 (form.finalMemory.buffer - if last then 56 else 0) + BitVec.ofNat 64 k := by
  have split : form.frameBytes = (form.finalMemory.buffer - if last then 56 else 0) + Zero.base last form := by
    cases form with
    | slices | digest | reset _ => cases last <;> rfl
    | finalizeIntoReset second | traitFinalizeIntoReset second => cases second <;> cases last <;> rfl
  change stackPtr s + _ = _
  rw [rsp, split, BitVec.ofNat_add, BitVec.ofNat_add]
  simp only [BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.add_assoc]
  rw [← BitVec.add_assoc (-BitVec.ofNat 64 (Zero.base last form)), BitVec.add_left_neg, BitVec.zero_add]

theorem zero_frame {v : Variant} {form : Form} (last : Bool) {initial s t : RamState} (rsp : stackPtr s = stackPtr initial - BitVec.ofNat 64 form.frameBytes)
    (effect : (Zero.effect v last s form).Holds s t)
 :
    AgreesExcept [.mem (stackPtr initial - BitVec.ofNat 64 (form.finalMemory.buffer - if last then 56 else 0)) 56, .rip] s t := by
  have cover (offset : Nat) (bound : offset + 8 ≤ 56) (a : BitVec 64)
      (covered : (Component.mem (rspOf s + BitVec.ofNat 64 (Zero.base last form + offset)) 8).Covers a) :
      (Component.mem (stackPtr initial - BitVec.ofNat 64 (form.finalMemory.buffer - if last then 56 else 0)) 56).Covers a := by
    obtain ⟨i, hi, rfl⟩ := covered
    refine ⟨offset + i, by omega, ?_⟩
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    simpa only [Nat.add_assoc] using zero_address last rsp (offset+i)
  apply Common.Encoding.Serialize.agrees_of_footprint effect.agrees
  · intro c hc noMem
    simp only [Zero.effect, Zero.effectAt, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
    all_goals simp_all [Component.isMem]
  · intro c hc a covered
    simp only [Zero.effect, Zero.effectAt, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
    all_goals try exact covered.elim
    all_goals refine ⟨.mem (stackPtr initial - BitVec.ofNat 64 (form.finalMemory.buffer - if last then 56 else 0)) 56, by simp, ?_⟩
    · exact cover 0 (by decide) a covered
    · exact cover 8 (by decide) a covered
    · exact cover 16 (by decide) a covered
    · exact cover 24 (by decide) a covered
    · exact cover 32 (by decide) a covered
    · exact cover 40 (by decide) a covered
    · exact cover 48 (by decide) a covered

theorem zero_words {v : Variant} {form : Form} (last : Bool) {s t : RamState} (effect : (Zero.effect v last s form).Holds s t) :
    ∀ j < 7, memLoad t.external (rspOf s + BitVec.ofNat 64 (Zero.base last form + 8 * j)) 64 = 0 := by
  have words := effect.writes
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ at words
  intro j bound
  have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 := by omega
  rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact words.1
  · exact words.2.1
  · exact words.2.2.1
  · exact words.2.2.2.1
  · exact words.2.2.2.2.1
  · exact words.2.2.2.2.2.1
  · exact words.2.2.2.2.2.2


set_option hygiene false in
macro "zero_layout" : tactic => `(tactic| (
  cases form
  case' finalizeIntoReset second => cases second
  case' traitFinalizeIntoReset second => cases second
  case' reset stage =>
    have hs : stage = 0 ∨ stage = 1 ∨ stage = 2 := by omega
    rcases hs with rfl | rfl | rfl
  all_goals cases last
  all_goals dsimp only [Form.finalMemory, Form.frameBytes, Form.stackBytes, ResetLayout.resetMemory,
    ResetLayout.finalizeMemory, ResetLayout.cloneMemory, Zero.base, Variant.routine,
    Bool.false_eq_true] at *))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1500000 in
theorem zero_half [Bindings] (last : Bool) {v : Variant} {form : Form} {initial s : RamState} {inputs : Array Input} {message : ByteArray}
    {hash : Array UInt64} (ctx : Context v initial inputs form)
    (input : Working v initial s message hash form) (rip : s.RIP = v.pc (Zero.offset last form v) form)
 :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ Working v initial t message hash form ∧ t.RIP = v.pc (Zero.nextOffset last form v) form ∧
      (∀ i < 56, t.external[stackPtr initial - BitVec.ofNat 64 (form.finalMemory.buffer - if last then 56 else 0) + BitVec.ofNat 64 i]? = some 0) ∧
      AgreesExcept [.mem (stackPtr initial - BitVec.ofNat 64 (form.finalMemory.buffer - if last then 56 else 0)) 56, .rip] s t := by
  have writable (offset : Nat) (bound : offset ≤ (v.routine form).minStackBytes) (align : offset % 8 = 0) :
      MemWritable s (stackPtr initial - BitVec.ofNat 64 offset) 8 := by
    have w := Dispatch.stack_sub_writable8_512 ctx bound align
    exact ⟨w.low, fun i hi => input.allocated _ (w.mem i hi), w.tables⟩
  have address (i : Nat) (member : i ∈ ([0,8,16,24,32,40,48] : List Nat)) : stackPtr initial - BitVec.ofNat 64 (form.finalMemory.buffer - if last then 56 else 0) + BitVec.ofNat 64 i =
      stackPtr initial - BitVec.ofNat 64 (form.finalMemory.buffer - (if last then 56 else 0) - i) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals zero_layout <;> simp [BitVec.sub_eq_add_neg, BitVec.add_assoc]
  have pre : Zero.Pre (v.textOffset form + Zero.offset last form v) (Zero.base last form) s := by
    refine ⟨rip, ?_, ?_⟩
    · intro i member
      rw [zero_address last input.rsp]
      rw [address i member]
      apply writable
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals zero_layout <;> decide +kernel
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at member
        rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals zero_layout <;> decide +kernel
    · intro i member offset len bound
      rw [zero_address last input.rsp, address i member]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals apply Machine.Stages.stack_slot_codeApart ctx (by zero_layout <;> decide +kernel) (by zero_layout <;> decide +kernel) bound
  obtain ⟨fuel, t, run, ready, codeAfter, effect⟩ :=
    Zero.run last (returnBoundary initial) (valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2
      s (supportedMachine_readyToStep input.machine) (Zero.code (form := form) last input.loaded) pre
  have frame := zero_frame last input.rsp effect
  have preserved := Absorb.preserved_of_agrees
    (keptFrameOutput := by intro _; left; simp) ctx input.toPreserved run ready frame
    (by
      intro c hc a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · have apart : (match form with
          | .slices | .digest => 56 + 624 ≤ (form.finalMemory.buffer - if last then 56 else 0) ∨ (form.finalMemory.buffer - if last then 56 else 0) ≤ 600
          | _ => ∀ slot ∈ form.metadataSlots, OffsetsApart (-BitVec.ofNat 64 (form.finalMemory.buffer - if last then 56 else 0)) 56 (-BitVec.ofNat 64 slot) 8) := by
          zero_layout
          all_goals first | exact .inr (by decide +kernel) | (simp only [Form.metadataSlots, List.mem_cons, List.not_mem_nil, or_false]; intro slot member; rcases member with rfl | rfl | rfl | rfl; all_goals unfold OffsetsApart; all_goals decide +kernel)
        have lm := Absorb.local_memory (form := form) (by zero_layout <;> decide +kernel)
          (by zero_layout <;> decide +kernel) (by cases form <;> exact apart) a ha
        cases form <;> exact lm
      · exact ha.elim) (by simp)
  have hash := Absorb.hashState_of_bytes input.hashWords (by
    intro i hi
    apply frame.byte
    intro c hc ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · obtain ⟨j, hj, he⟩ := ha
      apply OffsetsApart.ne (c₁ := -BitVec.ofNat 64 (form.finalMemory.buffer - if last then 56 else 0)) (len₁ := 56)
        (c₂ := -BitVec.ofNat 64 form.finalMemory.hash) (len₂ := 64) (by zero_layout <;> unfold OffsetsApart <;> decide +kernel)
        (stackPtr initial) hj hi (by decide)
      simpa only [BitVec.sub_eq_add_neg, BitVec.ofNat_eq_ofNat] using he.symm
    · exact ha.elim)
  have regs (r : Syntax.Reg) : t.regValue r = s.regValue r := by
    have h := frame.read (n := 64) (r := BitVec.ofNat 5 r.fin.val) (by simp)
    cases r <;> exact h
  refine ⟨fuel, t, run, ⟨⟨preserved, hash, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_, frame⟩
  · simpa only [hashPointerState, regs] using input.hashPointer
  · exact (regs _).trans input.blocks
  · exact (regs _).trans input.blocksHigh
  · exact (regs _).trans input.tailLength
  · simpa only [Zero.effect, Zero.effectAt, Zero.pc, Zero.nextOffset, Zero.bytes, Variant.pc,
      Nat.add_assoc] using effect.rip
  · intro i hi
    have readable := Machine.Initialize.stack_readable ctx preserved.toState
      (offset := form.finalMemory.buffer - if last then 56 else 0) (len := 56) (by zero_layout <;> decide +kernel)
      (by zero_layout <;> decide +kernel)
    have words := zero_words last effect (i / 8) (by omega)
    have address := zero_address last input.rsp
    rw [address] at words
    have bytes : Bytes t.external (stackPtr initial - BitVec.ofNat 64 (form.finalMemory.buffer - if last then 56 else 0) + BitVec.ofNat 64 (8*(i/8))) 8
        (storedByte (memLoad t.external (stackPtr initial - BitVec.ofNat 64 (form.finalMemory.buffer - if last then 56 else 0) + BitVec.ofNat 64 (8*(i/8))) 64)) := by
      apply Bytes.of_memLoad (n := 64)
      intro k hk
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact readable.mem _ (by omega)
    have byte := bytes (i % 8) (by omega)
    rw [words, BitVec.add_assoc, ← BitVec.ofNat_add, show 8*(i/8)+i%8=i by omega] at byte
    simpa [storedByte] using byte


theorem zero_stage [Bindings] {v : Variant} {form : Form} {initial s : RamState} {inputs : Array Input}
    {message : ByteArray} {hash : Array UInt64} (ctx : Context v initial inputs form)
    (input : Working v initial s message hash form) (rip : s.RIP = v.pc (Zero.offset false form v) form)
 :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ Working v initial t message hash form ∧ t.RIP = v.pc (Zero.nextOffset true form v) form ∧
      (⟨(stackPtr initial - BitVec.ofNat 64 form.finalMemory.buffer).toNat, 112⟩ : MemoryRegion).HasBytes
        t.external ⟨Array.replicate 112 0⟩ ∧
      AgreesExcept [.mem (stackPtr initial - BitVec.ofNat 64 form.finalMemory.buffer) 112, .rip] s t ∧
      MemoryWriteFrame s t #v[Stack.region initial form.stackBytes] ∧
      (¬ form.isTerminal → v.countValue form initial t = v.countValue form initial s) := by
  obtain ⟨fuelU, u, runU, stateU, ripU, bytesU, frameU⟩ := zero_half false ctx input rip
  obtain ⟨fuelT, t, runT, stateT, ripT, bytesT, frame⟩ := zero_half true ctx stateU ripU
  have widen (last : Bool) {u t : RamState}
      (frame : AgreesExcept [.mem (stackPtr initial - BitVec.ofNat 64 (form.finalMemory.buffer - if last then 56 else 0)) 56, .rip] u t) :
      AgreesExcept [.mem (stackPtr initial - BitVec.ofNat 64 form.finalMemory.buffer) 112, .rip] u t := by
    apply Common.Encoding.Serialize.agrees_of_footprint frame
    · intro c hc hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · simp [Component.isMem] at hm
      · simp
    · intro c hc a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · obtain ⟨j, hj, rfl⟩ := ha
        refine ⟨.mem (stackPtr initial - BitVec.ofNat 64 form.finalMemory.buffer) 112, by simp, (if last then 56 else 0)+j, by cases last <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> omega, ?_⟩
        have af := zero_address false input.rsp ((if last then 56 else 0)+j)
        simp only [Bool.false_eq_true, ↓reduceIte, Nat.sub_zero] at af
        rw [← zero_address last input.rsp j, ← af]
        congr 2
        simp only [Zero.base, Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Nat.add_assoc]
      · exact ha.elim
  have fullFrame : AgreesExcept [.mem (stackPtr initial - BitVec.ofNat 64 form.finalMemory.buffer) 112, .rip] s t := ((widen false frameU).trans (widen true frame)).mono (by simp)
  have stackFrame : MemoryWriteFrame s t #v[Stack.region initial form.stackBytes] := by
    apply fullFrame.memoryWriteFrame
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · refine ⟨Stack.region initial form.stackBytes, by simp, ?_⟩
      apply stackRegion_contains_sub ctx.stack.2.2.1 ?_ ?_ ha
      · have last := false
        zero_layout <;> decide +kernel
      · have last := false
        zero_layout <;> decide +kernel
    · exact ha.elim
  have countKept : ¬ form.isTerminal → v.countValue form initial t = v.countValue form initial s := by
    intro nonterminal
    cases form with
    | slices | digest => exact (nonterminal trivial).elim
    | reset stage =>
      have counts : ∀ stage : Fin 3, (v.traversal (.reset stage)).countReg = some 12 := by
        cases v <;> decide +kernel
      simp only [Variant.countValue, counts]
      exact fullFrame.read (n := 64) (r := 12) (by simp)
    | finalizeIntoReset second =>
      cases second
      · cases v
        · exact fullFrame.read (n := 64) (r := 12) (by simp)
        · exact fullFrame.read (n := 64) (r := 12) (by simp)
        · exact fullFrame.read (n := 64) (r := 15) (by simp)
        · exact fullFrame.read (n := 64) (r := 15) (by simp)
      · exact (nonterminal rfl).elim
    | traitFinalizeIntoReset second =>
      cases second
      · have target : memLoad t.external (stackPtr initial - 640) 64 =
            memLoad s.external (stackPtr initial - 640) 64 := by
          apply memLoad_congr
          intro i hi
          have byte : t.external[stackPtr initial - 640 + BitVec.ofNat 64 i]? =
              s.external[stackPtr initial - 640 + BitVec.ofNat 64 i]? := by
            apply fullFrame.byte
            intro c hc ha
            simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
            rcases hc with rfl | rfl
            · obtain ⟨j, hj, eq⟩ := ha
              apply OffsetsApart.ne (c₁ := -392) (len₁ := 112) (c₂ := -640) (len₂ := 8)
                (by unfold OffsetsApart; decide +kernel) (stackPtr initial) hj hi (by decide)
              simpa only [Form.finalMemory, ResetLayout.cloneMemory, BitVec.sub_eq_add_neg,
                BitVec.ofNat_eq_ofNat] using eq.symm
            · exact ha.elim
          exact congrArg (fun x : Option UInt8 => x.getD 0) byte
        cases v <;> exact target
      · exact (nonterminal rfl).elim
  refine ⟨fuelU+fuelT, t, runU.trans runT, stateT, ripT, ⟨by simp [MemoryRegion.HasLength, ByteArray.size], ?_⟩, fullFrame, stackFrame, countKept⟩
  intro i
  have hi : i.val < 112 := by simpa only [ByteArray.size, Array.size_replicate] using i.isLt
  change t.external[BitVec.ofNat 64 ((stackPtr initial - BitVec.ofNat 64 form.finalMemory.buffer).toNat + i.val)]? = _
  rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have byte : t.external[stackPtr initial - BitVec.ofNat 64 form.finalMemory.buffer + BitVec.ofNat 64 i.val]? = some 0 := by
    by_cases first : i.val < 56
    · rw [frame.byte (x := stackPtr initial - BitVec.ofNat 64 form.finalMemory.buffer + BitVec.ofNat 64 i.val) ?_]
      · exact bytesU i.val first
      · intro c hc ha
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl
        · obtain ⟨j, hj, he⟩ := ha
          exact OffsetsApart.ne (c₁ := -BitVec.ofNat 64 (form.finalMemory.buffer-56)) (len₁ := 56) (c₂ := -BitVec.ofNat 64 form.finalMemory.buffer) (len₂ := 56)
            (by have last := true; zero_layout <;> unfold OffsetsApart <;> decide +kernel) (stackPtr initial) hj first (by decide)
            (by simpa only [Form.frameBytes, Zero.base, ↓reduceIte, Nat.reduceSub, BitVec.sub_eq_add_neg,
              BitVec.ofNat_eq_ofNat] using he.symm)
        · exact ha.elim
    · have byte := bytesT (i.val - 56) (by omega)
      have address : stackPtr initial - BitVec.ofNat 64 form.finalMemory.buffer + BitVec.ofNat 64 i.val =
          stackPtr initial - BitVec.ofNat 64 (form.finalMemory.buffer-56) + BitVec.ofNat 64 (i.val-56) := by
        have af := zero_address false input.rsp i.val
        simp only [Bool.false_eq_true, ↓reduceIte, Nat.sub_zero] at af
        have addrTrue := zero_address true input.rsp (i.val-56)
        simp only [↓reduceIte] at addrTrue
        rw [← af, ← addrTrue]
        congr 2
        simp only [Zero.base, Bool.false_eq_true, ↓reduceIte, Nat.add_zero]
        omega
      rw [address]
      exact byte
  simpa only [ByteArray.getElem_eq_getElem_data, Array.getElem_replicate] using byte

theorem zero [Bindings] {v : Variant} {form : Form} {initial s : RamState} {inputs : Array Input}
    {message : ByteArray} {hash : Array UInt64} (ctx : Context v initial inputs form)
    (input : Working v initial s message hash form) (rip : s.RIP = v.pc (Zero.offset false form) form)
    (eligible : form = .slices ∨ form = .digest := by first | assumption | simp) :
    ∃ t, Working v initial t message hash form ∧ t.RIP = v.pc (Zero.nextOffset true form) form ∧
      (⟨(stackPtr initial - 600).toNat, 112⟩ : MemoryRegion).HasBytes
        t.external ⟨Array.replicate 112 0⟩ := by
  obtain ⟨_, t, _, state, ripT, bytes, _, _, _⟩ := zero_stage ctx input (by
    rcases eligible with rfl | rfl <;> exact rip)
  refine ⟨t, state, ?_, ?_⟩
  · rcases eligible with rfl | rfl <;> exact ripT
  · rcases eligible with rfl | rfl <;> exact bytes

end Sha2.Proofs.Wrapper512.Hash.Finalize
