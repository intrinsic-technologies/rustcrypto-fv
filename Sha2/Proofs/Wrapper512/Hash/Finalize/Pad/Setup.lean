import Sha2.Proofs.Common.Machine.CallMemory
import Sha2.Proofs.Wrapper512.Hash.Finalize.Pad.Load
import Sha2.Proofs.Wrapper512.Hash.Finalize.Pad.FillSetup
import Sha2.Proofs.Wrapper512.Hash.Finalize.Pad.Fill

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Hash.Finalize.Pad

open Sha2.Spec Sha2.Proofs.Program Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.SHA512

structure FillReady [Bindings] (v : Variant) (initial s : RamState) (message : ByteArray) (form : Form := .slices)
    : Prop
    extends Working v initial s message (compressBlocks v.initialHash message) form where
  rip : s.RIP = (v.pc (fillOffset v form) form)
  tailBytes : (⟨(stackPtr initial - BitVec.ofNat 64 form.finalMemory.buffer).toNat, message.size % 128⟩ : MemoryRegion).HasBytes
    s.external (remainderBytes message)
  marker : s.external[stackPtr initial - BitVec.ofNat 64 form.finalMemory.buffer + BitVec.ofNat 64 (message.size % 128)]? = some 128
  paddingLength : s.regValue (paddingRegister v form) = BitVec.ofNat 64 (127 - message.size % 128)
  destination : s.regValue .rdi = stackPtr initial - BitVec.ofNat 64 (form.finalMemory.hash + (127 - message.size % 128))
  zero : s.regValue .rsi = 0
  count : s.regValue .rdx = BitVec.ofNat 64 (127 - message.size % 128)


set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem marker_offsets (f : Form) (n : Fin 128) : f.finalMemory.buffer - n.val ≤ f.stackBytes ∧
        49 ≤ f.finalMemory.buffer - n.val ∧
        (match f with
        | .slices | .digest => 625 ≤ f.finalMemory.buffer - n.val ∨ f.finalMemory.buffer - n.val ≤ 600
        | _ => ∀ slot ∈ f.metadataSlots, OffsetsApart (-BitVec.ofNat 64 (f.finalMemory.buffer - n.val)) 1 (-BitVec.ofNat 64 slot) 8) := by
  cases f <;> simp only [Form.metadataSlots, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, OffsetsApart] <;> decide +revert +kernel

set_option maxHeartbeats 2000000 in
theorem setup_local [Bindings] {v : Variant} {form : Form} {initial s : RamState}
    {inputs : Array Input} {message : ByteArray} (ctx : Context v initial inputs form)
    (input : Loaded v initial s message form) (eligible : form.canFinalize) :
    ∃ t, (∃ fuel, Advances (returnBoundary initial) fuel s t) ∧
      FillReady v initial t message form ∧
      AgreesExcept ((FillSetup.effect v s form).components) s t ∧
      MemoryWriteFrame s t #v[Stack.region initial form.stackBytes] ∧
      (¬ form.isTerminal → v.countValue form initial t = v.countValue form initial s) := by
  have tailBound : message.size % 128 < 128 := Nat.mod_lt _ (by decide)
  have layout : 64 ≤ form.finalMemory.hash ∧
      form.finalMemory.hash + 128 = form.finalMemory.buffer ∧
      form.finalMemory.buffer ≤ form.frameBytes ∧ form.frameBytes < 2^64 := by
    cases form with
    | slices | digest => decide +kernel
    | reset _ => change 64 ≤ 296 ∧ 296+128=424 ∧ 424≤424 ∧ 424<2^64; decide +kernel
    | finalizeIntoReset b | traitFinalizeIntoReset b => cases b <;> decide +kernel
  have tailRead : (Operand.reg (FillSetup.tailIndex (FillSetup.encoding v form)) : Operand 64).read s =
      s.regValue (tailRegister v form) := by
    cases form with
    | slices | digest => rfl
    | reset stage => by_cases h : stage.val = 2 <;> simp only [FillSetup.encoding, tailRegister, h, ite_true, ite_false] <;> rfl
    | finalizeIntoReset b | traitFinalizeIntoReset b => cases b <;> cases v <;> rfl
  have padRead : (Operand.reg (FillSetup.paddingIndex (FillSetup.encoding v form)) : Operand 64).read s =
      s.regValue (paddingRegister v form) := by
    cases form with
    | slices | digest => rfl
    | reset stage => by_cases h : stage.val = 2 <;> simp only [FillSetup.encoding, paddingRegister, h, ite_true, ite_false] <;> rfl
    | finalizeIntoReset b | traitFinalizeIntoReset b => cases b <;> cases v <;> rfl
  have displacement : form.frameBytes = form.finalMemory.buffer + FillSetup.displacement (FillSetup.encoding v form) := by
    cases form with
    | slices | digest => rfl
    | reset stage => by_cases h : stage.val = 2 <;> simp only [FillSetup.encoding, h, ite_true, ite_false] <;> rfl
    | finalizeIntoReset b | traitFinalizeIntoReset b => cases b <;> cases v <;> rfl
  have address' : rspOf s + (Operand.reg (FillSetup.tailIndex (FillSetup.encoding v form)) : Operand 64).read s +
      BitVec.ofNat 64 (FillSetup.displacement (FillSetup.encoding v form)) =
      stackPtr initial - BitVec.ofNat 64 form.finalMemory.buffer + BitVec.ofNat 64 (message.size % 128) := by
    rw [tailRead]
    change stackPtr s + s.regValue (tailRegister v form) + _ = _
    rw [input.rsp, input.tailLength, displacement, BitVec.ofNat_add]
    simp only [BitVec.sub_eq_add_neg, BitVec.neg_add]
    rw [show stackPtr initial + (-BitVec.ofNat 64 form.finalMemory.buffer + -BitVec.ofNat 64 (FillSetup.displacement (FillSetup.encoding v form))) + BitVec.ofNat 64 (message.size % 128) + BitVec.ofNat 64 (FillSetup.displacement (FillSetup.encoding v form)) =
      (stackPtr initial + -BitVec.ofNat 64 form.finalMemory.buffer + BitVec.ofNat 64 (message.size % 128)) + (-BitVec.ofNat 64 (FillSetup.displacement (FillSetup.encoding v form)) + BitVec.ofNat 64 (FillSetup.displacement (FillSetup.encoding v form))) by ac_rfl]
    simp only [BitVec.add_left_neg, BitVec.add_zero]
  have address : rspOf s + (Operand.reg (FillSetup.tailIndex (FillSetup.encoding v form)) : Operand 64).read s +
      BitVec.ofNat 64 (FillSetup.displacement (FillSetup.encoding v form)) =
      stackPtr initial - BitVec.ofNat 64 (form.finalMemory.buffer - message.size % 128) := by
    rw [address', ← BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)]
    simp only [BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.neg_neg, BitVec.add_assoc]
  have offsets := marker_offsets form ⟨message.size % 128, tailBound⟩
  have pre : FillSetup.Pre v s form :=
    ⟨input.rip, address ▸ Machine.Initialize.stack_writable1 ctx input.toState offsets.1 (by omega),
      address ▸ Machine.Stages.stack_slot_codeApart ctx offsets.1 (by omega)
        (FillSetup.code_bound v form)⟩
  obtain ⟨fuel, t, run, ready, _, effect⟩ := FillSetup.run (returnBoundary initial)
    ((valid_return_boundary ctx.machine ctx.stack ctx.returnAddress).2.2) s
    (supportedMachine_readyToStep input.machine) (FillSetup.code input.loaded eligible) pre
  have frame := effect.agrees
  have localWrite : Absorb.LocalWrites initial (FillSetup.effect v s form).components form := by
    intro c hc a ha
    simp only [FillSetup.effect, FillSetup.effectAt, Effect.components, List.map_cons, List.map_nil,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false, Write.component, Operand.component] at hc
    rcases hc with ((rfl | rfl | rfl | rfl) | rfl) | rfl <;> try exact ha.elim
    rw [address] at ha
    have h := Absorb.local_memory offsets.1 offsets.2.1 (by cases form <;> exact offsets.2.2) a ha
    cases form <;> exact h
  have preserved := Absorb.preserved_of_agrees ctx input.toPreserved run ready frame localWrite
    (by simp [FillSetup.effect, FillSetup.effectAt, Effect.components])
    (by simp [FillSetup.effect, FillSetup.effectAt, Effect.components])
    (by intro hd; simp [FillSetup.effect, FillSetup.effectAt, Effect.components])
    (by intro hf; left; cases v <;> simp [FillSetup.effect, FillSetup.effectAt, Effect.components])
  have kept (r : Syntax.Reg) (hr : r ∈ ([.rbx, .rbp, .r12, .r13, .r14, .r15] : List Syntax.Reg)) : t.regValue r = s.regValue r := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact frame.read (n := 64) (r := 3) (by simp [FillSetup.effect, FillSetup.effectAt, Effect.components])
    · exact frame.read (n := 64) (r := 5) (by simp [FillSetup.effect, FillSetup.effectAt, Effect.components])
    · exact frame.read (n := 64) (r := 12) (by simp [FillSetup.effect, FillSetup.effectAt, Effect.components])
    · exact frame.read (n := 64) (r := 13) (by simp [FillSetup.effect, FillSetup.effectAt, Effect.components])
    · exact frame.read (n := 64) (r := 14) (by simp [FillSetup.effect, FillSetup.effectAt, Effect.components])
    · exact frame.read (n := 64) (r := 15) (by simp [FillSetup.effect, FillSetup.effectAt, Effect.components])
  have stackFrame : MemoryWriteFrame s t #v[Stack.region initial form.stackBytes] :=
    frame.memoryWriteFrame (localWrite.stack ctx)
  have countKept : ¬ form.isTerminal → v.countValue form initial t = v.countValue form initial s := by
    intro nonterminal
    cases form with
    | slices | digest => exact (nonterminal trivial).elim
    | reset stage =>
      have stages : stage = 0 ∨ stage = 1 ∨ stage = 2 := by omega
      rcases stages with rfl | rfl | rfl
      · exact (eligible rfl).elim
      · cases v <;> exact kept .r12 (by simp)
      · exact (nonterminal rfl).elim
    | finalizeIntoReset second =>
      cases second
      · cases v <;> first | exact kept .r12 (by simp) | exact kept .r15 (by simp)
      · exact (nonterminal rfl).elim
    | traitFinalizeIntoReset second =>
      cases second
      · have target : memLoad t.external (stackPtr initial - 640) 64 =
            memLoad s.external (stackPtr initial - 640) 64 := by
          apply memLoad_congr
          intro i hi
          have byte : t.external[stackPtr initial - 640 + BitVec.ofNat 64 i]? =
              s.external[stackPtr initial - 640 + BitVec.ofNat 64 i]? := by
            apply frame.byte
            intro c hc ha
            simp only [FillSetup.effect, FillSetup.effectAt, Effect.components, List.map_cons, List.map_nil,
              List.mem_append, List.mem_cons, List.not_mem_nil, or_false, Write.component, Operand.component] at hc
            rcases hc with ((rfl | rfl | rfl | rfl) | rfl) | rfl <;> try exact ha.elim
            obtain ⟨j, hj, eq⟩ := ha
            rw [address] at eq
            have apartFact : ∀ n : Fin 128,
                OffsetsApart (-BitVec.ofNat 64 (392 - n.val)) 1 (-640) 8 := by unfold OffsetsApart; decide +kernel
            change stackPtr initial - 640 + BitVec.ofNat 64 i =
              stackPtr initial - BitVec.ofNat 64 (392 - message.size % 128) + BitVec.ofNat 64 j at eq
            apply OffsetsApart.ne (apartFact ⟨message.size % 128, tailBound⟩) (stackPtr initial) hj hi (by decide)
            simpa only [BitVec.sub_eq_add_neg] using eq.symm
          change (t.external[_]?).getD 0 = (s.external[_]?).getD 0
          rw [byte]
        cases v <;> exact target
      · exact (nonterminal rfl).elim
  have bytes (i : Nat) (hi : i < 208) (ne : i ≠ message.size % 128) :
      t.external[stackPtr initial - BitVec.ofNat 64 form.finalMemory.buffer + BitVec.ofNat 64 i]? =
        s.external[stackPtr initial - BitVec.ofNat 64 form.finalMemory.buffer + BitVec.ofNat 64 i]? := by
    apply frame.byte
    intro c hc ha
    simp only [FillSetup.effect, FillSetup.effectAt, Effect.components, List.map_cons, List.map_nil,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false, Write.component, Operand.component] at hc
    rcases hc with ((rfl | rfl | rfl | rfl) | rfl) | rfl <;> try exact ha.elim
    obtain ⟨j, hj, eq⟩ := ha
    have hj0 : j = 0 := by omega
    subst j
    rw [address', BitVec.add_zero] at eq
    have same := (BitVec.add_right_inj _).mp eq
    have natSame := congrArg BitVec.toNat same
    simp only [BitVec.toNat_ofNat] at natSame
    apply ne
    omega
  have writes : memLoad t.external (stackPtr initial - BitVec.ofNat 64 form.finalMemory.buffer + BitVec.ofNat 64 (message.size % 128)) 8 = 128 ∧
    t.regValue .rdi = (stackPtr initial - BitVec.ofNat 64 form.finalMemory.buffer + BitVec.ofNat 64 (message.size % 128)) + 1 ∧
    t.regValue .rsi = 0 ∧ t.regValue .rdx = s.regValue (paddingRegister v form) := by
    have h : memLoad t.external (rspOf s + (Operand.reg (FillSetup.tailIndex (FillSetup.encoding v form)) : Operand 64).read s + BitVec.ofNat 64 (FillSetup.displacement (FillSetup.encoding v form))) 8 = 128 ∧
        t.regValue .rdi = rspOf s + (Operand.reg (FillSetup.tailIndex (FillSetup.encoding v form)) : Operand 64).read s + BitVec.ofNat 64 (FillSetup.displacement (FillSetup.encoding v form) + 1) ∧
        t.regValue .rsi = 0 ∧ t.regValue .rdx = (Operand.reg (FillSetup.paddingIndex (FillSetup.encoding v form)) : Operand 64).read s := effect.writes
    rw [padRead, address'] at h
    simpa only [BitVec.ofNat_add, ← BitVec.add_assoc, address', BitVec.ofNat_eq_ofNat] using h
  refine ⟨t, ⟨fuel, run⟩, ⟨⟨⟨preserved, ?_, ?_⟩, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, writes.2.2.1,
    writes.2.2.2.trans input.paddingLength⟩, frame, stackFrame, countKept⟩
  · apply Absorb.hashState_of_bytes input.hashWords
    intro i hi
    have byte := bytes (128+i) (by omega) (by omega)
    rw [← layout.2.1] at byte
    simpa only [BitVec.ofNat_add, ← BitVec.sub_sub, ← BitVec.add_assoc,
      BitVec.sub_add_cancel, BitVec.ofNat_eq_ofNat] using byte
  · cases form with
    | slices | digest => exact (kept .r14 (by simp)).trans input.hashPointer
    | reset _ => trivial
    | finalizeIntoReset b =>
      cases b
      · trivial
      · exact (kept .rbx (by simp)).trans input.hashPointer
    | traitFinalizeIntoReset b =>
      cases b
      · exact ⟨(kept _ (by cases v <;> simp)).trans input.hashPointer.1,
          (kept _ (by cases v <;> simp)).trans input.hashPointer.2⟩
      · exact (kept .rbx (by simp)).trans input.hashPointer
  · exact (kept _ (by cases form <;> cases v <;> simp only [lowCountRegister] <;> (try split) <;> simp)).trans input.blocks
  · exact (kept _ (by cases form <;> cases v <;> simp only [highCountRegister] <;> (try split) <;> simp)).trans input.blocksHigh
  · exact (kept _ (by cases form <;> cases v <;> simp only [tailRegister] <;> (try split) <;> simp)).trans input.tailLength
  · simpa only [FillSetup.effect_rip] using effect.rip
  · refine ⟨input.tailBytes.1, ?_⟩
    intro i
    have hi : i.val < message.size % 128 := by simpa only [remainderBytes_size] using i.isLt
    change t.external[BitVec.ofNat 64 ((stackPtr initial - BitVec.ofNat 64 form.finalMemory.buffer).toNat + i.val)]? = _
    rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, bytes i.val (by omega) (by omega)]
    simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using input.tailBytes.2 i
  · have value := writes.1
    rw [memLoad_8] at value
    change ((t.external[stackPtr initial - BitVec.ofNat 64 form.finalMemory.buffer + BitVec.ofNat 64 (message.size % 128)]?).getD 0).toBitVec = 128 at value
    cases byte : t.external[stackPtr initial - BitVec.ofNat 64 form.finalMemory.buffer + BitVec.ofNat 64 (message.size % 128)]? with
    | none => rw [byte] at value; contradiction
    | some v =>
      simp only [byte, Option.getD_some] at value
      exact congrArg some (UInt8.eq_of_toBitVec_eq value)
  · exact (kept _ (by cases form <;> cases v <;> simp only [paddingRegister] <;> (try split) <;> simp)).trans input.paddingLength
  · rw [writes.2.1, ← address', address]
    have add : form.finalMemory.buffer - message.size % 128 = (form.finalMemory.hash + (127 - message.size % 128)) + 1 := by omega
    rw [add, BitVec.ofNat_add]
    simp only [← BitVec.sub_sub, BitVec.sub_add_cancel, BitVec.ofNat_eq_ofNat]

theorem setup [Bindings] {v : Variant} {form : Form} {initial s : RamState}
    {inputs : Array Input} {message : ByteArray} (ctx : Context v initial inputs form)
    (input : Loaded v initial s message form)
    (eligible : form = .slices ∨ form = .digest := by first | assumption | simp) :
    ∃ t, FillReady v initial t message form := by
  obtain ⟨t, _, ready, _⟩ := setup_local ctx input (by rcases eligible with rfl | rfl <;> trivial)
  exact ⟨t, ready⟩

end Sha2.Proofs.Wrapper512.Hash.Finalize.Pad
