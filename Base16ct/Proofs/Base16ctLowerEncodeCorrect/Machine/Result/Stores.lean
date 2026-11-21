import Base16ct.Proofs.Base16ctLowerEncodeCorrect.Machine.Geometry
import Base16ct.Proofs.Base16ctLowerEncodeCorrect.Machine.Preservation
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.Call.Triple

namespace Base16ct.Proofs.LowerEncode

open Base16ct.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem result_store_invariant [Bindings] {initial s t : RamState}
    {input : List UInt8} {capacity written offset len : Nat}
    (call : ValidCall base16ctLowerEncode initial input.toByteArray capacity (2 * input.length) (2 * input.length ≤ capacity))
    (state : MachineInvariant initial written s)
    (low : offset ≤ 32) (high : len ≤ offset)
    (ready : ReadyToStep t)
    (frame : AgreesExcept [.mem (stackPtr initial - BitVec.ofNat 64 offset) len, .rip] s t) :
    MachineInvariant initial written t := by
  apply state.of_agreesExcept frame ready
  · simp [PreservesCalleeSaved]
  · exact stack_store_within call low (by omega)
  · intro c hc a b hab covers
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · obtain ⟨i, hi, he⟩ := covers
      exact stack_avoids_program call low (by omega) i hi (he ▸ ⟨b, hab⟩)
    · exact covers.elim
  · intro i hi c hc covers
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · obtain ⟨j, hj, he⟩ := covers
      exact stack_return_apart call low high j hj i hi he.symm
    · exact covers.elim

theorem result_store_read_mem {s t : RamState} {writeAddress readAddress : BitVec 64}
    {len n : Nat} (frame : AgreesExcept [.mem writeAddress len, .rip] s t)
    (apart : RangeApart writeAddress len readAddress (n / 8)) :
    (Operand.mem readAddress : Operand n).read t =
      (Operand.mem readAddress : Operand n).read s := by
  apply read_mem_of_agreesExcept frame
  intro i hi c hc covers
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · obtain ⟨j, hj, he⟩ := covers
    exact apart j hj i hi he.symm
  · exact covers.elim

theorem result_store_step [Bindings] {initial s : RamState}
    {input : List UInt8} {capacity written offset n pc : Nat} {bytes : List UInt8}
    {address : RamState → BitVec 64} {value : RamState → BitVec n}
    (call : ValidCall base16ctLowerEncode initial input.toByteArray capacity (2 * input.length) (2 * input.length ≤ capacity))
    (state : MachineInvariant initial written s)
    (outside : ¬ InProgram (returnBoundary initial).rip)
    (low : offset ≤ 32) (high : n / 8 ≤ offset)
    (writable : MemWritable s (stackPtr initial - BitVec.ofNat 64 offset) (n / 8))
    (rip : s.RIP = Extracted.textAddress + BitVec.ofNat 64 pc)
    (addr : address s = stackPtr initial - BitVec.ofNat 64 offset)
    (code : Extracted.textBytes.toListFrom pc bytes.length = bytes)
    (bound : pc + bytes.length < Extracted.textBytes.size)
    (step : StepEffect
      (StorePre (Extracted.textAddress + BitVec.ofNat 64 pc) bytes.length address (n / 8))
      (codeRange (Extracted.textAddress + BitVec.ofNat 64 pc) bytes)
      (storeEffect (Extracted.textAddress + BitVec.ofNat 64 pc) bytes.length address value)) :
    ∃ t, Advances (returnBoundary initial) 1 s t ∧
      MachineInvariant initial written t ∧
      t.RIP = Extracted.textAddress + BitVec.ofNat 64 (pc + bytes.length) ∧
      (Operand.mem (stackPtr initial - BitVec.ofNat 64 offset) : Operand n).read t = value s ∧
      AgreesExcept [.mem (stackPtr initial - BitVec.ofNat 64 offset) (n / 8), .rip] s t := by
  have bytesIn : CodeIn (codeRange (Extracted.textAddress + BitVec.ofNat 64 pc) bytes) s := by
    rw [← code]
    exact program_text_slice state.code pc bytes.length (by omega)
  obtain ⟨t, run, ready, effect⟩ := step.advances state.ready bytesIn
    ⟨rip, by rw [addr]; exact writable,
      by rw [addr]; exact stack_codeApart call low (by omega) (by omega)⟩
    (by
      change Extracted.textAddress + BitVec.ofNat 64 pc + BitVec.ofNat 64 bytes.length ≠ _
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact text_address_ne_return outside _ bound)
  have frame : AgreesExcept
      [.mem (stackPtr initial - BitVec.ofNat 64 offset) (n / 8), .rip] s t := by
    simpa only [storeEffect_components, addr] using effect.agrees
  refine ⟨t, run, result_store_invariant call state low high ready frame, ?_, ?_, frame⟩
  · simpa only [storeEffect, BitVec.ofNat_add, BitVec.add_assoc] using effect.rip
  · simpa only [storeEffect, Write.AllHold, addr] using effect.writes

theorem result_ret_step [Bindings] {initial s : RamState} {input : List UInt8}
    {capacity written pc : Nat} (call : ValidCall base16ctLowerEncode initial input.toByteArray capacity (2 * input.length) (2 * input.length ≤ capacity))
    (state : MachineInvariant initial written s)
    (outside : ¬ InProgram (returnBoundary initial).rip)
    (rip : s.RIP = Extracted.textAddress + BitVec.ofNat 64 pc)
    (rsp : stackPtr s = stackPtr initial - 32)
    (inner : (Operand.mem (stackPtr initial - 32) : Operand 64).read s = 0x100156)
    (code : Extracted.textBytes.toListFrom pc 1 = [0xc3])
    (bound : pc + 1 ≤ Extracted.textBytes.size) :
    ∃ t, Advances (returnBoundary initial) 1 s t ∧
      MachineInvariant initial written t ∧ t.RIP = 0x100156 ∧
      stackPtr t = stackPtr initial - 24 ∧ t.external = s.external ∧
      (Operand.reg 3 : Operand 64).read t = (Operand.reg 3 : Operand 64).read s := by
  have top : stackTop s = 0x100156 := by
    rw [stackTop, rsp]
    exact inner
  have bytesIn : CodeIn (codeRange (Extracted.textAddress + BitVec.ofNat 64 pc) [0xc3]) s := by
    rw [← code]
    exact program_text_slice state.code pc 1 bound
  obtain ⟨t, run, ready, effect⟩ := (ret_effect_step _).advances state.ready bytesIn
    ⟨⟨rip, by rw [rsp]; exact stack_readable call state (by decide) (by decide)⟩,
      by rw [top]; decide +kernel⟩
    (by change stackTop s ≠ _; rw [top];
        exact text_address_ne_return outside 0x156 (by decide +kernel))
  refine ⟨t, run, state.of_agreesExcept_noMem effect.agrees ready
    (by simp [PreservesCalleeSaved]) (by simp [Component.isMem]),
    effect.rip.trans top, ?_, effect.agrees.external (by simp [Component.Covers]),
    effect.agrees.read (by simp)⟩
  change stackPtr t = _
  have hs : stackPtr t = stackPtr s + 8 := effect.writes
  rw [hs, rsp]
  simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
  rfl

end Base16ct.Proofs.LowerEncode
