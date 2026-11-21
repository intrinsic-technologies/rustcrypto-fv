import Base16ct.Proofs.EncodeStr.Lower.Machine.Control
import Base16ct.Proofs.EncodeStr.Lower.Machine.Start
import Base16ct.Proofs.EncodeStr.Lower.Machine.Preservation
import Base16ct.Proofs.EncodeStr.Lower.Machine.ByteArithmetic

namespace Base16ct.Proofs.EncodeStr.Lower

open Base16ct.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure EncoderState [Bindings] (initial : RamState) (input : List UInt8)
    (capacity : Nat) (s : RamState) : Prop extends MachineInvariant initial (if 2 * input.length ≤ capacity then 2 * input.length else 0) s where
  rsp : stackPtr s = stackPtr initial - 32
  resultPointer : (Operand.reg 0 : Operand 64).read s = stackPtr initial - 24
  inputPointer : (Operand.reg 6 : Operand 64).read s = initial.regValue .rdi
  inputLength : (Operand.reg 2 : Operand 64).read s = BitVec.ofNat 64 input.length
  outputPointer : (Operand.reg 1 : Operand 64).read s = initial.regValue .rcx
  outputLength : (Operand.reg 7 : Operand 64).read s = BitVec.ofNat 64 (2 * input.length)
  innerReturn : (Operand.mem (stackPtr initial - 32) : Operand 64).read s = 0x100196
  savedRbx : (Operand.mem (stackPtr initial - 8) : Operand 64).read s = initial.regValue .rbx
  lengthPointer : (Operand.reg 3 : Operand 64).read s = initial.regValue .rdx

theorem validCall_length_bounds {initial : RamState} {input : List UInt8} {capacity : Nat}
    (hCall : ValidCall base16ctLowerEncodeStr initial input.toByteArray capacity (2 * input.length) (2 * input.length ≤ capacity)) :
    input.length < 2 ^ 32 ∧ capacity < 2 ^ 32 := by
  have hi := hCall.inputInMemory.2.1
  have ho := hCall.outputInMemory.2.1
  change (initial.regValue .rdi).toNat + input.toByteArray.size < 2 ^ 32 at hi
  rw [List.size_toByteArray] at hi
  change (initial.regValue .rcx).toNat + capacity < 2 ^ 32 at ho
  omega

theorem capacity_checked [Bindings] {initial s : RamState} {input : List UInt8} {capacity : Nat}
    (hCall : ValidCall base16ctLowerEncodeStr initial input.toByteArray capacity (2 * input.length) (2 * input.length ≤ capacity))
    (hOutside : ¬ InProgram (returnBoundary initial).rip)
    (h : SubroutinePre initial input capacity s) :
    ∃ t, Advances (returnBoundary initial) 4 s t ∧ EncoderState initial input capacity t ∧
      t.RIP = if 2 * input.length ≤ capacity then 0x1004b8 else 0x1004ac := by
  obtain ⟨t, ha, hr, _, he⟩ := capacity_check_run hOutside h.ready h.code h.rip
  have hm := h.toMachineInvariant.of_agreesExcept_noMem he.agrees hr
    (by simp [PreservesCalleeSaved, capacityCheckEffect, Effect.components])
    (by simp [capacityCheckEffect, Effect.components, Component.isMem])
    (by simp [capacityCheckEffect, Effect.components])
  have hlen : (BitVec.ofNat 64 input.length).toNat = input.length := by
    have hb := (validCall_length_bounds hCall).1
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show input.length < 2 ^ 64 by omega)]
  have hcap : (BitVec.ofNat 64 capacity).toNat = capacity := by
    have hb := (validCall_length_bounds hCall).2
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show capacity < 2 ^ 64 by omega)]
  have hdouble : (Operand.reg 2 : Operand 64).read s + (Operand.reg 2 : Operand 64).read s =
      BitVec.ofNat 64 (2 * input.length) := by
    rw [h.inputLength, ← BitVec.ofNat_add]
    congr 1
    omega
  have hdoubleNat : ((Operand.reg 2 : Operand 64).read s +
      (Operand.reg 2 : Operand 64).read s).toNat = 2 * input.length := by
    rw [h.inputLength, lengthDouble_toNat _ (by rw [hlen]; exact (validCall_length_bounds hCall).1), hlen]
  refine ⟨t, ha, ⟨hm, ?_, he.writes.1.trans h.resultPointer, ?_, ?_, ?_,
    he.writes.2.trans hdouble, ?_, ?_, ?_⟩, ?_⟩
  · exact (he.agrees.read (n := 64) (r := 4)
      (by simp [capacityCheckEffect, Effect.components])).trans h.rsp
  · exact (he.agrees.read (n := 64) (r := 6)
      (by simp [capacityCheckEffect, Effect.components])).trans h.inputPointer
  · exact (he.agrees.read (n := 64) (r := 2)
      (by simp [capacityCheckEffect, Effect.components])).trans h.inputLength
  · exact (he.agrees.read (n := 64) (r := 1)
      (by simp [capacityCheckEffect, Effect.components])).trans h.outputPointer
  · exact (read_mem_of_agreesExcept he.agrees _ 64
      (by simp [capacityCheckEffect, Effect.components, Component.Covers])).trans h.innerReturn
  · exact (read_mem_of_agreesExcept he.agrees _ 64
      (by simp [capacityCheckEffect, Effect.components, Component.Covers])).trans h.savedRbx
  · exact (he.agrees.read (n := 64) (r := 3)
      (by simp [capacityCheckEffect, Effect.components])).trans h.lengthPointer
  · simpa only [capacityCheckEffect, hdoubleNat, h.outputCapacity, hcap] using he.rip

theorem masked_state [Bindings] {initial s : RamState} {input : List UInt8} {capacity : Nat}
    (hCall : ValidCall base16ctLowerEncodeStr initial input.toByteArray capacity (2 * input.length) (2 * input.length ≤ capacity))
    (hOutside : ¬ InProgram (returnBoundary initial).rip)
    (h : EncoderState initial input capacity s) (hRip : s.RIP = 0x1004b8) :
    ∃ t, Advances (returnBoundary initial) 3 s t ∧ EncoderState initial input capacity t ∧
      t.RIP = if input.length = 0 then 0x100521 else 0x1004c7 := by
  obtain ⟨t, ha, hr, _, he⟩ := mask_branch_run hOutside h.ready h.code hRip
  have hm := h.toMachineInvariant.of_agreesExcept_noMem he.agrees hr
    (by simp [PreservesCalleeSaved, maskBranchEffect, Effect.components])
    (by simp [maskBranchEffect, Effect.components, Component.isMem])
    (by simp [maskBranchEffect, Effect.components])
  have hlen : (BitVec.ofNat 64 input.length).toNat = input.length := by
    have hb := (validCall_length_bounds hCall).1
    simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show input.length < 2 ^ 64 by omega)]
  have hmask : ((Operand.reg 2 : Operand 64).read s &&& 0x3fffffffffffffff) =
      BitVec.ofNat 64 input.length := by
    rw [h.inputLength]
    exact lengthMask_eq _ (by rw [hlen]; exact (validCall_length_bounds hCall).1)
  have hzero : (BitVec.ofNat 64 input.length = 0) ↔ input.length = 0 := by
    constructor
    · intro hz
      have hn := congrArg BitVec.toNat hz
      simpa [hlen] using hn
    · intro hz
      rw [hz]
      rfl
  refine ⟨t, ha, ⟨hm, ?_, ?_, ?_, he.writes.2.trans hmask, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · exact (he.agrees.read (n := 64) (r := 4)
      (by simp [maskBranchEffect, Effect.components])).trans h.rsp
  · exact (he.agrees.read (n := 64) (r := 0)
      (by simp [maskBranchEffect, Effect.components])).trans h.resultPointer
  · exact (he.agrees.read (n := 64) (r := 6)
      (by simp [maskBranchEffect, Effect.components])).trans h.inputPointer
  · exact (he.agrees.read (n := 64) (r := 1)
      (by simp [maskBranchEffect, Effect.components])).trans h.outputPointer
  · exact (he.agrees.read (n := 64) (r := 7)
      (by simp [maskBranchEffect, Effect.components])).trans h.outputLength
  · exact (read_mem_of_agreesExcept he.agrees _ 64
      (by simp [maskBranchEffect, Effect.components, Component.Covers])).trans h.innerReturn
  · exact (read_mem_of_agreesExcept he.agrees _ 64
      (by simp [maskBranchEffect, Effect.components, Component.Covers])).trans h.savedRbx
  · exact (he.agrees.read (n := 64) (r := 3)
      (by simp [maskBranchEffect, Effect.components])).trans h.lengthPointer
  · simpa only [maskBranchEffect, hmask, hzero] using he.rip

theorem loop_initialized [Bindings] {initial s : RamState} {input : List UInt8} {capacity : Nat}
    (hOutside : ¬ InProgram (returnBoundary initial).rip)
    (h : EncoderState initial input capacity s) (hRip : s.RIP = 0x1004c7)
    (hNonempty : 0 < input.length) :
    ∃ t, Advances (returnBoundary initial) 2 s t ∧ LoopInvariant initial input capacity 0 t := by
  obtain ⟨t, ha, hr, _, he⟩ := index_init_run hOutside h.ready h.code hRip
  have hm := h.toMachineInvariant.of_agreesExcept_noMem he.agrees hr
    (by simp [PreservesCalleeSaved, indexInitEffect, Effect.components])
    (by simp [indexInitEffect, Effect.components, Component.isMem])
    (by simp [indexInitEffect, Effect.components])
  refine ⟨t, ha, ⟨hm, ?_, ?_, ?_, ?_, ?_, ?_, ?_, he.writes, ?_, ?_, ?_, ?_⟩⟩
  · simpa only [indexInitEffect, ite_eq_left hNonempty] using he.rip
  · exact (he.agrees.read (n := 64) (r := 4)
      (by simp [indexInitEffect, Effect.components])).trans h.rsp
  · exact (he.agrees.read (n := 64) (r := 0)
      (by simp [indexInitEffect, Effect.components])).trans h.resultPointer
  · exact (he.agrees.read (n := 64) (r := 6)
      (by simp [indexInitEffect, Effect.components])).trans h.inputPointer
  · exact (he.agrees.read (n := 64) (r := 2)
      (by simp [indexInitEffect, Effect.components])).trans h.inputLength
  · exact (he.agrees.read (n := 64) (r := 1)
      (by simp [indexInitEffect, Effect.components])).trans h.outputPointer
  · exact (he.agrees.read (n := 64) (r := 7)
      (by simp [indexInitEffect, Effect.components])).trans h.outputLength
  · exact (read_mem_of_agreesExcept he.agrees _ 64
      (by simp [indexInitEffect, Effect.components, Component.Covers])).trans h.innerReturn
  · rfl
  · exact (read_mem_of_agreesExcept he.agrees _ 64
      (by simp [indexInitEffect, Effect.components, Component.Covers])).trans h.savedRbx
  · exact (he.agrees.read (n := 64) (r := 3)
      (by simp [indexInitEffect, Effect.components])).trans h.lengthPointer

theorem subroutine_prepare [Bindings] {initial s : RamState} {input : List UInt8} {capacity : Nat}
    (hCall : ValidCall base16ctLowerEncodeStr initial input.toByteArray capacity (2 * input.length) (2 * input.length ≤ capacity))
    (hOutside : ¬ InProgram (returnBoundary initial).rip)
    (h : SubroutinePre initial input capacity s) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧
      (CalleeExitPre initial input capacity t ∨
        (2 * input.length ≤ capacity ∧ LoopInvariant initial input capacity 0 t)) := by
  obtain ⟨u, ha, hu, hRip⟩ := capacity_checked hCall hOutside h
  by_cases hFits : 2 * input.length ≤ capacity
  · have hEntry : u.RIP = 0x1004b8 := by simpa only [ite_eq_left hFits] using hRip
    obtain ⟨v, hb, hv, hRip'⟩ := masked_state hCall hOutside hu hEntry
    by_cases hEmpty : input.length = 0
    · refine ⟨7, v, ha.trans hb, .inl ⟨hv.toMachineInvariant, ?_, hv.rsp,
        hv.resultPointer, hv.innerReturn, fun _ => ⟨hv.outputPointer, hv.outputLength, ?_⟩, hv.savedRbx, hv.lengthPointer⟩⟩
      · simpa only [ite_eq_left hFits, ite_eq_left hEmpty] using hRip'
      · have he : input = [] := List.length_eq_zero_iff.mp hEmpty
        subst input
        rfl
    · have hEntry' : v.RIP = 0x1004c7 := by simpa only [ite_eq_right hEmpty] using hRip'
      obtain ⟨t, hc, ht⟩ := loop_initialized hOutside hv hEntry' (by omega)
      exact ⟨9, t, (ha.trans hb).trans hc, .inr ⟨hFits, ht⟩⟩
  · exact ⟨4, u, ha, .inl ⟨hu.toMachineInvariant, by simpa only [ite_eq_right hFits] using hRip,
      hu.rsp, hu.resultPointer, hu.innerReturn, fun h => (hFits h).elim, hu.savedRbx, hu.lengthPointer⟩⟩

theorem loop_finished [Bindings] {initial s : RamState} {input : List UInt8} {capacity : Nat}
    (hFits : 2 * input.length ≤ capacity)
    (h : LoopInvariant initial input capacity input.length s) :
    CalleeExitPre initial input capacity s := by
  refine ⟨h.toMachineInvariant, ?_, h.rsp, h.resultPointer, h.innerReturn,
    fun _ => ⟨h.outputPointer, h.outputLength, ?_⟩, h.savedRbx, h.lengthPointer⟩
  · simpa only [Nat.lt_irrefl, ite_false, ite_eq_left hFits] using h.rip
  · simpa only [List.take_length] using h.output

end Base16ct.Proofs.EncodeStr.Lower
