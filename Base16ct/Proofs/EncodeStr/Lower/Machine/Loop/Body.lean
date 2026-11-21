import Base16ct.Proofs.EncodeStr.Lower.Machine.Loop.Compute
import Base16ct.Proofs.EncodeStr.Lower.Machine.Geometry
import Base16ct.Proofs.EncodeStr.Lower.Machine.Preservation
import Base16ct.Proofs.EncodeStr.Lower.Machine.Instructions.ByteStore
import X86Proofs.Instructions.Movzx.Generated.RM8.Triple

namespace Base16ct.Proofs.EncodeStr.Lower

open Base16ct.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

private theorem loop_output_address {initial s : RamState} {index : Nat}
    (pointer : (Operand.reg 1 : Operand 64).read s = initial.regValue .rcx)
    (value : (Operand.reg 8 : Operand 64).read s = BitVec.ofNat 64 index)
    (next : BitVec 64) :
    AddrMode.addr (.sib 1 (some 8) 1 .none) s next =
      initial.regValue .rcx + BitVec.ofNat 64 (2 * index) := by
  change (Operand.reg 1 : Operand 64).read s +
    ((Operand.reg 8 : Operand 64).read s <<< 1) + 0#64 = _
  rw [pointer, value, BitVec.add_zero]
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft, Nat.shiftLeft_eq, Nat.mul_mod, Nat.mul_comm]

private theorem loop_output_next_address {initial s : RamState} {index : Nat}
    (pointer : (Operand.reg 1 : Operand 64).read s = initial.regValue .rcx)
    (value : (Operand.reg 8 : Operand 64).read s = BitVec.ofNat 64 index)
    (next : BitVec 64) :
    AddrMode.addr (.sib 1 (some 8) 1 (.d8 1)) s next =
      initial.regValue .rcx + BitVec.ofNat 64 (2 * index + 1) := by
  have high := loop_output_address pointer value next
  change (Operand.reg 1 : Operand 64).read s +
    ((Operand.reg 8 : Operand 64).read s <<< 1) + 1#64 = _
  change (Operand.reg 1 : Operand 64).read s +
    ((Operand.reg 8 : Operand 64).read s <<< 1) + 0#64 = _ at high
  rw [BitVec.add_zero] at high
  rw [high, BitVec.ofNat_add, ← BitVec.add_assoc]

def loopBodyChanges (initial : RamState) (index : Nat) : List Component :=
  [.reg 9, .reg 10, .reg 11, .flags, .rip,
    .mem (initial.regValue .rcx + BitVec.ofNat 64 (2 * index)) 1,
    .mem (initial.regValue .rcx + BitVec.ofNat 64 (2 * index + 1)) 1]

theorem loop_body [Bindings] {initial s : RamState} {input : List UInt8}
    {capacity index : Nat} (call : ValidCall base16ctLowerEncodeStr initial input.toByteArray capacity (2 * input.length) (2 * input.length ≤ capacity))
    (outside : ¬ InProgram (returnBoundary initial).rip)
    (capacityFits : 2 * input.length ≤ capacity)
    (h : LoopInvariant initial input capacity index s) (hi : index < input.length) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ ReadyToStep t ∧
      t.RIP = 0x100519 ∧ AgreesExcept (loopBodyChanges initial index) s t ∧
      (Operand.mem (initial.regValue .rcx + BitVec.ofNat 64 (2 * index)) : Operand 8).read t =
        lowerHighDigit input[index] ∧
      (Operand.mem (initial.regValue .rcx + BitVec.ofNat 64 (2 * index + 1)) : Operand 8).read t =
        lowerLowDigit input[index] := by
  let highAddress := initial.regValue .rcx + BitVec.ofNat 64 (2 * index)
  let lowAddress := initial.regValue .rcx + BitVec.ofNat 64 (2 * index + 1)
  have highFits : 2 * index + 1 ≤ capacity := by omega
  have lowFits : 2 * index + 1 + 1 ≤ capacity := by omega
  have readInput := input_byte_read call h.toMachineInvariant hi
  have inputAddr (next : BitVec 64) : AddrMode.addr (.sib 6 (some 8) 0 .none) s next =
      initial.regValue .rdi + BitVec.ofNat 64 index := by
    change (Operand.reg 6 : Operand 64).read s +
      ((Operand.reg 8 : Operand 64).read s <<< 0) + 0#64 = _
    rw [BitVec.shiftLeft_zero, BitVec.add_zero, h.inputPointer, h.indexValue]
  have c0 : CodeIn (codeRange 0x1004d0 [0x46, 0x0f, 0xb6, 0x0c, 0x06]) s :=
    program_text_slice h.code 0x4d0 5 (by decide +kernel)
  obtain ⟨s1, run1, ready1, e1⟩ :=
    (movzx_r_m8_rex_effect_step 0x1004d0 0x46
      (by unfold RexPrefix; decide +kernel) 32 (.inr rfl)
      (fun _ => rfl) 1 (.sib 6 (some 8) 0 .none) (by decide +kernel) rfl rfl).advances
      h.ready c0 ⟨by simpa [hi] using h.rip, by rw [inputAddr]; exact readInput.1⟩
      (text_address_ne_return outside 0x4d5 (by decide +kernel))
  have a1 : AgreesExcept [.reg 9, .rip] s s1 := e1.agrees
  have code1 := a1.codeIn (by simp [Component.Covers]) h.code
  have byte1 : (Operand.reg 9 : Operand 64).read s1 = BitVec.ofNat 64 input[index].toNat := by
    have hw := e1.writes
    change (Operand.reg 9 : Operand 64).read s1 =
      ((Operand.mem (AddrMode.addr (.sib 6 (some 8) 0 .none) s 0x1004d5) : Operand 8).read s).setWidth 64 at hw
    rw [inputAddr, readInput.2] at hw
    rw [hw]
    apply BitVec.eq_of_toNat_eq
    simp
  obtain ⟨highFuel, s2, run2, ready2, _, e2⟩ :=
    Loop.Compute.high_run (returnBoundary initial) outside s1 ready1
      (Loop.Compute.high_code code1) e1.rip
  have a2 : AgreesExcept [.reg 10, .reg 11, .flags, .rip] s1 s2 := e2.agrees
  have a02 := a1.trans a2
  have code2 := e2.codeIn (Loop.Compute.highEffect_avoids _ _) code1
  have highAddr : storeAddrAt 0x1004f4 (.sib 1 (some 8) 1 .none) 4 s2 = highAddress :=
    loop_output_address ((a02.read (by simp)).trans h.outputPointer)
      ((a02.read (by simp)).trans h.indexValue) _
  have writableHigh := output_byte_writable call h.toMachineInvariant (by omega : 2 * index < capacity)
  have writableHigh2 : MemWritable s2 highAddress 1 :=
    ⟨writableHigh.low,
      fun j hj => a02.grow _ (writableHigh.mem j hj), writableHigh.tables⟩
  have c2 : CodeIn (codeRange 0x1004f4 [0x46, 0x88, 0x1c, 0x41]) s2 :=
    program_text_slice code2 0x4f4 4 (by decide +kernel)
  obtain ⟨s3, run3, ready3, e3⟩ := store_high_effect_step.advances ready2 c2
    ⟨e2.rip, by rwa [highAddr], by
      rw [highAddr]
      exact output_codeApart call highFits (codeOffset := 0x4f4) (by decide +kernel)⟩
    (text_address_ne_return outside 0x4f8 (by decide +kernel))
  have a3 : AgreesExcept [.mem highAddress 1, .rip] s2 s3 := by
    simpa only [movM8R8Effect_components, highAddr] using e3.agrees
  have code3 : CodeIn Extracted.programImage s3 := by
    apply CodeIn.of_agreesExcept a3 _ code2
    intro pair member component hc covers
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · obtain ⟨j, hj, eq⟩ := covers
      apply output_avoids_program call highFits j hj
      exact eq ▸ ⟨pair.2, member⟩
    · exact covers.elim
  have high3 : (Operand.mem highAddress : Operand 8).read s3 = lowerHighDigit input[index] := by
    have hw := e3.writes
    change (Operand.mem (storeAddrAt 0x1004f4 (.sib 1 (some 8) 1 .none) 4 s2) : Operand 8).read s3 =
      (Operand.reg 11 : Operand 8).read s2 at hw
    rw [highAddr, Loop.Compute.highEffect_read8 e2 byte1] at hw
    exact hw
  have byte3 : (Operand.reg 9 : Operand 64).read s3 = BitVec.ofNat 64 input[index].toNat :=
    (a3.read (by simp)).trans ((Loop.Compute.highEffect_read9 e2).trans byte1)
  obtain ⟨lowFuel, s4, run4, ready4, _, e4⟩ :=
    Loop.Compute.low_run (returnBoundary initial) outside s3 ready3
      (Loop.Compute.low_code code3) e3.rip
  have a4 : AgreesExcept [.reg 9, .reg 10, .flags, .rip] s3 s4 := e4.agrees
  have a04 := (a02.trans a3).trans a4
  have code4 := e4.codeIn (Loop.Compute.lowEffect_avoids _ _) code3
  have lowAddr : storeAddrAt 0x100514 (.sib 1 (some 8) 1 (.d8 1)) 5 s4 = lowAddress :=
    loop_output_next_address ((a04.read (by simp)).trans h.outputPointer)
      ((a04.read (by simp)).trans h.indexValue) _
  have writableLow := output_byte_writable call h.toMachineInvariant
    (by omega : 2 * index + 1 < capacity)
  have writableLow4 : MemWritable s4 lowAddress 1 :=
    ⟨writableLow.low,
      fun j hj => a04.grow _ (writableLow.mem j hj), writableLow.tables⟩
  have c4 : CodeIn (codeRange 0x100514 [0x46, 0x88, 0x54, 0x41, 0x01]) s4 :=
    program_text_slice code4 0x514 5 (by decide +kernel)
  obtain ⟨t, run5, readyt, e5⟩ := store_low_effect_step.advances ready4 c4
    ⟨e4.rip, by rwa [lowAddr], by
      rw [lowAddr]
      exact output_codeApart call lowFits (codeOffset := 0x514) (by decide +kernel)⟩
    (text_address_ne_return outside 0x519 (by decide +kernel))
  have a5 : AgreesExcept [.mem lowAddress 1, .rip] s4 t := by
    simpa only [movM8R8Effect_components, lowAddr] using e5.agrees
  have addresses : highAddress ≠ lowAddress := by
    dsimp only [highAddress, lowAddress]
    intro he
    have he := BitVec.add_right_inj _ |>.mp he
    have heNat := congrArg BitVec.toNat he
    have bound : (initial.regValue .rcx).toNat + capacity < 2 ^ 32 := call.outputInMemory.2.1
    simp only [BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show 2 * index < 2 ^ 64 by omega),
      Nat.mod_eq_of_lt (show 2 * index + 1 < 2 ^ 64 by omega)] at heNat
    omega
  refine ⟨1 + highFuel + 1 + lowFuel + 1, t,
    (((run1.trans run2).trans run3).trans run4).trans run5, readyt, e5.rip, ?_, ?_, ?_⟩
  · exact (a04.trans a5).mono (by simp [loopBodyChanges, highAddress, lowAddress])
  · apply Eq.trans (read_mem_of_agreesExcept (a4.trans a5) highAddress 8 ?_) high3
    intro j hj component hc covers
    have jz : j = 0 := by omega
    subst j
    simp only [BitVec.add_zero] at covers
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl) | (rfl | rfl)
    · exact covers.elim
    · exact covers.elim
    · exact covers.elim
    · exact covers.elim
    · obtain ⟨k, hk, he⟩ := covers
      have kz : k = 0 := by omega
      subst k
      exact addresses (by simpa using he)
    · exact covers.elim
  · have hw := e5.writes
    change (Operand.mem (storeAddrAt 0x100514 (.sib 1 (some 8) 1 (.d8 1)) 5 s4) : Operand 8).read t =
      (Operand.reg 10 : Operand 8).read s4 at hw
    rw [lowAddr, Loop.Compute.lowEffect_read8 e4 byte3] at hw
    exact hw

end Base16ct.Proofs.EncodeStr.Lower
