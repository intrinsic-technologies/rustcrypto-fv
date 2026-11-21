import Base16ct.Proofs.Base16ctUpperEncodeCorrect.Context
import Base16ct.Proofs.Copied.Md5.Proofs.Memory.Basic
import Base16ct.Proofs.Copied.Md5.Proofs.Machine
namespace Base16ct.Proofs.Base16ctUpperEncodeCorrect
open Base16ct.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem length_output_contains (c : CallContext) (fits : 2 * c.input.length ≤ c.capacity)
    {address : BitVec 64} (inside : (Component.mem (c.initial.regValue .rdx) 8).Covers address) :
    (lengthOutputRegion c.initial).Contains address.toNat := by
  apply contains_of_mem_covers (c.valid.lengthOutputInMemoryIfLengthWritten fits).1
  simpa only [lengthOutputRegion, registerRegion, BitVec.ofNat_toNat,
    BitVec.setWidth_eq] using inside

theorem length_output_writable [Bindings] (c : CallContext) {s : RamState}
    (state : RunInvariant c s) (fits : 2 * c.input.length ≤ c.capacity) :
    Base16ct.Proofs.Copied.Md5.Proofs.Memory.MemWritable s (c.initial.regValue .rdx) 8 := by
  have valid := c.valid.lengthOutputInMemoryIfLengthWritten fits
  have hw : Base16ct.Proofs.Copied.Md5.Proofs.Memory.MemWritable c.initial (c.initial.regValue .rdx) 8 := by
    apply Base16ct.Proofs.Copied.Md5.Proofs.Memory.MemWritable.of_region valid.1 valid.2
    · intro address contains tables
      apply (c.valid.separation.2.2 fits).2 address contains
      apply Or.inr
      obtain ⟨region, member, inside⟩ := tables
      simp only [Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl
      · change 0x1000 ≤ address.toNat ∧ address.toNat < 0x1000 + 8 at inside
        change 0x1000 ≤ address.toNat ∧ address.toNat < 0x1000 + 0x2000
        omega
      · change 0x2000 ≤ address.toNat ∧ address.toNat < 0x2000 + 32 at inside
        change 0x1000 ≤ address.toNat ∧ address.toNat < 0x1000 + 0x2000
        omega
    · exact Nat.le_refl _
    · exact Nat.le_refl _
  exact ⟨hw.low, fun i hi ↦ state.agrees.grow _ (hw.bytes i hi), hw.tables⟩

theorem length_output_avoids_program (c : CallContext) (fits : 2 * c.input.length ≤ c.capacity) :
    ∀ i < 8, ¬ InProgram (c.initial.regValue .rdx + BitVec.ofNat 64 i) := by
  intro i hi inside
  exact (c.valid.separation.2.2 fits).2 _
    (length_output_contains c fits ⟨i, hi, rfl⟩) (.inl inside)

theorem length_output_apart_stack (c : CallContext) (fits : 2 * c.input.length ≤ c.capacity)
    {offset len : Nat} (low : offset ≤ 32) (high : len ≤ offset + 8) :
    RangeApart (c.initial.regValue .rdx) 8
      (stackPtr c.initial - BitVec.ofNat 64 offset) len := by
  have hs : Stack.Valid c.initial 160 := c.valid.stack
  obtain ⟨hstart, hend⟩ := stack_subrange_bounds hs (used := offset) (by omega)
  apply rangeApart_of_disjoint_subranges
    (c.valid.lengthOutputInMemoryIfLengthWritten fits).1 hs.1
    ((c.valid.separation.2.2 fits).1 0 2 (by decide +kernel))
    (Nat.le_refl _) (Nat.le_refl _) hstart (by omega)

theorem length_output_apart_output (c : CallContext) (fits : 2 * c.input.length ≤ c.capacity) :
    RangeApart (c.initial.regValue .rdx) 8 (c.initial.regValue .rcx) (2 * c.input.length) := by
  apply rangeApart_of_disjoint_subranges
    (c.valid.lengthOutputInMemoryIfLengthWritten fits).1
    (show (outputRegion c.initial (2 * c.input.length)).Bounded from by
      have hb := c.valid.outputInMemory.2.1
      change (c.initial.regValue .rcx).toNat + c.capacity < userAddressLimit at hb
      change (c.initial.regValue .rcx).toNat + 2 * c.input.length < userAddressLimit
      omega)
    ((c.valid.separation.2.2 fits).1 0 1 (by decide +kernel))
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _)

theorem encoder_final_state [bindings : Bindings] (c : CallContext) {t : RamState}
    (hMachine : SupportedIntegerMachineState bindings.processor c.initial)
    (hBindings : MachineRamUnitStrideDecodable bindings c.initial)
    (hReady : ReadyToStep t)
    (hAgree : AgreesExcept (encoderComponents c.initial c.writeLength ++
      if 2 * c.input.length ≤ c.capacity then [.mem (c.initial.regValue .rdx) 8] else [])
      c.initial t)
    (hRbx : t.regValue .rbx = c.initial.regValue .rbx) :
    SupportedIntegerMachineState bindings.processor t ∧
      MachineRamUnitStrideDecodable bindings t ∧
      CalleeSavedRegistersUnchanged c.initial t ∧ DirectionFlagUnset t := by
  refine ⟨supportedIntegerMachineState_of_ready hReady hAgree hMachine.sse,
    Base16ct.Proofs.Copied.Md5.Proofs.machineRamUnitStrideDecodable_of_ready hReady hBindings.stringStride,
    ?_, hAgree.directionFlagClear ?_ c.valid.directionFlagUnset⟩
  · intro register hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hRbx
    · exact hAgree.read (n := 64) (r := 5) (by split <;> simp [encoderComponents])
    · exact hAgree.read (n := 64) (r := 12) (by split <;> simp [encoderComponents])
    · exact hAgree.read (n := 64) (r := 13) (by split <;> simp [encoderComponents])
    · exact hAgree.read (n := 64) (r := 14) (by split <;> simp [encoderComponents])
    · exact hAgree.read (n := 64) (r := 15) (by split <;> simp [encoderComponents])
  · split <;> simp [encoderComponents]

theorem encoder_final_memoryWriteFrame (c : CallContext) {t : RamState}
    (hAgree : AgreesExcept (encoderComponents c.initial c.writeLength ++
      if 2 * c.input.length ≤ c.capacity then [.mem (c.initial.regValue .rdx) 8] else [])
      c.initial t) :
    if 2 * c.input.length ≤ c.capacity then
      MemoryWriteFrame c.initial t #v[outputRegion c.initial (2 * c.input.length),
        lengthOutputRegion c.initial, Stack.region c.initial 160]
    else MemoryWriteFrame c.initial t #v[Stack.region c.initial 160] := by
  have covers (comp : Component) (hc : comp ∈ encoderComponents c.initial c.writeLength ++
      if 2 * c.input.length ≤ c.capacity then [.mem (c.initial.regValue .rdx) 8] else [])
      (address : BitVec 64) (hcov : comp.Covers address) :
      (2 * c.input.length ≤ c.capacity ∧
        (outputRegion c.initial (2 * c.input.length)).Contains address.toNat) ∨
      (2 * c.input.length ≤ c.capacity ∧
        (lengthOutputRegion c.initial).Contains address.toNat) ∨
      (Stack.region c.initial 160).Contains address.toNat := by
    simp only [List.mem_append] at hc
    rcases hc with hc | hc
    · simp only [encoderComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl <;> try exact False.elim hcov
      · by_cases fits : 2 * c.input.length ≤ c.capacity
        · refine Or.inl ⟨fits, ?_⟩
          have ho : (outputRegion c.initial (2 * c.input.length)).Bounded := by
            have hb := c.valid.outputInMemory.2.1
            change (c.initial.regValue .rcx).toNat + c.capacity < 2^32 at hb
            change (c.initial.regValue .rcx).toNat + 2 * c.input.length < 2^32
            omega
          apply contains_of_mem_covers ho
          simpa only [CallContext.writeLength, ite_eq_left fits, outputRegion, registerRegion,
            BitVec.ofNat_toNat, BitVec.setWidth_eq] using hcov
        · obtain ⟨i, hi, _⟩ := hcov
          simp only [CallContext.writeLength, ite_eq_right fits] at hi
          omega
      · right; right
        obtain ⟨i, hi, rfl⟩ := hcov
        have hs : Stack.Valid c.initial 160 := c.valid.stack
        obtain ⟨hstart, hend⟩ := stack_subrange_bounds hs (used := 32) (by decide)
        exact contains_offset_of_subrange hs.1 hstart (by omega) i hi
    · split at hc
      next fits =>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        subst comp
        exact Or.inr (Or.inl ⟨fits, length_output_contains c fits hcov⟩)
      next fails => simp only [List.not_mem_nil] at hc
  split
  next fits =>
    intro address outside
    apply hAgree.byte
    intro comp hc hcov
    rcases covers comp hc address hcov with ⟨_, ho⟩ | ⟨_, hl⟩ | hs
    · exact outside _ (by simp) ho
    · exact outside _ (by simp) hl
    · exact outside _ (by simp) hs
  next fails =>
    intro address outside
    apply hAgree.byte
    intro comp hc hcov
    rcases covers comp hc address hcov with ⟨fits, _⟩ | ⟨fits, _⟩ | hs
    · exact fails fits
    · exact fails fits
    · exact outside _ (by simp) hs

theorem RunInvariant.returnSlot_read [Bindings] (c : CallContext) {s : RamState}
    (h : RunInvariant c s) :
    (Operand.mem (stackPtr c.initial) : Operand 64).read s = (returnBoundary c.initial).rip := by
  have hw := c.writeLength_le_capacity
  have ho : (outputRegion c.initial c.writeLength).Bounded := by
    have hb := c.valid.outputInMemory.2.1
    change (c.initial.regValue .rcx).toNat + c.capacity < 2^32 at hb
    change (c.initial.regValue .rcx).toNat + c.writeLength < 2^32
    omega
  have hd : (outputRegion c.initial c.writeLength).Disjoint (Stack.region c.initial 32) := by
    intro address hout hstack
    apply c.valid.separation.1 1 2 (by decide +kernel) address
    · change (c.initial.regValue .rcx).toNat ≤ address ∧
        address < (c.initial.regValue .rcx).toNat + c.writeLength at hout
      change (c.initial.regValue .rcx).toNat ≤ address ∧
        address < (c.initial.regValue .rcx).toNat + c.capacity
      omega
    · change (stackPtr c.initial).toNat - 32 ≤ address ∧
        address < (stackPtr c.initial).toNat - 32 +
          ((stackPtr c.initial).toNat + 8 - ((stackPtr c.initial).toNat - 32)) at hstack
      change (stackPtr c.initial).toNat - 160 ≤ address ∧
        address < (stackPtr c.initial).toNat - 160 +
          ((stackPtr c.initial).toNat + 8 - ((stackPtr c.initial).toNat - 160))
      omega
  exact encoder_returnSlot_read h.agrees ho c.stack32 hd

end Base16ct.Proofs.Base16ctUpperEncodeCorrect
