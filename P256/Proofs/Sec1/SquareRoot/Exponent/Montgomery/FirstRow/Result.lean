import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.FirstRow.Top
import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.FirstRow.Interface
import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.FirstRow.Arithmetic

set_option autoImplicit false

open P256.Proofs.Common.Instructions (mulHigh64)
open P256.Proofs.Common.Instructions.Carry (adcSpec)

namespace P256.Proofs.Sec1.SquareRoot.Montgomery

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

private theorem firstTop_pointer {p : BitVec 64} {s t : RamState}
    (h : (firstTopEffect p s).Holds s t) :
    (Operand.mem (stackPtr t+24#64) : Operand 64).read t =
      (Operand.mem (stackPtr s+24#64) : Operand 64).read s := by
  rw [Reduction.scratch_rsp (firstTop_frame h)]
  have hf : ∀ w ∈ (firstTopEffect p s).writes, w.Full := by
    simp [firstTopEffect, Write.Full, Operand.Full]
  have hp := (h.obsAfter hf true).read (Operand.mem (stackPtr s+24#64) : Operand 64) (by trivial)
  have hs (u : RamState) : stackPtr u = (Operand.reg 4#5 : Operand 64).read u := rfl
  x86_norm [firstTopEffect, hs] at hp
  exact hp.symm

private theorem FirstRowTrace.frame {entry : BitVec 64} {s t : RamState}
    (trace : FirstRowTrace entry s t) : AgreesExcept (Reduction.scratchComponents s) s t :=
  Reduction.scratch_trans (Reduction.scratch_trans (Reduction.scratch_trans
    (Reduction.scratch_trans (Reduction.scratch_trans
      (initialize_frame trace.initializeEffect) (firstProducts_frame trace.productsEffect))
      (firstCarry_frame trace.carryEffect)) (firstMiddle_frame trace.middleEffect))
      (firstHigh_frame trace.highEffect)) (firstTop_frame trace.topEffect)

private theorem FirstRowTrace.pointer {entry : BitVec 64} {s t : RamState}
    (trace : FirstRowTrace entry s t) : Rows.savedPtr t = s.regValue .rsi := by
  have hp := firstTop_pointer trace.topEffect
  have hp1 : (Operand.mem (stackPtr trace.initialized+24#64) : Operand 64).read trace.initialized =
      s.regValue .rsi := by
    rw [Reduction.scratch_rsp (initialize_frame trace.initializeEffect)]
    exact trace.initializeEffect.writes.2.2.2.2.2.2.2.1
  exact hp.trans ((firstHigh_pointer trace.highEffect).trans
    ((firstMiddle_pointer trace.middleEffect).trans
      ((firstCarry_pointer trace.carryEffect).trans
        ((firstProducts_pointer trace.productsEffect).trans hp1))))

private theorem scratch_read_limb {s t : RamState} {address : BitVec 64}
    (ag : AgreesExcept (Reduction.scratchComponents s) s t)
    (apart : RangeApart (stackPtr s) 112 address 32) (i : Fin 4) :
    (Operand.mem (address+BitVec.ofNat 64 (8*i.val)) : Operand 64).read t =
      (Operand.mem (address+BitVec.ofNat 64 (8*i.val)) : Operand 64).read s := by
  apply memLoad_congr
  intro j hj
  have hb : t.external[address+BitVec.ofNat 64 (8*i.val)+BitVec.ofNat 64 j]? =
      s.external[address+BitVec.ofNat 64 (8*i.val)+BitVec.ofNat 64 j]? := by
    apply ag.byte
    intro c hc ha
    simp only [Reduction.scratchComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    obtain ⟨k, hk, he⟩ := ha
    apply apart k hk (8*i.val+j) (by omega)
    simpa only [BitVec.ofNat_add, BitVec.add_assoc] using he.symm
  simp only [memByte, PhysicalMemory.read, hb]

private theorem read64_of_agrees {cs : List Component} {s t : RamState} {address : BitVec 64}
    (ag : AgreesExcept cs s t)
    (avoid : ∀ i < 8, ∀ c ∈ cs, ¬ c.Covers (address+BitVec.ofNat 64 i)) :
    (Operand.mem address : Operand 64).read t = (Operand.mem address : Operand 64).read s := by
  apply memLoad_congr
  intro i hi
  have hb := ag.byte (avoid i hi)
  simp only [memByte, PhysicalMemory.read, hb]

private theorem firstProducts_slot {p : BitVec 64} {s t : RamState}
    (h : (firstProductsEffect p s).Holds s t) (off : BitVec 64) :
    (Operand.mem (stackPtr t+off) : Operand 64).read t =
      (Operand.mem (stackPtr s+off) : Operand 64).read s := by
  rw [Reduction.scratch_rsp (firstProducts_frame h)]
  have hm := h.agrees.external (by simp [firstProductsEffect, Effect.components, Component.Covers])
  change memLoad t.external _ 64 = memLoad s.external _ 64
  rw [hm]

private theorem firstCarry_slot {p : BitVec 64} {s t : RamState}
    (h : (firstCarryEffect p s).Holds s t) (off : BitVec 64)
    (apart0 : OffsetsApart 48 8 off 8)
    : (Operand.mem (stackPtr t+off) : Operand 64).read t =
      (Operand.mem (stackPtr s+off) : Operand 64).read s := by
  rw [Reduction.scratch_rsp (firstCarry_frame h)]
  apply read64_of_agrees h.agrees
  intro i hi c hc ha
  simp only [firstCarryEffect, Effect.components, List.map_cons, List.map_nil,
    Write.component_reg, Write.component_mem, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  all_goals obtain ⟨j, hj, he⟩ := ha
  · exact apart0.ne (stackPtr s) hj hi (by decide) he.symm

private theorem firstMiddle_slot {p : BitVec 64} {s t : RamState}
    (h : (firstMiddleEffect p s).Holds s t) (off : BitVec 64)
    (apart0 : OffsetsApart 88 8 off 8)
    (apart1 : OffsetsApart 40 8 off 8)
    (apart2 : OffsetsApart 64 8 off 8)
    : (Operand.mem (stackPtr t+off) : Operand 64).read t =
      (Operand.mem (stackPtr s+off) : Operand 64).read s := by
  rw [Reduction.scratch_rsp (firstMiddle_frame h)]
  apply read64_of_agrees h.agrees
  intro i hi c hc ha
  simp only [firstMiddleEffect, Effect.components, List.map_cons, List.map_nil,
    Write.component_reg, Write.component_mem, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  all_goals obtain ⟨j, hj, he⟩ := ha
  · exact apart0.ne (stackPtr s) hj hi (by decide) he.symm
  · exact apart1.ne (stackPtr s) hj hi (by decide) he.symm
  · exact apart2.ne (stackPtr s) hj hi (by decide) he.symm

private theorem firstHigh_slot {p : BitVec 64} {s t : RamState}
    (h : (firstHighEffect p s).Holds s t) (off : BitVec 64)
    (apart0 : OffsetsApart 96 8 off 8)
    : (Operand.mem (stackPtr t+off) : Operand 64).read t =
      (Operand.mem (stackPtr s+off) : Operand 64).read s := by
  rw [Reduction.scratch_rsp (firstHigh_frame h)]
  apply read64_of_agrees h.agrees
  intro i hi c hc ha
  simp only [firstHighEffect, Effect.components, List.map_cons, List.map_nil,
    Write.component_reg, Write.component_mem, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  all_goals obtain ⟨j, hj, he⟩ := ha
  · exact apart0.ne (stackPtr s) hj hi (by decide) he.symm

private theorem firstTop_slot {p : BitVec 64} {s t : RamState}
    (h : (firstTopEffect p s).Holds s t) (off : BitVec 64)
    (apart0 : OffsetsApart 104 8 off 8)
    (apart1 : OffsetsApart 7 1 off 8)
    : (Operand.mem (stackPtr t+off) : Operand 64).read t =
      (Operand.mem (stackPtr s+off) : Operand 64).read s := by
  rw [Reduction.scratch_rsp (firstTop_frame h)]
  apply read64_of_agrees h.agrees
  intro i hi c hc ha
  simp only [firstTopEffect, Effect.components, List.map_cons, List.map_nil,
    Write.component_reg, Write.component_mem, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  all_goals obtain ⟨j, hj, he⟩ := ha
  · exact apart0.ne (stackPtr s) hj hi (by decide) he.symm
  · exact apart1.ne (stackPtr s) hj hi (by decide) he.symm

private theorem FirstRowTrace.initialized_slot {entry : BitVec 64} {s t : RamState}
    (trace : FirstRowTrace entry s t) (off : BitVec 64)
    (ho : off ∈ ([16,32,72,80] : List (BitVec 64))) :
    (Operand.mem (stackPtr t+off) : Operand 64).read t =
      (Operand.mem (stackPtr trace.initialized+off) : Operand 64).read trace.initialized := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl | rfl
  · exact (firstTop_slot trace.topEffect 16 (by unfold OffsetsApart; decide +kernel) (by unfold OffsetsApart; decide +kernel)).trans ((firstHigh_slot trace.highEffect 16 (by unfold OffsetsApart; decide +kernel)).trans ((firstMiddle_slot trace.middleEffect 16 (by unfold OffsetsApart; decide +kernel) (by unfold OffsetsApart; decide +kernel) (by unfold OffsetsApart; decide +kernel)).trans ((firstCarry_slot trace.carryEffect 16 (by unfold OffsetsApart; decide +kernel)).trans ((firstProducts_slot trace.productsEffect 16)))))
  · exact (firstTop_slot trace.topEffect 32 (by unfold OffsetsApart; decide +kernel) (by unfold OffsetsApart; decide +kernel)).trans ((firstHigh_slot trace.highEffect 32 (by unfold OffsetsApart; decide +kernel)).trans ((firstMiddle_slot trace.middleEffect 32 (by unfold OffsetsApart; decide +kernel) (by unfold OffsetsApart; decide +kernel) (by unfold OffsetsApart; decide +kernel)).trans ((firstCarry_slot trace.carryEffect 32 (by unfold OffsetsApart; decide +kernel)).trans ((firstProducts_slot trace.productsEffect 32)))))
  · exact (firstTop_slot trace.topEffect 72 (by unfold OffsetsApart; decide +kernel) (by unfold OffsetsApart; decide +kernel)).trans ((firstHigh_slot trace.highEffect 72 (by unfold OffsetsApart; decide +kernel)).trans ((firstMiddle_slot trace.middleEffect 72 (by unfold OffsetsApart; decide +kernel) (by unfold OffsetsApart; decide +kernel) (by unfold OffsetsApart; decide +kernel)).trans ((firstCarry_slot trace.carryEffect 72 (by unfold OffsetsApart; decide +kernel)).trans ((firstProducts_slot trace.productsEffect 72)))))
  · exact (firstTop_slot trace.topEffect 80 (by unfold OffsetsApart; decide +kernel) (by unfold OffsetsApart; decide +kernel)).trans ((firstHigh_slot trace.highEffect 80 (by unfold OffsetsApart; decide +kernel)).trans ((firstMiddle_slot trace.middleEffect 80 (by unfold OffsetsApart; decide +kernel) (by unfold OffsetsApart; decide +kernel) (by unfold OffsetsApart; decide +kernel)).trans ((firstCarry_slot trace.carryEffect 80 (by unfold OffsetsApart; decide +kernel)).trans ((firstProducts_slot trace.productsEffect 80)))))

private theorem FirstRowTrace.carry_slot {entry : BitVec 64} {s t : RamState}
    (trace : FirstRowTrace entry s t) (off : BitVec 64)
    (ho : off ∈ ([48] : List (BitVec 64))) :
    (Operand.mem (stackPtr t+off) : Operand 64).read t =
      (Operand.mem (stackPtr trace.carry+off) : Operand 64).read trace.carry := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl
  · exact (firstTop_slot trace.topEffect 48 (by unfold OffsetsApart; decide +kernel) (by unfold OffsetsApart; decide +kernel)).trans ((firstHigh_slot trace.highEffect 48 (by unfold OffsetsApart; decide +kernel)).trans ((firstMiddle_slot trace.middleEffect 48 (by unfold OffsetsApart; decide +kernel) (by unfold OffsetsApart; decide +kernel) (by unfold OffsetsApart; decide +kernel))))

private theorem FirstRowTrace.middle_slot {entry : BitVec 64} {s t : RamState}
    (trace : FirstRowTrace entry s t) (off : BitVec 64)
    (ho : off ∈ ([40,64,88] : List (BitVec 64))) :
    (Operand.mem (stackPtr t+off) : Operand 64).read t =
      (Operand.mem (stackPtr trace.middle+off) : Operand 64).read trace.middle := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl | rfl | rfl
  · exact (firstTop_slot trace.topEffect 40 (by unfold OffsetsApart; decide +kernel) (by unfold OffsetsApart; decide +kernel)).trans ((firstHigh_slot trace.highEffect 40 (by unfold OffsetsApart; decide +kernel)))
  · exact (firstTop_slot trace.topEffect 64 (by unfold OffsetsApart; decide +kernel) (by unfold OffsetsApart; decide +kernel)).trans ((firstHigh_slot trace.highEffect 64 (by unfold OffsetsApart; decide +kernel)))
  · exact (firstTop_slot trace.topEffect 88 (by unfold OffsetsApart; decide +kernel) (by unfold OffsetsApart; decide +kernel)).trans ((firstHigh_slot trace.highEffect 88 (by unfold OffsetsApart; decide +kernel)))

private theorem FirstRowTrace.high_slot {entry : BitVec 64} {s t : RamState}
    (trace : FirstRowTrace entry s t) (off : BitVec 64)
    (ho : off ∈ ([96] : List (BitVec 64))) :
    (Operand.mem (stackPtr t+off) : Operand 64).read t =
      (Operand.mem (stackPtr trace.high+off) : Operand 64).read trace.high := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
  rcases ho with rfl
  · exact (firstTop_slot trace.topEffect 96 (by unfold OffsetsApart; decide +kernel) (by unfold OffsetsApart; decide +kernel))

private theorem FirstRowTrace.sources {entry : BitVec 64} {s t : RamState}
    {a b : Vector (BitVec 64) 4} (pre : InitializePre (entry+14#64) s)
    (input : FirstRowInput s a b) (trace : FirstRowTrace entry s t) :
    (Operand.mem ((Operand.reg 1#5 : Operand 64).read trace.products+8#64) : Operand 64).read trace.products = 0xffffffff#64 ∧
    (Operand.mem ((Operand.reg 9#5 : Operand 64).read trace.carry+16#64) : Operand 64).read trace.carry = b[2] ∧
    (Operand.mem ((Operand.reg 1#5 : Operand 64).read trace.carry+16#64) : Operand 64).read trace.carry = 0#64 ∧
    (Operand.mem ((Operand.reg 9#5 : Operand 64).read trace.carry+24#64) : Operand 64).read trace.carry = b[3] ∧
    (Operand.mem ((Operand.reg 1#5 : Operand 64).read trace.carry+24#64) : Operand 64).read trace.carry = 0xffffffff00000001#64 ∧
    (Operand.mem ((Operand.mem (stackPtr trace.high+24#64) : Operand 64).read trace.high+8#64) : Operand 64).read trace.high = a[1] := by
  have f1 := initialize_frame trace.initializeEffect
  have f12 := Reduction.scratch_trans f1 (firstProducts_frame trace.productsEffect)
  have f123 := Reduction.scratch_trans f12 (firstCarry_frame trace.carryEffect)
  have f12345 := Reduction.scratch_trans (Reduction.scratch_trans f123
    (firstMiddle_frame trace.middleEffect)) (firstHigh_frame trace.highEffect)
  have m1 : (Operand.reg 1#5 : Operand 64).read trace.initialized = (Operand.reg 1#5 : Operand 64).read s :=
    trace.initializeEffect.agrees.read (by simp [Montgomery.initializeEffect, Effect.components, Write.component, Operand.component])
  have b1 : (Operand.reg 9#5 : Operand 64).read trace.initialized = (Operand.reg 2#5 : Operand 64).read s :=
    trace.initializeEffect.writes.2.1
  have m2 : (Operand.reg 1#5 : Operand 64).read trace.products = (Operand.reg 1#5 : Operand 64).read s :=
    (trace.productsEffect.agrees.read (by simp [firstProductsEffect, Effect.components, Write.component, Operand.component])).trans m1
  have b2 : (Operand.reg 9#5 : Operand 64).read trace.products = (Operand.reg 2#5 : Operand 64).read s :=
    (trace.productsEffect.agrees.read (by simp [firstProductsEffect, Effect.components, Write.component, Operand.component])).trans b1
  have m3 : (Operand.reg 1#5 : Operand 64).read trace.carry = (Operand.reg 1#5 : Operand 64).read s :=
    (trace.carryEffect.agrees.read (by simp [firstCarryEffect, Effect.components, Write.component, Operand.component])).trans m2
  have b3 : (Operand.reg 9#5 : Operand 64).read trace.carry = (Operand.reg 2#5 : Operand 64).read s :=
    (trace.carryEffect.agrees.read (by simp [firstCarryEffect, Effect.components, Write.component, Operand.component])).trans b2
  have ptr1 : (Operand.mem (stackPtr trace.initialized+24#64) : Operand 64).read trace.initialized =
      (Operand.reg 6#5 : Operand 64).read s := by
    rw [Reduction.scratch_rsp f1]
    exact trace.initializeEffect.writes.2.2.2.2.2.2.2.1
  have ptr5 : (Operand.mem (stackPtr trace.high+24#64) : Operand 64).read trace.high =
      (Operand.reg 6#5 : Operand 64).read s :=
    (firstHigh_pointer trace.highEffect).trans ((firstMiddle_pointer trace.middleEffect).trans
      ((firstCarry_pointer trace.carryEffect).trans ((firstProducts_pointer trace.productsEffect).trans ptr1)))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [m2]
    exact (scratch_read_limb f12 pre.modulusApart 1).trans (input.modulus 1)
  · rw [b3]
    exact (scratch_read_limb f123 pre.rightApart 2).trans (input.right 2)
  · rw [m3]
    exact (scratch_read_limb f123 pre.modulusApart 2).trans (input.modulus 2)
  · rw [b3]
    exact (scratch_read_limb f123 pre.rightApart 3).trans (input.right 3)
  · rw [m3]
    exact (scratch_read_limb f123 pre.modulusApart 3).trans (input.modulus 3)
  · rw [ptr5]
    exact (scratch_read_limb f12345 pre.leftApart 1).trans (input.left 1)

private theorem FirstRowTrace.saved {entry : BitVec 64} {s t : RamState}
    {a b : Vector (BitVec 64) 4} (pre : InitializePre (entry+14#64) s)
    (input : FirstRowInput s a b) (trace : FirstRowTrace entry s t) : Rows.Saved t b := by
  obtain ⟨hp1, hb2, hp2, hb3, hp3, _⟩ := trace.sources pre input
  have sp1 := Reduction.scratch_rsp (initialize_frame trace.initializeEffect)
  have sp3 := Reduction.scratch_rsp (firstCarry_frame trace.carryEffect)
  have sp4 := Reduction.scratch_rsp (firstMiddle_frame trace.middleEffect)
  have sp5 := Reduction.scratch_rsp (firstHigh_frame trace.highEffect)
  constructor
  · rw [trace.initialized_slot 72 (by simp), sp1]
    exact trace.initializeEffect.writes.2.2.2.2.2.2.2.2.1 |>.trans (by
      have hh := input.right 0
      change (Operand.mem ((Operand.reg 2#5 : Operand 64).read s+0#64) : Operand 64).read s = b[0] at hh
      simpa only [BitVec.add_zero] using hh)
  · rw [trace.initialized_slot 16 (by simp), sp1]
    exact trace.initializeEffect.writes.2.2.2.2.2.2.2.2.2.1 |>.trans (input.right 1)
  · rw [trace.middle_slot 88 (by simp), sp4]
    exact trace.middleEffect.writes.2.1 |>.trans hb2
  · rw [trace.high_slot 96 (by simp), sp5]
    exact trace.highEffect.writes.2.2.2.1 |>.trans (trace.middleEffect.writes.2.2.2.2.2.2.2.2.2.1.trans hb3)
  · rw [trace.initialized_slot 32 (by simp), sp1]
    exact trace.initializeEffect.writes.2.2.2.2.2.2.2.2.2.2 |>.trans (by
      have hh := input.modulus 0
      change (Operand.mem ((Operand.reg 1#5 : Operand 64).read s+0#64) : Operand 64).read s = 0xffffffffffffffff#64 at hh
      rw [BitVec.add_zero] at hh
      exact hh.trans (by decide +kernel))
  · rw [trace.carry_slot 48 (by simp), sp3]
    exact trace.carryEffect.writes.2.2.2.2.2.trans hp1
  · rw [trace.middle_slot 40 (by simp), sp4]
    exact trace.middleEffect.writes.2.2.2.2.2.1.trans hp2
  · rw [trace.middle_slot 64 (by simp), sp4]
    exact trace.middleEffect.writes.2.2.2.2.2.2.2.2.2.2.2.trans hp3
  · rw [trace.initialized_slot 80 (by simp), sp1]
    exact trace.initializeEffect.writes.2.2.2.2.2.2.1.trans input.inverse

attribute [local irreducible] addSpec adcSpec mulHigh64

section
variable {entry : BitVec 64} {s t : RamState} {a b : Vector (BitVec 64) 4}
variable (input : FirstRowInput s a b) (trace : FirstRowTrace entry s t)
variable (hp1 : (Operand.mem ((Operand.reg 1#5 : Operand 64).read trace.products+8#64) : Operand 64).read trace.products = 0xffffffff#64)
variable (hb2 : (Operand.mem ((Operand.reg 9#5 : Operand 64).read trace.carry+16#64) : Operand 64).read trace.carry = b[2])
variable (hp2 : (Operand.mem ((Operand.reg 1#5 : Operand 64).read trace.carry+16#64) : Operand 64).read trace.carry = 0#64)
variable (hb3 : (Operand.mem ((Operand.reg 9#5 : Operand 64).read trace.carry+24#64) : Operand 64).read trace.carry = b[3])
variable (hp3 : (Operand.mem ((Operand.reg 1#5 : Operand 64).read trace.carry+24#64) : Operand 64).read trace.carry = 0xffffffff00000001#64)
variable (ha1 : (Operand.mem ((Operand.mem (stackPtr trace.high+24#64) : Operand 64).read trace.high+8#64) : Operand 64).read trace.high = a[1])

include input trace hp1 hb2 hp2 hb3 hp3 ha1 in
set_option maxHeartbeats 800000 in
theorem firstRow_trace_arithmetic :
    (Operand.reg 14 : Operand 64).read t = a[1] ∧
    (Operand.reg 10 : Operand 64).read t = (firstRow a[0] a[1] b).first ∧
    (Operand.reg 3 : Operand 64).read t = (firstRow a[0] a[1] b).second ∧
    (Operand.reg 15 : Operand 64).read t = (firstRow a[0] a[1] b).top.low ∧
    (Operand.reg 9 : Operand 64).read t = (firstRow a[0] a[1] b).top.mid ∧
    (Operand.mem (stackPtr t+104) : Operand 64).read t = (firstRow a[0] a[1] b).top.high ∧
    (Operand.mem (stackPtr t+7) : Operand 8).read t = BitVec.ofNat 8 (firstRow a[0] a[1] b).top.carry.toNat := by
  let q := (product64 a[0] b[0]).1
  let c := startCarry q (product64 a[0] b[0]).2 false
  let m := middleCarry a[0] b[1] q 0 0 c.1 c.2
  let n := middleCarry a[0] b[2] q 0xffffffff00000001 0 m.2.1 m.2.2
  have ia : (Operand.mem ((Operand.reg 6#5 : Operand 64).read s) : Operand 64).read s = a[0] := by
    have h := input.left 0
    change (Operand.mem ((Operand.reg 6#5 : Operand 64).read s+0#64) : Operand 64).read s = a[0] at h
    simpa only [BitVec.add_zero] using h
  have ib0 : (Operand.mem ((Operand.reg 2#5 : Operand 64).read s) : Operand 64).read s = b[0] := by
    have h := input.right 0
    change (Operand.mem ((Operand.reg 2#5 : Operand 64).read s+0#64) : Operand 64).read s = b[0] at h
    simpa only [BitVec.add_zero] using h
  have ib1 : (Operand.mem ((Operand.reg 2#5 : Operand 64).read s+8) : Operand 64).read s = b[1] := input.right 1
  have ip0 : (Operand.mem ((Operand.reg 1#5 : Operand 64).read s) : Operand 64).read s = 0xffffffffffffffff#64 := by
    have h := input.modulus 0
    change (Operand.mem ((Operand.reg 1#5 : Operand 64).read s+0#64) : Operand 64).read s = 0xffffffffffffffff#64 at h
    simpa only [BitVec.add_zero] using h
  have ii : (Operand.reg 8#5 : Operand 64).read s = 1#64 := input.inverse
  have i14 : (Operand.reg 14#5 : Operand 64).read trace.initialized = 1#64 := by
    have hw := trace.initializeEffect.writes.1
    dsimp only [initializeEffect, Write.AllHold] at hw
    simpa only [ii] using hw
  have i2 : (Operand.reg 2#5 : Operand 64).read trace.initialized = b[0] := by
    have hw := trace.initializeEffect.writes.2.2.1
    dsimp only [initializeEffect, Write.AllHold] at hw
    simpa only [ib0] using hw
  have i10 : (Operand.reg 10#5 : Operand 64).read trace.initialized = b[1] := by
    have hw := trace.initializeEffect.writes.2.2.2.1
    dsimp only [initializeEffect, Write.AllHold] at hw
    simpa only [ib1] using hw
  have i15 : (Operand.reg 15#5 : Operand 64).read trace.initialized = 0xffffffffffffffff#64 := by
    have hw := trace.initializeEffect.writes.2.2.2.2.1
    dsimp only [initializeEffect, Write.AllHold] at hw
    simpa only [ip0] using hw
  have i11 : (Operand.reg 11#5 : Operand 64).read trace.initialized = a[0] := by
    have hw := trace.initializeEffect.writes.2.2.2.2.2.1
    dsimp only [initializeEffect, Write.AllHold] at hw
    simpa only [ia] using hw
  have p6 : (Operand.reg 6#5 : Operand 64).read trace.products = q := by
    have hw := trace.productsEffect.writes.2.2.1
    dsimp only [firstProductsEffect, Write.AllHold] at hw
    simpa only [i11, i2, i10, i15, i14, BitVec.one_mul, q, product64, BitVec.ofNat_eq_ofNat] using hw
  have p3 : (Operand.reg 3#5 : Operand 64).read trace.products = (product64 a[0] b[0]).2 := by
    have hw := trace.productsEffect.writes.2.2.2.1
    dsimp only [firstProductsEffect, Write.AllHold] at hw
    simpa only [i11, i2, i10, i15, i14, BitVec.one_mul, q, product64, BitVec.ofNat_eq_ofNat] using hw
  have p14 : (Operand.reg 14#5 : Operand 64).read trace.products = q := by
    have hw := trace.productsEffect.writes.2.2.2.2.1
    dsimp only [firstProductsEffect, Write.AllHold] at hw
    simpa only [i11, i2, i10, i15, i14, BitVec.one_mul, q, product64, BitVec.ofNat_eq_ofNat] using hw
  have p12 : (Operand.reg 12#5 : Operand 64).read trace.products = (product64 q 0xffffffffffffffff).2 := by
    have hw := trace.productsEffect.writes.2.2.2.2.2.1
    dsimp only [firstProductsEffect, Write.AllHold] at hw
    simpa only [i11, i2, i10, i15, i14, BitVec.one_mul, q, product64, BitVec.ofNat_eq_ofNat] using hw
  have p13 : (Operand.reg 13#5 : Operand 64).read trace.products = (product64 q 0xffffffffffffffff).1 := by
    have hw := trace.productsEffect.writes.2.2.2.2.2.2.1
    dsimp only [firstProductsEffect, Write.AllHold] at hw
    simpa only [i11, i2, i10, i15, i14, BitVec.one_mul, q, product64, BitVec.ofNat_eq_ofNat] using hw
  have p15 : (Operand.reg 15#5 : Operand 64).read trace.products = (product64 a[0] b[1]).1 := by
    have hw := trace.productsEffect.writes.2.2.2.2.2.2.2.1
    dsimp only [firstProductsEffect, Write.AllHold] at hw
    simpa only [i11, i2, i10, i15, i14, BitVec.one_mul, q, product64, BitVec.ofNat_eq_ofNat] using hw
  have p8 : (Operand.reg 8#5 : Operand 64).read trace.products = (product64 a[0] b[1]).2 := by
    have hw := trace.productsEffect.writes.2.2.2.2.2.2.2.2
    dsimp only [firstProductsEffect, Write.AllHold] at hw
    simpa only [i11, i2, i10, i15, i14, BitVec.one_mul, q, product64, BitVec.ofNat_eq_ofNat] using hw
  have p11 : (Operand.reg 11#5 : Operand 64).read trace.products = a[0] := by
    have he : (Operand.reg 11#5 : Operand 64).read trace.products = (Operand.reg 11#5 : Operand 64).read trace.initialized :=
      trace.productsEffect.agrees.read (by simp [firstProductsEffect, Effect.components])
    exact he.trans i11
  have hc := firstCarry_words q (product64 a[0] b[0]).2
  simp only [add64, adc64, product64, BitVec.ofNat_eq_ofNat] at hc
  have c10 : (Operand.reg 10#5 : Operand 64).read trace.carry = c.1 := by
    have hw := trace.carryEffect.writes.2.2.2.1
    dsimp only [firstCarryEffect, Write.AllHold] at hw
    simp only [hp1, p14, p3, p12, p13, p6, product64, BitVec.ofNat_eq_ofNat] at hw
    have he := congrArg (fun z : BitVec 64 × BitVec 64 => z.1) hc
    simpa only [c, product64] using hw.trans he
  have c5 : (Operand.reg 5#5 : Operand 64).read trace.carry = c.2 := by
    have hw := trace.carryEffect.writes.2.2.1
    dsimp only [firstCarryEffect, Write.AllHold] at hw
    simp only [hp1, p14, p3, p12, p13, p6, product64, BitVec.ofNat_eq_ofNat] at hw
    have he := congrArg (fun z : BitVec 64 × BitVec 64 => z.2) hc
    simpa only [c, product64] using hw.trans he
  have c11 : (Operand.reg 11#5 : Operand 64).read trace.carry = a[0] := by
    have he : (Operand.reg 11#5 : Operand 64).read trace.carry = (Operand.reg 11#5 : Operand 64).read trace.products :=
      trace.carryEffect.agrees.read (by simp [firstCarryEffect, Effect.components])
    exact he.trans p11
  have c14 : (Operand.reg 14#5 : Operand 64).read trace.carry = q := by
    have he : (Operand.reg 14#5 : Operand 64).read trace.carry = (Operand.reg 14#5 : Operand 64).read trace.products :=
      trace.carryEffect.agrees.read (by simp [firstCarryEffect, Effect.components])
    exact he.trans p14
  have c15 : (Operand.reg 15#5 : Operand 64).read trace.carry = (product64 a[0] b[1]).1 := by
    have he : (Operand.reg 15#5 : Operand 64).read trace.carry = (Operand.reg 15#5 : Operand 64).read trace.products :=
      trace.carryEffect.agrees.read (by simp [firstCarryEffect, Effect.components])
    exact he.trans p15
  have c8 : (Operand.reg 8#5 : Operand 64).read trace.carry = (product64 a[0] b[1]).2 := by
    have he : (Operand.reg 8#5 : Operand 64).read trace.carry = (Operand.reg 8#5 : Operand 64).read trace.products :=
      trace.carryEffect.agrees.read (by simp [firstCarryEffect, Effect.components])
    exact he.trans p8
  have hm := firstMiddle_words a[0] b[1] q 0 c.1 c.2
  simp only [add64, adc64, product64, BitVec.ofNat_eq_ofNat] at hm
  have m10 : (Operand.reg 10#5 : Operand 64).read trace.middle = m.1 := by
    have hw := trace.middleEffect.writes.2.2.2.2.2.2.2.2.1
    dsimp only [firstMiddleEffect, Write.AllHold] at hw
    simp only [c10, c15, product64] at hw
    have he := congrArg (fun z : BitVec 64 × BitVec 64 × BitVec 64 => z.1) hm
    simpa only [m, product64, BitVec.ofNat_eq_ofNat] using hw.trans he
  have m3 : (Operand.reg 3#5 : Operand 64).read trace.middle = m.2.1 := by
    have hw := trace.middleEffect.writes.2.2.2.2.2.2.2.1
    dsimp only [firstMiddleEffect, Write.AllHold] at hw
    simp only [hp2, c14, c8, c5, c10, c15, product64] at hw
    have he := congrArg (fun z : BitVec 64 × BitVec 64 × BitVec 64 => z.2.1) hm
    simpa only [m, product64, BitVec.ofNat_eq_ofNat] using hw.trans he
  have m12 : (Operand.reg 12#5 : Operand 64).read trace.middle = m.2.2 := by
    have hw := trace.middleEffect.writes.2.2.2.2.2.2.1
    dsimp only [firstMiddleEffect, Write.AllHold] at hw
    simp only [hp2, c14, c8, c5, c10, c15, product64] at hw
    have he := congrArg (fun z : BitVec 64 × BitVec 64 × BitVec 64 => z.2.2) hm
    simpa only [m, product64, BitVec.ofNat_eq_ofNat] using hw.trans he
  have m6 : (Operand.reg 6#5 : Operand 64).read trace.middle = (product64 a[0] b[2]).1 := by
    have hw := trace.middleEffect.writes.2.2.2.1
    dsimp only [firstMiddleEffect, Write.AllHold] at hw
    simpa only [c11, hb2, product64] using hw
  have m13 : (Operand.reg 13#5 : Operand 64).read trace.middle = (product64 a[0] b[2]).2 := by
    have hw := trace.middleEffect.writes.2.2.2.2.1
    dsimp only [firstMiddleEffect, Write.AllHold] at hw
    simpa only [c11, hb2, product64] using hw
  have m8 : (Operand.reg 8#5 : Operand 64).read trace.middle = b[3] := by
    have hw := trace.middleEffect.writes.2.2.2.2.2.2.2.2.2.1
    dsimp only [firstMiddleEffect, Write.AllHold] at hw
    simpa only [hb3] using hw
  have m9 : (Operand.reg 9#5 : Operand 64).read trace.middle = 0xffffffff00000001#64 := by
    have hw := trace.middleEffect.writes.2.2.2.2.2.2.2.2.2.2.1
    dsimp only [firstMiddleEffect, Write.AllHold] at hw
    simpa only [hp3] using hw
  have m11 : (Operand.reg 11#5 : Operand 64).read trace.middle = a[0] := by
    have he : (Operand.reg 11#5 : Operand 64).read trace.middle = (Operand.reg 11#5 : Operand 64).read trace.carry :=
      trace.middleEffect.agrees.read (by simp [firstMiddleEffect, Effect.components])
    exact he.trans c11
  have m14 : (Operand.reg 14#5 : Operand 64).read trace.middle = q := by
    have he : (Operand.reg 14#5 : Operand 64).read trace.middle = (Operand.reg 14#5 : Operand 64).read trace.carry :=
      trace.middleEffect.agrees.read (by simp [firstMiddleEffect, Effect.components])
    exact he.trans c14
  have hn := firstMiddle_words a[0] b[2] q 0xffffffff00000001 m.2.1 m.2.2
  simp only [add64, adc64, product64, BitVec.ofNat_eq_ofNat] at hn
  have h3 : (Operand.reg 3#5 : Operand 64).read trace.high = n.1 := by
    have hw := trace.highEffect.writes.2.2.2.2.2.2.2.2
    dsimp only [firstHighEffect, Write.AllHold] at hw
    simp only [m3, m6, product64] at hw
    have he := congrArg (fun z : BitVec 64 × BitVec 64 × BitVec 64 => z.1) hn
    simpa only [n, product64, BitVec.ofNat_eq_ofNat] using hw.trans he
  have h15 : (Operand.reg 15#5 : Operand 64).read trace.high = n.2.1 := by
    have hw := trace.highEffect.writes.2.2.2.2.2.2.2.1
    dsimp only [firstHighEffect, Write.AllHold] at hw
    simp only [m14, m9, m13, m12, m3, m6, product64] at hw
    have he := congrArg (fun z : BitVec 64 × BitVec 64 × BitVec 64 => z.2.1) hn
    simpa only [n, product64, BitVec.ofNat_eq_ofNat] using hw.trans he
  have h9 : (Operand.reg 9#5 : Operand 64).read trace.high = n.2.2 := by
    have hw := trace.highEffect.writes.2.2.2.2.2.2.1
    dsimp only [firstHighEffect, Write.AllHold] at hw
    simp only [m14, m9, m13, m12, m3, m6, product64] at hw
    have he := congrArg (fun z : BitVec 64 × BitVec 64 × BitVec 64 => z.2.2) hn
    simpa only [n, product64, BitVec.ofNat_eq_ofNat] using hw.trans he
  have h1 : (Operand.reg 1#5 : Operand 64).read trace.high = (product64 a[0] b[3]).2 := by
    have hw := trace.highEffect.writes.2.2.2.2.1
    dsimp only [firstHighEffect, Write.AllHold] at hw
    simpa only [m11, m8, product64] using hw
  have h8 : (Operand.reg 8#5 : Operand 64).read trace.high = (product64 a[0] b[3]).1 := by
    have hw := trace.highEffect.writes.2.2.2.2.2.1
    dsimp only [firstHighEffect, Write.AllHold] at hw
    simpa only [m11, m8, product64] using hw
  have h11 : (Operand.reg 11#5 : Operand 64).read trace.high = b[3] := by
    have hw := trace.highEffect.writes.2.2.1
    dsimp only [firstHighEffect, Write.AllHold] at hw
    simpa only [m8] using hw
  have h10 : (Operand.reg 10#5 : Operand 64).read trace.high = m.1 := by
    have he : (Operand.reg 10#5 : Operand 64).read trace.high = (Operand.reg 10#5 : Operand 64).read trace.middle :=
      trace.highEffect.agrees.read (by simp [firstHighEffect, Effect.components])
    exact he.trans m10
  have t10 : (Operand.reg 10#5 : Operand 64).read t = m.1 := by
    have he : (Operand.reg 10#5 : Operand 64).read t = (Operand.reg 10#5 : Operand 64).read trace.high :=
      trace.topEffect.agrees.read (by simp [firstTopEffect, Effect.components])
    exact he.trans h10
  have t3 : (Operand.reg 3#5 : Operand 64).read t = n.1 := by
    have he : (Operand.reg 3#5 : Operand 64).read t = (Operand.reg 3#5 : Operand 64).read trace.high :=
      trace.topEffect.agrees.read (by simp [firstTopEffect, Effect.components])
    exact he.trans h3
  obtain ⟨t14, t15, t9, mem104, mem7⟩ :=
    firstTop_values trace.topEffect h15 h9 h8 h1 h11 ha1
  have row : firstRow a[0] a[1] b =
      ⟨m.1, n.1, firstTop n.2.1 n.2.2 a[0] b[3] a[1]⟩ := by
    simp only [firstRow, coreWords, add64_zero, q, c, m, n]
  rw [row]
  simpa only [BitVec.ofNat_eq_ofNat] using
    And.intro t14 (And.intro t10 (And.intro t3 (And.intro t15 (And.intro t9 (And.intro mem104 mem7)))))

end

theorem firstRow_trace_result [Bindings] {entry : BitVec 64} {boundary : ReturnBoundary}
    {s t : RamState} {a b : Vector (BitVec 64) 4}
    (he : Entry entry) (hout : ¬ InProgram boundary.rip)
    (pre : InitializePre (entry+14#64) s) (input : FirstRowInput s a b)
    (trace : FirstRowTrace entry s t) (ready : ReadyToStep t) (loaded : ProgramLoaded t) :
    Rows.Pre entry boundary a b t := by
  obtain ⟨hp1,hb2,hp2,hb3,hp3,ha1⟩ := trace.sources pre input
  obtain ⟨digit,first,second,low,mid,high,carry⟩ :=
    firstRow_trace_arithmetic input trace hp1 hb2 hp2 hb3 hp3 ha1
  have frame := trace.frame
  refine ⟨he, ?_, ready, loaded, hout, pre.memory.of_scratch frame,
    trace.saved pre input, ?_, ?_, ?_, digit, first, second, low, mid, high, carry⟩
  · have h := trace.topEffect.rip
    change t.RIP = (entry+281#64)+48#64 at h
    simpa only [BitVec.add_assoc, show 281#64+48#64 = 0x149#64 by decide +kernel] using h
  · rw [trace.pointer]
    exact P256.Proofs.Program.readable_of_grow pre.left frame.grow
  · rw [trace.pointer, Reduction.scratch_rsp frame]
    exact pre.leftApart
  · intro i
    rw [trace.pointer]
    exact (scratch_read_limb frame pre.leftApart i).trans (input.left i)

end P256.Proofs.Sec1.SquareRoot.Montgomery
