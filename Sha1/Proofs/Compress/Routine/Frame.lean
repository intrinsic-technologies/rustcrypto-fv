import Sha1.Proofs.Compress.Routine.Interface
import X86Proofs.Program.Entry
import X86Proofs.Program.ReadWrite.WriteFrame

namespace Sha1.Proofs.Compress.Routine

open Prelude X86 X86.Machine X86.UserProcess X86Proofs Sha1.Proofs.Refine
open Sha1.Spec Sha1.Spec.Program Standards.NIST

theorem Context.Valid.stack_bounds {c : Context} {bindings : Bindings}
    (h : c.Valid bindings) : 336 ≤ c.sp.toNat ∧ c.sp.toNat + 8 < 2 ^ 32 := by
  have hb := h.call.stackAvailable.1
  have hn := h.call.stackAvailable.2.2.1
  change (c.sp.toNat - 336) + (c.sp.toNat + 8 - (c.sp.toNat - 336)) < 2 ^ 32 at hb
  change 336 ≤ c.sp.toNat at hn
  exact ⟨hn, by omega⟩

theorem Context.Valid.stack_toNat {c : Context} {bindings : Bindings}
    (h : c.Valid bindings) : c.stack.toNat = c.sp.toNat - 208 := by
  have hs := h.stack_bounds
  change (c.sp - 208).toNat = _
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; change 208 ≤ c.sp.toNat; omega)]
  rfl

theorem Context.Valid.stack_add_toNat {c : Context} {bindings : Bindings}
    (h : c.Valid bindings) {off : Nat} (hoff : off ≤ 216) :
    (c.stack + BitVec.ofNat 64 off).toNat = c.sp.toNat - 208 + off := by
  have hs := h.stack_bounds
  rw [BitVec.toNat_add, h.stack_toNat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (a := off) (by omega), Nat.mod_eq_of_lt (by omega)]

theorem Context.Valid.stack_inRegion {c : Context} {bindings : Bindings}
    (h : c.Valid bindings) {off len : Nat} (hb : off + len ≤ 216) :
    InRegion c.stackRegion (c.stack + BitVec.ofNat 64 off) len := by
  unfold InRegion
  rw [h.stack_add_toNat (by omega)]
  have hs := h.stack_bounds
  change c.sp.toNat - 336 ≤ c.sp.toNat - 208 + off ∧
    c.sp.toNat - 208 + off + len ≤
      c.sp.toNat - 336 + (c.sp.toNat + 8 - (c.sp.toNat - 336)) ∧
    c.sp.toNat - 208 + off + len ≤ 2 ^ 64
  constructor
  · omega
  · constructor <;> omega

theorem Context.Valid.outputContract {c : Context} {bindings : Bindings}
    (h : c.Valid bindings) :
    Common.OutputFrameContract Extracted.programImage c.initial.external
      (Compress.outputRegion c.initial) c.stackRegion := by
  exact Common.OutputFrameContract.of_valid
    ⟨h.call.outputInMemory.1, h.call.outputInMemory.2.1,
      allocated_of_hasBytes h.call.outputInMemory.2.2⟩
    h.call.stackAvailable h.call.separation

theorem Context.Valid.stack_writable {c : Context} {bindings : Bindings}
    (h : c.Valid bindings) : Machine.MemWritable c.initial c.stack 216 := by
  have hr := h.outputContract.stack
  have hin : InRegion c.stackRegion c.stack 216 := by
    simpa only [BitVec.reduceOfNat, BitVec.add_zero] using h.stack_inRegion (off := 0) (by decide)
  refine ⟨Nat.le_trans hin.2.1 (Nat.le_of_lt hr.bounded), ?_, ?_⟩
  · intro i hi
    exact Option.isSome_iff_exists.mpr (hr.allocated _ (Common.StoreRegion.contains_byte hin hi))
  · intro i hi ht
    exact hr.avoids _ (Common.StoreRegion.contains_byte hin hi) (.inr ht)

theorem Context.Valid.outputStoreRegion {c : Context} {bindings : Bindings}
    (h : c.Valid bindings) {s : RamState} (hf : Frame c s) :
    Common.StoreRegion Extracted.programImage s.external (Compress.outputRegion c.initial) :=
  h.outputContract.output.of_frame hf.memory

theorem CallData.boundary {c : Context} (bindings : Bindings)
    (hEnv : MachineRamUnitStrideDecodable bindings c.initial)
    (hMachine : SupportedIntegerMachineState bindings.processor c.initial) (h : CallData c) :
    @nearReturn64Boundary _ _ bindings c.initial = .ok (returnBoundary c.initial) := by
  letI := bindings
  have entry : EntryReady Extracted.programImage c.initial :=
    EntryReady.of_sections hMachine hEnv.smrr hEnv.memoryType
      hEnv.leadingZeroCount h.programLoaded (by decide +kernel)
  have hb := h.stackAvailable.1
  have hn := h.stackAvailable.2.2.1
  change Compress.minStackBytes ≤ c.sp.toNat at hn
  change c.sp.toNat - Compress.minStackBytes +
    (c.sp.toNat + 8 - (c.sp.toNat - Compress.minStackBytes)) < 2 ^ 32 at hb
  have hr : MemReadable c.initial (stackPtr c.initial) 8 := by
    refine ⟨?_, fun i hi ↦ ?_⟩
    · change c.sp.toNat + 8 ≤ 2 ^ 32
      omega
    · apply Option.isSome_iff_exists.mpr
      apply h.stackAvailable.2.1
      change c.sp.toNat - Compress.minStackBytes ≤ (c.sp + BitVec.ofNat 64 i).toNat ∧
        (c.sp + BitVec.ofNat 64 i).toNat < c.sp.toNat - Compress.minStackBytes +
          (c.sp.toNat + 8 - (c.sp.toNat - Compress.minStackBytes))
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := i) (by omega),
        Nat.mod_eq_of_lt (by omega)]
      constructor <;> omega
  exact nearReturn64Boundary_eq c.initial entry.ready.dataReady entry.ready.cpu.ss hr

theorem CallData.boundary_of_ready {c : Context} {bindings : Bindings}
    (hReady : ReadyToStep c.initial) (h : CallData c) :
    @nearReturn64Boundary _ _ bindings c.initial = .ok (returnBoundary c.initial) := by
  letI := bindings
  have hb := h.stackAvailable.1
  have hn := h.stackAvailable.2.2.1
  change Compress.minStackBytes ≤ c.sp.toNat at hn
  change c.sp.toNat - Compress.minStackBytes +
    (c.sp.toNat + 8 - (c.sp.toNat - Compress.minStackBytes)) < 2 ^ 32 at hb
  have hr : MemReadable c.initial (stackPtr c.initial) 8 := by
    refine ⟨?_, fun i hi ↦ ?_⟩
    · change c.sp.toNat + 8 ≤ 2 ^ 32
      omega
    · apply Option.isSome_iff_exists.mpr
      apply h.stackAvailable.2.1
      change Compress.minStackBytes ≤ c.sp.toNat at hn
      change c.sp.toNat - Compress.minStackBytes ≤
        (c.sp + BitVec.ofNat 64 i).toNat ∧
        (c.sp + BitVec.ofNat 64 i).toNat < c.sp.toNat - Compress.minStackBytes +
          (c.sp.toNat + 8 - (c.sp.toNat - Compress.minStackBytes))
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := i) (by omega),
        Nat.mod_eq_of_lt (by omega)]
      constructor <;> omega
  exact nearReturn64Boundary_eq c.initial hReady.dataReady hReady.cpu.ss hr

theorem Context.Valid.boundary {c : Context} {bindings : Bindings}
    (h : c.Valid bindings) :
    @nearReturn64Boundary _ _ bindings c.initial = .ok (returnBoundary c.initial) :=
  h.call.boundary_of_ready h.ready

private theorem protected_load {c : Context} {bindings : Bindings}
    (hv : c.Valid bindings) {s t : RamState}
    (ha : AgreesExcept (Machine.scratchComponents c.stack) s t)
    {off : Nat} (hb : (128 ≤ off ∧ off + 8 ≤ 144) ∨ (160 ≤ off ∧ off + 8 ≤ 216)) :
    memLoad t.external (c.stack + BitVec.ofNat 64 off) 64 =
      memLoad s.external (c.stack + BitVec.ofNat 64 off) 64 := by
  have hs := hv.stack_bounds
  have h0 := hv.stack_toNat
  have h144 : (c.stack + 144).toNat = c.sp.toNat - 208 + 144 :=
    hv.stack_add_toNat (by decide)
  have ho := hv.stack_add_toNat (off := off) (by rcases hb with h | h <;> omega)
  have ha0 : RangeApart c.stack 128 (c.stack + BitVec.ofNat 64 off) 8 := by
    apply RangeApart.of_toNat
    · rw [h0]; omega
    · rw [ho]; rcases hb with h | h <;> omega
    · rw [h0, ho]; rcases hb with h | h <;> omega
  have ha144 : RangeApart (c.stack + 144) 16 (c.stack + BitVec.ofNat 64 off) 8 := by
    apply RangeApart.of_toNat
    · rw [h144]; omega
    · rw [ho]; rcases hb with h | h <;> omega
    · rw [h144, ho]; rcases hb with h | h <;> omega
  apply memLoad_congr
  intro i hi
  change (t.external[c.stack + BitVec.ofNat 64 off + BitVec.ofNat 64 i]?).getD 0 = _
  congr 1
  apply ha.byte
  intro comp hc hcov
  simp only [Machine.scratchComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact hcov.elim
  · obtain ⟨j, hj, he⟩ := hcov
    exact ha0 j hj i hi he.symm
  · obtain ⟨j, hj, he⟩ := hcov
    exact ha144 j hj i hi he.symm

private theorem ramWriteFrame_of_covers {region : MemoryRegion} {cs : List Component}
    {s t : RamState} (ha : AgreesExcept cs s t)
    (hinside : ∀ comp ∈ cs, ∀ x, comp.Covers x → region.Contains x.toNat) :
    RamWriteFrame s.external t.external [region] := by
  refine ⟨?_, ha.grow⟩
  intro x hx
  apply ha.byte
  intro comp hc hcov
  have hm := hinside comp hc x hcov
  have hout := hx.2 region (List.mem_singleton_self _)
  change region.start ≤ x.toNat ∧ x.toNat < region.start + region.size at hm
  rcases hout with hout | hout <;> omega

theorem Context.Valid.ramWriteFrame_of_agrees {c : Context} {bindings : Bindings}
    (hv : c.Valid bindings) {s : RamState}
    (ha : AgreesExcept [.mem c.stack 208, .reg 0, .reg 2, .reg 4, .reg 8,
      .reg 10, .reg 11, .flags, .rip] c.initial s) :
    RamWriteFrame c.initial.external s.external [c.stackRegion] := by
  apply ramWriteFrame_of_covers ha
  intro comp hc x hcov
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact hcov.elim
  obtain ⟨i, hi, rfl⟩ := hcov
  have hin : InRegion c.stackRegion c.stack 208 := by
    simpa only [BitVec.add_zero] using hv.stack_inRegion (off := 0) (len := 208) (by decide)
  exact Common.StoreRegion.contains_byte hin hi

theorem Frame.of_agrees {c : Context} {bindings : Bindings} (hv : c.Valid bindings)
    {s t : RamState} (h : Frame c s)
    (ha : AgreesExcept (Machine.scratchComponents c.stack) s t) : Frame c t := by
  refine ⟨(ha.read (r := 4) (n := 64) (by simp [Machine.scratchComponents])).trans h.stackPointer,
    ⟨h.writable.low, fun i hi ↦ ha.grow _ (h.writable.mem i hi), h.writable.tables⟩,
    ?_, ?_, ?_, ?_, ?_,
    ha.rest.trans h.controls,
    ha.directionFlagClear (by simp [Machine.scratchComponents]) h.directionFlag⟩
  · apply h.memory.trans (ramWriteFrame_of_covers ha ?_)
    · intro r hr
      obtain rfl := List.mem_singleton.mp hr
      exact ⟨c.stackRegion, List.mem_singleton_self _, Nat.le_refl _, Nat.le_refl _⟩
    · intro comp hc x hcov
      obtain ⟨i, hi, he⟩ := Machine.scratchComponents_covers hc hcov
      have hin : InRegion c.stackRegion c.stack 160 := by
        simpa only [BitVec.add_zero] using hv.stack_inRegion (off := 0) (len := 160) (by decide)
      rw [he]
      exact Common.StoreRegion.contains_byte hin hi
  · intro i
    rw [protected_load hv ha (Or.inr ⟨by omega, by have := i.isLt; omega⟩)]
    exact h.saved i
  · exact (protected_load hv ha (off := 128) (Or.inl ⟨by decide, by decide⟩)).trans h.output
  · exact (protected_load hv ha (off := 136) (Or.inl ⟨by decide, by decide⟩)).trans h.inputEnd
  · have he : c.sp = c.stack + BitVec.ofNat 64 208 := by
      change c.sp = c.sp - 208 + 208
      bv_omega
    rw [he, protected_load hv ha (off := 208) (Or.inr ⟨by decide, by decide⟩)]
    rw [← he]
    exact h.callerReturn

theorem Context.Valid.input_add_toNat {c : Context} {bindings : Bindings}
    (h : c.Valid bindings) {k off : Nat} (hb : 64 * k + off ≤ c.blocks.size) :
    (c.input k + BitVec.ofNat 64 off).toNat =
      (c.initial.regValue .rsi).toNat + 64 * k + off := by
  have hi := h.call.inputInMemory.2.1
  change (c.initial.regValue .rsi).toNat + c.blocks.size < 2 ^ 32 at hi
  simp only [Context.input, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := 64 * k) (by omega),
    Nat.mod_eq_of_lt (a := (c.initial.regValue .rsi).toNat + 64 * k) (by omega),
    Nat.mod_eq_of_lt (a := off) (by omega), Nat.mod_eq_of_lt (by omega)]

theorem Context.Valid.input_inRegion {c : Context} {bindings : Bindings}
    (h : c.Valid bindings) {k : Nat} (hk : k < c.count) :
    InRegion (Compress.inputRegion c.initial c.blocks) (c.input k) 64 := by
  have hi := h.call.inputInMemory.2.1
  change (c.initial.regValue .rsi).toNat + c.blocks.size < 2 ^ 32 at hi
  have hk' : k < c.blocks.size / 64 := hk
  have he : (c.input k).toNat = (c.initial.regValue .rsi).toNat + 64 * k := by
    simpa only [BitVec.add_zero, Nat.add_zero] using
      h.input_add_toNat (k := k) (off := 0) (by omega)
  change (c.initial.regValue .rsi).toNat ≤ (c.input k).toNat ∧
    (c.input k).toNat + 64 ≤ (c.initial.regValue .rsi).toNat + c.blocks.size ∧
    (c.input k).toNat + 64 ≤ 2 ^ 64
  rw [he]
  constructor
  · omega
  · constructor <;> omega

theorem Frame.input_hasBytes {c : Context} {bindings : Bindings} (hv : c.Valid bindings)
    {s : RamState} (h : Frame c s) :
    (Compress.inputRegion c.initial c.blocks).HasBytes s.external c.blocks := by
  refine ⟨hv.call.inputInMemory.2.2.1, ?_⟩
  intro i
  have hi := i.isLt
  have hb := hv.call.inputInMemory.2.1
  change (c.initial.regValue .rsi).toNat + c.blocks.size < 2 ^ 32 at hb
  have ha : (BitVec.ofNat 64 ((Compress.inputRegion c.initial c.blocks).start + i.val)).toNat =
      (c.initial.regValue .rsi).toNat + i.val := by
    change ((c.initial.regValue .rsi).toNat + i.val) % 2 ^ 64 = _
    exact Nat.mod_eq_of_lt (by omega)
  have hin : (Compress.inputRegion c.initial c.blocks).Contains
      (BitVec.ofNat 64 ((Compress.inputRegion c.initial c.blocks).start + i.val)).toNat := by
    rw [ha]
    change (c.initial.regValue .rsi).toNat ≤ (c.initial.regValue .rsi).toNat + i.val ∧
      (c.initial.regValue .rsi).toNat + i.val < (c.initial.regValue .rsi).toNat + c.blocks.size
    constructor <;> omega
  have hdis := (hv.call.separation.2 c.stackRegion (by simp [Context.stackRegion])).1
    (Compress.inputRegion c.initial c.blocks) (List.mem_singleton_self _)
  have hn := hdis _ hin
  rw [h.memory.outside _ ⟨by rw [ha]; omega, ?_⟩]
  · exact hv.call.inputInMemory.2.2.2 i
  · intro r hr
    obtain rfl := List.mem_singleton.mp hr
    change ¬ (c.stackRegion.start ≤ _ ∧ _ < c.stackRegion.start + c.stackRegion.size) at hn
    omega

theorem atBlock_blockData {c : Context} {bindings : Bindings} (hv : c.Valid bindings)
    {k : Nat} {H : Vector (BitVec 32) 5} {s : RamState} (hk : k < c.count)
    (h : AtBlock c k H s) : Machine.BlockData c.stack (c.input k) H (c.message k) s := by
  have hin := hv.input_inRegion hk
  have hbytes := h.frame.input_hasBytes hv
  have hb := hv.call.inputInMemory.2.1
  have halloc := allocated_of_hasBytes hbytes
  have hstack : InRegion c.stackRegion c.stack 160 := by
    simpa only [BitVec.add_zero] using hv.stack_inRegion (off := 0) (len := 160) (by decide)
  have hdis := (hv.call.separation.2 c.stackRegion (by simp [Context.stackRegion])).1
    (Compress.inputRegion c.initial c.blocks) (List.mem_singleton_self _)
  refine ⟨h.registers, h.frame.stackPointer, h.inputPointer, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [BitVec.add_zero] using
      Machine.memoryWritable_slice h.frame.writable 0 160 (by decide)
  · refine ⟨Nat.le_trans hin.2.1 (Nat.le_of_lt hb), fun i hi ↦ ?_⟩
    exact Option.isSome_iff_exists.mpr (halloc _ (Common.StoreRegion.contains_byte hin hi))
  · intro i
    have hkp : k < (SHA2.SHA256.parse (SHA2.bytesToBits c.blocks)).size := by
      rw [Parser.parse_size]
      exact hk
    have hm : c.message k = (SHA2.SHA256.parse (SHA2.bytesToBits c.blocks))[k]'hkp := by
      simp only [Context.message,
        getElem?_pos (SHA2.SHA256.parse (SHA2.bytesToBits c.blocks)) k hkp, Option.getD_some]
    rw [hm]
    change memLoad s.external (c.input k + BitVec.ofNat 64 (4 * i.val)) 32 = _
    rw [Context.input, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact Input.memLoad_parse_at hbytes k i.val hk i.isLt
  · intro i hi j hj he
    have hs := Common.StoreRegion.contains_byte hstack hi
    rw [he] at hs
    exact hdis _ (Common.StoreRegion.contains_byte hin hj) hs
  · intro i hi hp
    exact hv.outputContract.stack.avoids _ (Common.StoreRegion.contains_byte hstack hi) (.inl hp)

theorem Context.Valid.stack_outside_output {c : Context} {bindings : Bindings}
    (hv : c.Valid bindings) {off len : Nat} (hb : off + len ≤ 216) :
    Outside [Compress.outputRegion c.initial] (c.stack + BitVec.ofNat 64 off) len := by
  have hin := hv.stack_inRegion hb
  have hs := hv.stack_bounds
  have hap : (Compress.outputRegion c.initial).start + (Compress.outputRegion c.initial).size ≤
      c.stackRegion.start ∨ c.stackRegion.start + c.stackRegion.size ≤
        (Compress.outputRegion c.initial).start := by
    apply Classical.byContradiction
    intro hn
    have hf := hv.call.separation.1
      (max (Compress.outputRegion c.initial).start c.stackRegion.start)
    apply hf
    · change (c.initial.regValue .rdi).toNat ≤
        max (c.initial.regValue .rdi).toNat (c.sp.toNat - 336) ∧
        max (c.initial.regValue .rdi).toNat (c.sp.toNat - 336) <
          (c.initial.regValue .rdi).toNat + 20
      change ¬ ((c.initial.regValue .rdi).toNat + 20 ≤ c.sp.toNat - 336 ∨
        c.sp.toNat - 336 + (c.sp.toNat + 8 - (c.sp.toNat - 336)) ≤
          (c.initial.regValue .rdi).toNat) at hn
      constructor <;> omega
    · change c.sp.toNat - 336 ≤
        max (c.initial.regValue .rdi).toNat (c.sp.toNat - 336) ∧
        max (c.initial.regValue .rdi).toNat (c.sp.toNat - 336) <
          c.sp.toNat - 336 + (c.sp.toNat + 8 - (c.sp.toNat - 336))
      change ¬ ((c.initial.regValue .rdi).toNat + 20 ≤ c.sp.toNat - 336 ∨
        c.sp.toNat - 336 + (c.sp.toNat + 8 - (c.sp.toNat - 336)) ≤
          (c.initial.regValue .rdi).toNat) at hn
      constructor <;> omega
  refine ⟨hin.2.2, ?_⟩
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  rcases hap with hap | hap
  · exact Or.inr (Nat.le_trans hap hin.1)
  · exact Or.inl (Nat.le_trans hin.2.1 hap)

end Sha1.Proofs.Compress.Routine
