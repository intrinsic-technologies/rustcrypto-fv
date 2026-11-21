import Sha2.Proofs.Wrapper512.Absorb.State
import Sha2.Proofs.Common.Memory.LoadBytes
import Sha2.Proofs.Wrapper512.Dispatch.Initialize

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Absorb

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.SHA512
open Sha2.Proofs.Wrapper512


theorem loadBytes_of_bytes_at {before after : Ram} {a b : BitVec 64}
    {count : Nat} {value : BitVec 64}
    (same : ∀ i < count,
      after[b + BitVec.ofNat 64 i]? = before[a + BitVec.ofNat 64 i]?)
    (loaded : loadBytes before a count = .ok value) :
    loadBytes after b count = .ok value := by
  have loop : ∀ (n offset shift accumulator : Nat),
      offset + n ≤ count →
      loadBytes.loop before a n offset shift accumulator = .ok value →
      loadBytes.loop after b n offset shift accumulator = .ok value := by
    intro n
    induction n with
    | zero => intro offset shift accumulator bound h; exact h
    | succ n ih =>
      intro offset shift accumulator bound h
      simp only [loadBytes.loop, addAddress, fromNat] at h ⊢
      have eq := same offset (by omega)
      rw [eq]
      split at h
      · contradiction
      · rename_i byte hb
        rw [hb]
        apply ih (offset + 1) (shift + 8) (accumulator + byte.toNat * 2 ^ shift)
          (by omega)
        exact h
  have hloop : loadBytes.loop before a count 0 0 0 = .ok value := loaded
  exact loop count 0 0 0 (by omega) hloop

theorem hashState_of_bytes {s t : RamState} {a b : BitVec 64} {hash : Array UInt64}
    (input : HashStateAt s a hash)
    (bytes : ∀ i < 64, t.external[b + BitVec.ofNat 64 i]? =
      s.external[a + BitVec.ofNat 64 i]?) :
    HashStateAt t b hash := by
  refine ⟨input.1, fun i hi => ?_⟩
  apply loadBytes_of_bytes_at
  · intro j hj
    have eq := bytes (8 * i + j) (by omega)
    calc
      t.external[b + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j]? =
          t.external[b + BitVec.ofNat 64 (8 * i + j)]? := by
            rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      _ = s.external[a + BitVec.ofNat 64 (8 * i + j)]? := eq
      _ = s.external[a + BitVec.ofNat 64 (8 * i) + BitVec.ofNat 64 j]? := by
            rw [BitVec.add_assoc, ← BitVec.ofNat_add]

  · exact input.2 i hi

theorem preserved_of_bytes [Bindings] {v : Variant} {initial s t : RamState} {form : Form}
    (input : Preserved v initial s form) (state : State v initial t form)
    (bytes : match form with
      | .slices => ∀ a, (Component.mem (stackPtr initial - 624) 24).Covers a →
          t.external[a]? = s.external[a]?
      | .digest => True
      | _ => ∀ offset ∈ [form.outputSlot, form.secondOutputSlot, form.pointerSlot, form.lengthSlot],
          ∀ a, (Component.mem (stackPtr initial - BitVec.ofNat 64 offset) 8).Covers a →
            t.external[a]? = s.external[a]?)
    (keptOutput : form = .digest → t.regValue .rbx = s.regValue .rbx := by simp)
    (keptFrameOutput : form = .traitFinalizeIntoReset false →
      t.regValue (if v = .sha512 then .r13 else .rbp) =
        s.regValue (if v = .sha512 then .r13 else .rbp) ∨
      memLoad s.external (outputSavePointer initial form) 64 = initial.regValue .rcx := by simp) :
    Preserved v initial t form := by
  cases form with
  | digest => exact ⟨state, (keptOutput rfl).trans input.outputPointer, trivial, trivial⟩
  | reset stage | finalizeIntoReset second | traitFinalizeIntoReset second =>
    have same (offset : Nat)
        (unchanged : ∀ a, (Component.mem (stackPtr initial - BitVec.ofNat 64 offset) 8).Covers a →
          t.external[a]? = s.external[a]?) :
        memLoad t.external (stackPtr initial - BitVec.ofNat 64 offset) 64 =
          memLoad s.external (stackPtr initial - BitVec.ofNat 64 offset) 64 := by
      apply memLoad_congr
      intro j hj
      change (t.external[_]?).getD 0 = (s.external[_]?).getD 0
      rw [unchanged _ ⟨j, hj, rfl⟩]
    refine ⟨state, ⟨?_, ?_⟩, ?_, ?_⟩
    · rcases input.outputPointer.1 with h | ⟨h, hr⟩
      · exact .inl ((same _ (bytes _ (by simp))).trans h)
      · rcases keptFrameOutput h with kept | saved
        · exact .inr ⟨h, kept.trans hr⟩
        · have transferred := (same _ (bytes _ (by simp))).trans saved
          cases h <;> (apply Or.inl
                       simpa only [outputSavePointer, Form.secondOutput, Bool.false_eq_true, ite_false]
                         using transferred)
    · exact (same _ (bytes _ (by simp))).trans input.outputPointer.2
    · exact (same _ (bytes _ (by simp))).trans input.pointerTable
    · exact (same _ (bytes _ (by simp))).trans input.lengthTable
  | slices =>

    have same (offset : Nat) (lo : 608 ≤ offset) (hi : offset ≤ 624) :
        memLoad t.external (stackPtr initial - BitVec.ofNat 64 offset) 64 =
          memLoad s.external (stackPtr initial - BitVec.ofNat 64 offset) 64 := by
      apply memLoad_congr
      intro i bound
      change (t.external[_]?).getD 0 = (s.external[_]?).getD 0
      rw [bytes _ ⟨624-offset+i, by omega, ?_⟩]
      rw [BitVec.ofNat_add, ← BitVec.ofNat_sub_ofNat_of_le 624 offset (by omega) hi]
      calc
        _ = (stackPtr initial - 624 + 624) - BitVec.ofNat 64 offset + BitVec.ofNat 64 i := by
          rw [BitVec.sub_add_cancel]
        _ = _ := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.ofNat_eq_ofNat]
    exact ⟨state, (same 624 (by decide) (by decide)).trans input.outputPointer,
      (same 616 (by decide) (by decide)).trans input.pointerTable,
      (same 608 (by decide) (by decide)).trans input.lengthTable⟩

theorem frame_bytes [Bindings] {v : Variant} {initial s t : RamState} {inputs : Array Input}
    {form : Form} {output count reserve offset len : Nat} (ctx : Context v initial inputs form)
    (frame : MemoryWriteFrame s t #v[
      (⟨(stackPtr initial - BitVec.ofNat 64 output).toNat, count⟩ : MemoryRegion),
      (⟨(stackPtr initial - BitVec.ofNat 64 reserve).toNat, reserve-form.frameBytes⟩ : MemoryRegion)])
    (outLow : output ≤ form.frameBytes) (_outHigh : count ≤ output)
    (resLow : form.frameBytes ≤ reserve) (resHigh : reserve ≤ form.stackBytes)
    (low : offset ≤ form.frameBytes) (high : len ≤ offset)
    (apart : output + len ≤ offset ∨ offset + count ≤ output) :
    ∀ i < len, t.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      s.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  intro i hi
  apply frame
  intro region member contains
  have budget := show (v.routine form).minStackBytes = form.stackBytes from rfl
  have frameBound : form.frameBytes ≤ form.stackBytes := by cases form <;> dsimp only [Form.frameBytes, Form.stackBytes] <;> decide
  have bounds := Dispatch.stack_bounds512 ctx
  have outNat := Dispatch.stack_sub_toNat512 ctx (offset := output) (by omega)
  have resNat := Dispatch.stack_sub_toNat512 ctx resHigh
  have address : (stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat =
      (stackPtr initial).toNat - offset + i := by
    rw [BitVec.toNat_add, Dispatch.stack_sub_toNat512 ctx (by omega), BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have cases : region = (⟨(stackPtr initial - BitVec.ofNat 64 output).toNat, count⟩ : MemoryRegion) ∨
      region = (⟨(stackPtr initial - BitVec.ofNat 64 reserve).toNat, reserve-form.frameBytes⟩ : MemoryRegion) := by
    simpa using member
  rcases cases with rfl | rfl
  · change (stackPtr initial - BitVec.ofNat 64 output).toNat ≤ _ ∧
      _ < (stackPtr initial - BitVec.ofNat 64 output).toNat + count at contains
    rw [outNat, address] at contains
    rcases apart with apart | apart <;> omega
  · change (stackPtr initial - BitVec.ofNat 64 reserve).toNat ≤ _ ∧
      _ < (stackPtr initial - BitVec.ofNat 64 reserve).toNat + (reserve-form.frameBytes) at contains
    rw [resNat, address] at contains
    omega


def _root_.Sha2.Proofs.Wrapper512.Form.metadataSlots (form : Form) : List Nat :=
  [form.outputSlot, form.secondOutputSlot, form.pointerSlot, form.lengthSlot]

def LocalWrites (initial : RamState) (components : List Component) (form : Form := .slices) : Prop :=
  ∀ c ∈ components, ∀ a, c.Covers a →
    match form with
    | .slices | .digest => (Component.mem (stackPtr initial - BitVec.ofNat 64 form.stackBytes) (form.stackBytes - 624)).Covers a ∨
    (Component.mem (stackPtr initial - 600) 552).Covers a
    | _ =>
      (Component.mem (stackPtr initial - BitVec.ofNat 64 form.stackBytes)
        (form.stackBytes - 48)).Covers a ∧
      ∀ slot ∈ form.metadataSlots,
        ¬ (Component.mem (stackPtr initial - BitVec.ofNat 64 slot) 8).Covers a

theorem local_memory {initial : RamState} {offset len : Nat} {form : Form}
    (lo : offset ≤ form.stackBytes) (hi : len + 48 ≤ offset)
    (apart : match form with
      | .slices | .digest => len + 624 ≤ offset ∨ offset ≤ 600
      | _ => ∀ slot ∈ form.metadataSlots,
          OffsetsApart (-(BitVec.ofNat 64 offset)) len (-(BitVec.ofNat 64 slot)) 8) :
    ∀ a, (Component.mem (stackPtr initial - BitVec.ofNat 64 offset) len).Covers a →
      match form with
      | .slices | .digest =>
        (Component.mem (stackPtr initial - BitVec.ofNat 64 form.stackBytes)
          (form.stackBytes - 624)).Covers a ∨
        (Component.mem (stackPtr initial - 600) 552).Covers a
      | _ =>
        (Component.mem (stackPtr initial - BitVec.ofNat 64 form.stackBytes)
          (form.stackBytes - 48)).Covers a ∧
        ∀ slot ∈ form.metadataSlots,
          ¬ (Component.mem (stackPtr initial - BitVec.ofNat 64 slot) 8).Covers a := by
  have covered (reserve : Nat) (reserveBound : reserve < 2^64)
      (offsetBound : offset ≤ reserve) (a : BitVec 64)
      (ha : (Component.mem (stackPtr initial - BitVec.ofNat 64 offset) len).Covers a) :
      (Component.mem (stackPtr initial - BitVec.ofNat 64 reserve) (reserve - 48)).Covers a := by
    obtain ⟨i, hi', rfl⟩ := ha
    refine ⟨reserve - offset + i, by omega, ?_⟩
    rw [BitVec.ofNat_add, ← BitVec.ofNat_sub_ofNat_of_le reserve offset (by omega) offsetBound]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rw [← BitVec.add_assoc (-(BitVec.ofNat 64 reserve)), BitVec.add_left_neg, BitVec.zero_add]
  have legacy (apart : len + 624 ≤ offset ∨ offset ≤ 600) :
      ∀ a, (Component.mem (stackPtr initial - BitVec.ofNat 64 offset) len).Covers a →
        (Component.mem (stackPtr initial - BitVec.ofNat 64 form.stackBytes)
          (form.stackBytes - 624)).Covers a ∨
        (Component.mem (stackPtr initial - 600) 552).Covers a := by
    have bound : form.stackBytes < 2^64 := by cases form <;> dsimp only [Form.frameBytes, Form.stackBytes] <;> decide
    intro a ha
    obtain ⟨i, hi', rfl⟩ := ha
    rcases apart with below | above
    · left
      refine ⟨form.stackBytes-offset+i, by omega, ?_⟩
      rw [BitVec.ofNat_add, ← BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)]
      calc
        _ = (stackPtr initial - BitVec.ofNat 64 form.stackBytes + BitVec.ofNat 64 form.stackBytes) - BitVec.ofNat 64 offset + BitVec.ofNat 64 i := by
          rw [BitVec.sub_add_cancel]
        _ = _ := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    · right
      refine ⟨600-offset+i, by omega, ?_⟩
      rw [BitVec.ofNat_add, ← BitVec.ofNat_sub_ofNat_of_le _ _ (by omega) (by omega)]
      calc
        _ = (stackPtr initial - 600 + 600) - BitVec.ofNat 64 offset + BitVec.ofNat 64 i := by
          rw [BitVec.sub_add_cancel]
        _ = _ := by simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.ofNat_eq_ofNat]
  cases form with
  | reset stage | finalizeIntoReset second | traitFinalizeIntoReset second =>
    have bound : offset + 8 < 2^64 := by
      dsimp only [Form.stackBytes] at lo
      omega
    intro a ha
    obtain ⟨i, hi', rfl⟩ := ha
    constructor
    · exact covered _ (by dsimp only [Form.stackBytes]; decide) lo _ ⟨i, hi', rfl⟩
    · intro slot member covers
      obtain ⟨j, hj, eq⟩ := covers
      exact OffsetsApart.ne (apart slot member) (stackPtr initial) hi' hj (by omega)
        (by simpa only [BitVec.sub_eq_add_neg] using eq)
  | slices | digest => exact legacy apart

theorem LocalWrites.stack [Bindings] {v : Variant} {initial : RamState} {inputs : Array Input}
    {components : List Component} {form : Form} (h : LocalWrites initial components form)
    (ctx : Context v initial inputs form) :
    WritesWithin components #v[Stack.region initial (v.routine form).minStackBytes] := by
  intro c hc a ha
  refine ⟨Stack.region initial (v.routine form).minStackBytes,
    by simp, ?_⟩
  cases form with
  | reset stage | finalizeIntoReset second | traitFinalizeIntoReset second =>
    apply stackRegion_contains_sub ctx.stack.2.2.1 (Nat.le_refl _) _ (h c hc a ha).1
    dsimp only [Variant.routine, Form.stackBytes]
    omega
  | slices | digest =>
    rcases h c hc a ha with low | high
    · exact stackRegion_contains_sub ctx.stack.2.2.1 (Nat.le_refl _) (by dsimp only [Variant.routine, Form.stackBytes]; decide) low
    · exact stackRegion_contains_sub ctx.stack.2.2.1 (by dsimp only [Variant.routine, Form.stackBytes]; decide) (by decide) high

theorem LocalWrites.within [Bindings] {v : Variant} {initial : RamState} {inputs : Array Input}
    {components : List Component} {form : Form} (h : LocalWrites initial components form)
    (ctx : Context v initial inputs form) :
    WritesWithin components (v.writeRegions initial form) := by
  intro c hc a ha
  obtain ⟨region, member, contains⟩ := h.stack ctx c hc a ha
  have eq : region = Stack.region initial (v.routine form).minStackBytes := by simpa using member
  subst region
  exact ⟨_, by cases form <;> exact ⟨by simp [Variant.writeRegions, Variant.routine]⟩, contains⟩

theorem LocalWrites.saved {initial : RamState} {components : List Component} {form : Form}
    (h : LocalWrites initial components form) :
    ∀ c ∈ components, ∀ a,
      (Component.mem (stackPtr initial - 48) 56).Covers a → ¬ c.Covers a := by
  have lowApart : OffsetsApart (-48) 56 (-(BitVec.ofNat 64 form.stackBytes)) (form.stackBytes - 624) := by
    cases form <;> dsimp only [Form.stackBytes] <;> unfold OffsetsApart <;> decide +kernel
  have allApart : OffsetsApart (-48) 56 (-(BitVec.ofNat 64 form.stackBytes)) (form.stackBytes - 48) := by
    cases form <;> dsimp only [Form.stackBytes] <;> unfold OffsetsApart <;> decide +kernel
  intro c hc a ha hw
  obtain ⟨i, hi, rfl⟩ := ha
  cases form with
  | reset stage | finalizeIntoReset second | traitFinalizeIntoReset second =>
    obtain ⟨j, hj, he⟩ := (h c hc _ hw).1
    exact OffsetsApart.ne allApart (stackPtr initial) hi hj (by dsimp only [Form.stackBytes]; decide)
      (by simpa only [BitVec.sub_eq_add_neg] using he)
  | slices | digest =>
    rcases h c hc _ hw with ⟨j, hj, he⟩ | ⟨j, hj, he⟩
    · exact OffsetsApart.ne lowApart (stackPtr initial) hi hj (by decide)
        (by simpa only [BitVec.sub_eq_add_neg] using he)
    · exact OffsetsApart.ne (c₁ := -48) (len₁ := 56) (c₂ := -600) (len₂ := 552)
        (by unfold OffsetsApart; decide +kernel) (stackPtr initial) hi hj (by decide)
        (by simpa only [BitVec.sub_eq_add_neg] using he)

theorem LocalWrites.memory {initial s t : RamState} {components : List Component} {form : Form}
    (h : LocalWrites initial components form) (frame : AgreesExcept components s t)
    {a : BitVec 64} (ha : match form with
      | .slices | .digest => (Component.mem (stackPtr initial - 624) 24).Covers a
      | _ => ∃ slot ∈ form.metadataSlots,
          (Component.mem (stackPtr initial - BitVec.ofNat 64 slot) 8).Covers a) :
    t.external[a]? = s.external[a]? := by
  have lowApart : OffsetsApart (-624) 24 (-(BitVec.ofNat 64 form.stackBytes)) (form.stackBytes - 624) := by
    cases form <;> dsimp only [Form.stackBytes] <;> unfold OffsetsApart <;> decide +kernel
  apply frame.memory
  intro c hc hw
  cases form with
  | reset stage | finalizeIntoReset second | traitFinalizeIntoReset second =>
    obtain ⟨slot, member, covers⟩ := ha
    exact (h c hc a hw).2 slot member covers
  | slices | digest =>
    obtain ⟨i, hi, rfl⟩ := ha
    rcases h c hc _ hw with ⟨j, hj, he⟩ | ⟨j, hj, he⟩
    · exact OffsetsApart.ne lowApart (stackPtr initial) hi hj (by decide)
        (by simpa only [BitVec.sub_eq_add_neg] using he)
    · exact OffsetsApart.ne (c₁ := -624) (len₁ := 24) (c₂ := -600) (len₂ := 552)
        (by unfold OffsetsApart; decide +kernel) (stackPtr initial) hi hj (by decide)
        (by simpa only [BitVec.sub_eq_add_neg] using he)

theorem preserved_of_agrees [Bindings] {v : Variant} {initial s t : RamState} {inputs : Array Input}
    {fuel : Nat} {components : List Component} {form : Form}
    (ctx : Context v initial inputs form) (input : Preserved v initial s form)
    (run : Advances (returnBoundary initial) fuel s t) (ready : ReadyToStep t)
    (frame : AgreesExcept components s t) (writes : LocalWrites initial components form)
    (kept4 : Component.reg 4 ∉ components) (hdf : .df ∉ components := by simp)
    (keptOutput : form = .digest → Component.reg 3 ∉ components := by simp)
    (keptFrameOutput : form = .traitFinalizeIntoReset false →
      (Component.reg (if v = .sha512 then 13 else 5) ∉ components ∨
        memLoad s.external (outputSavePointer initial form) 64 = initial.regValue .rcx) := by simp) :
    Preserved v initial t form :=
  preserved_of_bytes input
    (State.of_agrees input.toState ctx run ready frame (writes.within ctx) kept4 writes.saved hdf)
    (by cases form with
        | slices => exact fun _ ha => writes.memory frame ha
        | digest => trivial
        | reset stage | finalizeIntoReset second | traitFinalizeIntoReset second =>
          exact fun slot member a ha => writes.memory frame ⟨slot, member, ha⟩)
    (fun hd => frame.read (n := 64) (r := 3) (keptOutput hd))
    (fun hf => by
      rcases keptFrameOutput hf with kept | saved
      · left
        have h := frame.read (n := 64) (r := if v = .sha512 then 13 else 5) kept
        cases v <;> exact h
      · exact .inr saved)


end Sha2.Proofs.Wrapper512.Absorb
