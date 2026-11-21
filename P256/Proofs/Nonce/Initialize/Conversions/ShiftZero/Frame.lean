import P256.Proofs.Nonce.Initialize.Conversions.ShiftZero.State
import P256.Proofs.Program.ScalarFrame.Memory
import P256.Proofs.Common.Encoding.Serialize.Convert.SavePointer
import X86Proofs.Program.Compose

set_option autoImplicit false

open P256.Proofs.Program (memoryRegion_contains_add memoryRegion_memReadable stack_region_end)

namespace P256.Proofs.Nonce.Initialize.Conversions.ShiftZero

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

open P256.Proofs.Program

theorem agrees_of_footprint {s t : RamState} {small large : List Component}
    (h : AgreesExcept small s t)
    (hreg : ∀ c ∈ small, c.isMem = false → c ∈ large)
    (hmem : ∀ c ∈ small, ∀ a, c.Covers a → ∃ d ∈ large, d.Covers a) :
    AgreesExcept large s t := by
  refine ⟨?_, ?_, h.rest, h.grow⟩
  · intro c hc hm
    exact h.agree c (fun hs => hc (hreg c hs hm)) hm
  · intro a ha
    apply h.memory a
    intro c hc hcover
    obtain ⟨d, hd, hcover'⟩ := hmem c hc a hcover
    exact ha d hd hcover'

variable [Bindings] {s t u : RamState} {boundary : ReturnBoundary}

theorem stack_contains (pre : P256.Proofs.Program.CalleePre s boundary 0x109530 32 32 128)
    {offset len : Nat} (ho : offset ≤ 128) (hl : len ≤ offset + 8)
    {a : BitVec 64} (h : (Component.mem (s.regValue .rsp - BitVec.ofNat 64 offset) len).Covers a) :
    (Stack.region s 128).Contains a.toNat := by
  obtain ⟨i, hi, rfl⟩ := h
  apply memoryRegion_contains_add pre.stack.1 (len := len) _ _ hi
  · rw [show (s.regValue .rsp - BitVec.ofNat 64 offset).toNat =
        (stackPtr s).toNat - offset from stack_sub_toNat pre.stack ho]
    change (stackPtr s).toNat - 128 ≤ _
    omega
  · rw [stack_region_end, show (s.regValue .rsp - BitVec.ofNat 64 offset).toNat =
        (stackPtr s).toNat - offset from stack_sub_toNat pre.stack ho]
    have := (stack_bounds pre.stack).1
    omega

theorem frame_within (pre : P256.Proofs.Program.CalleePre s boundary 0x109530 32 32 128) :
    WritesWithin (frame s) #v[registerRegion s .rdi 32, Stack.region s 128] := by
  intro c hc address hcover
  rcases List.mem_append.mp hc with hc | hc
  · obtain ⟨i, _, rfl⟩ := List.mem_map.mp hc
    exact hcover.elim
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact hcover.elim
    · exact hcover.elim
    · exact ⟨Stack.region s 128, by simp, stack_contains pre (by decide) (by decide) hcover⟩
    · obtain ⟨i, hi, rfl⟩ := hcover
      exact ⟨registerRegion s .rdi 32, by simp,
        memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) hi⟩

theorem loaded_of_frame (pre : P256.Proofs.Program.CalleePre s boundary 0x109530 32 32 128)
    (h : AgreesExcept (frame s) s t) : ProgramLoaded t :=
  ScalarFrame.loaded_of_frame pre (h.memoryWriteFrame (frame_within pre))

omit [Bindings] in
theorem register_mem_frame (s : RamState) (r : BitVec 5) (h : r.toNat < 16) :
    Component.reg r ∈ frame s := by
  apply List.mem_append_left
  exact List.mem_map.mpr ⟨r.toNat, by simp [h], by simp⟩

omit [Bindings] in
theorem stack_covers {address : BitVec 64} {offset len : Nat}
    (ho : offset ≤ 128) (hl : len ≤ offset)
    (h : (Component.mem (s.regValue .rsp - BitVec.ofNat 64 offset) len).Covers address) :
    (Component.mem (s.regValue .rsp - 128) 128).Covers address := by
  obtain ⟨i, hi, rfl⟩ := h
  refine ⟨128 - offset + i, by omega, ?_⟩
  rw [BitVec.ofNat_add, ← BitVec.ofNat_sub_ofNat_of_le 128 offset (by omega) ho]
  have cancel : (s.regValue .rsp - BitVec.ofNat 64 128) +
      (BitVec.ofNat 64 128 - BitVec.ofNat 64 offset) = s.regValue .rsp - BitVec.ofNat 64 offset := by
    rw [BitVec.sub_eq_add_neg (BitVec.ofNat 64 128), ← BitVec.add_assoc,
      BitVec.sub_add_cancel, ← BitVec.sub_eq_add_neg]
  change s.regValue .rsp - BitVec.ofNat 64 offset + BitVec.ofNat 64 i =
    (s.regValue .rsp - BitVec.ofNat 64 128) +
      (BitVec.ofNat 64 128 - BitVec.ofNat 64 offset + BitVec.ofNat 64 i)
  rw [← BitVec.add_assoc, cancel]

def BodyComponent (base : BitVec 64) : Component → Prop
  | .reg r => r.toNat < 16
  | .flags | .rip => True
  | .mem address len => ∃ offset : Nat, address = base + BitVec.ofNat 64 offset ∧ offset + len ≤ 24
  | _ => False

omit [Bindings] in
theorem body_covers {base a : BitVec 64} {c : Component}
    (hc : BodyComponent base c) (ha : c.Covers a) :
    (Component.mem base 24).Covers a := by
  cases c <;> try exact ha.elim
  obtain ⟨offset, rfl, hl⟩ := hc
  obtain ⟨i, hi, rfl⟩ := ha
  exact ⟨offset + i, by omega, by rw [BitVec.ofNat_add, BitVec.add_assoc]⟩

theorem Stage.of_effect {fuel : Nat} {e : Effect} (pre : P256.Proofs.Program.CalleePre s boundary 0x109530 32 32 128)
    (stage : Stage s t boundary) (run : Advances boundary fuel t u)
    (ready : ReadyToStep u) (effect : e.Holds t u)
    (hcs : ∀ c ∈ e.components, BodyComponent (rspOf t) c)
    (hsp : Component.reg 4 ∉ e.components) : Stage s u boundary := by
  have sp : rspOf t = s.regValue .rsp - 72 := stage.rsp
  have small : AgreesExcept (frame s) t u := by
    apply agrees_of_footprint effect.agrees
    · intro c hc hm
      have h := hcs c hc
      cases c with
      | reg r => exact register_mem_frame s r h
      | flags => simp [frame]
      | rip => simp [frame]
      | mem => contradiction
      | _ => exact h.elim
    · intro c hc a ha
      have h := body_covers (hcs c hc) ha
      rw [sp] at h
      exact ⟨.mem (s.regValue .rsp - 128) 128, by simp [frame]; rfl,
        stack_covers (offset := 72) (by decide) (by decide) h⟩
  have whole : AgreesExcept (frame s) s u :=
    (stage.agrees.trans small).mono fun _ hc => (List.mem_append.mp hc).elim id id
  refine ⟨?_, ready, whole, loaded_of_frame pre whole,
    (effect.agrees.read (n := 64) hsp).trans stage.rsp, ?_⟩
  · obtain ⟨n, hn⟩ := stage.execution
    exact ⟨n + fuel, hn.trans run⟩
  · intro saved hsaved
    have hs : saved.2 ≤ 48 := by
      simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at hsaved
      rcases hsaved with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    rw [P256.Proofs.Common.Encoding.Serialize.read_mem_of_agrees effect.agrees]
    · exact stage.saved saved hsaved
    · intro i hi c hc ha
      have h := body_covers (hcs c hc) ha
      rw [sp] at h
      obtain ⟨j, hj, he⟩ := h
      have apart : RangeApart (s.regValue .rsp - 72) 24
          (s.regValue .rsp - BitVec.ofNat 64 saved.2) 8 := by
        have h₁ : (s.regValue .rsp - 72).toNat = (stackPtr s).toNat - 72 :=
          stack_sub_toNat pre.stack (offset := 72) (by decide)
        have h₂ : (s.regValue .rsp - BitVec.ofNat 64 saved.2).toNat = (stackPtr s).toNat - saved.2 :=
          stack_sub_toNat pre.stack (by omega)
        have hb := stack_bounds pre.stack
        apply RangeApart.of_toNat
        · rw [h₁]; omega
        · rw [h₂]; omega
        · rw [h₁, h₂]; omega
      exact apart j hj i hi he.symm

theorem Stage.input_readable (pre : P256.Proofs.Program.CalleePre s boundary 0x109530 32 32 128) (stage : Stage s t boundary)
    {offset len : Nat} (bound : offset + len ≤ 32) :
    MemReadable t (s.regValue .rsi + BitVec.ofNat 64 offset) len := by
  apply readable_of_grow _ stage.agrees.grow
  apply memoryRegion_memReadable pre.inputBounded pre.inputAllocated
  · rw [BitVec.toNat_add_of_lt (by
      have hb := pre.inputBounded
      change (s.regValue .rsi).toNat + 32 < 2^32 at hb
      simp only [BitVec.toNat_ofNat]
      omega)]
    simp only [BitVec.toNat_ofNat]
    change (s.regValue .rsi).toNat ≤ _
    omega
  · rw [BitVec.toNat_add_of_lt (by
      have hb := pre.inputBounded
      change (s.regValue .rsi).toNat + 32 < 2^32 at hb
      simp only [BitVec.toNat_ofNat]
      omega)]
    simp only [BitVec.toNat_ofNat]
    change _ ≤ (s.regValue .rsi).toNat + 32
    omega

end P256.Proofs.Nonce.Initialize.Conversions.ShiftZero
