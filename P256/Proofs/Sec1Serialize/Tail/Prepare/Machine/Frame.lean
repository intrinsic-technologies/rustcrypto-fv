import P256.Proofs.Sec1Serialize.State
import P256.Proofs.Common.Field.Operations.Run.Compose

set_option autoImplicit false

namespace P256.Proofs.Sec1Serialize.Prepare

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

variable [Bindings] {s t u : RamState} {boundary : ReturnBoundary}

structure EncodingPre (pc : BitVec 64) (codeLen lo hi : Nat) (t : RamState) : Prop where
  rip : t.RIP = pc
  readable : ∀ (c : BitVec 64) {len : Nat}, (SlotIn c len lo hi ∧ (c + BitVec.ofNat 64 lo).toNat % 8 = 0 ∧
    len ≤ 8 ∧ lo % 8 = 0) →
    MemReadable t (rspOf t + c) len
  writable : ∀ (c : BitVec 64) {len : Nat}, (SlotIn c len lo hi ∧ (c + BitVec.ofNat 64 lo).toNat % 8 = 0 ∧
    len ≤ 8 ∧ lo % 8 = 0) →
    MemWritable t (rspOf t + c) len
  apart : ∀ (c : BitVec 64) {len : Nat}, (SlotIn c len lo hi ∧ (c + BitVec.ofNat 64 lo).toNat % 8 = 0 ∧
    len ≤ 8 ∧ lo % 8 = 0) →
    ∀ (off ilen : Nat), off + ilen ≤ codeLen →
      RangeApart (rspOf t + c) len (pc + BitVec.ofNat 64 off) ilen

macro_rules
  | `(tactic| x86_frame) => `(tactic| first
    | with_reducible_and_instances
        exact EncodingPre.readable (by assumption) _ (by decide +kernel)
    | with_reducible_and_instances
        exact EncodingPre.writable (by assumption) _ (by decide +kernel)
    | with_reducible_and_instances
        exact EncodingPre.apart (by assumption) _ (by decide +kernel) _ _ (by decide +kernel))

theorem prepare_stack_frame
    (pre : CalleePre s boundary 0x110d70 72 65 328)
    (state : FrameState s t 65 328 312) {codeOffset codeLen : Nat}
    (hc : codeOffset + codeLen ≤ 118431)
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 codeOffset) :
    EncodingPre (Extracted.textAddress + BitVec.ofNat 64 codeOffset) codeLen 0 264 t := by
  refine ⟨rip, ?_, ?_, ?_⟩
  · intro c len h
    have bound : c.toNat + len ≤ 264 := by simpa [SlotIn] using h.1
    have hr := stack_readable (frameOffset := 312) pre state (offset := c.toNat) (len := len) (by decide) (by omega)
    change MemReadable t (stackPtr t + c) len
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using hr
  · intro c len h
    have bound : c.toNat + len ≤ 264 := by simpa [SlotIn] using h.1
    have align : c.toNat % 8 = 0 := by simpa [SlotIn] using h.2.1
    have hs := (stack_bounds pre.stack).1
    have ha : (stackPtr s).toNat % 16 = 8 := pre.stack.2.2.2
    have offset : (312 - c.toNat) % 8 = 0 := by omega
    have hw := writable_of_grow
      (stack_sub_writable pre.stack
        (fun a ha hr => pre.avoids _ (by simp) a ha (.inr hr))
        (offset := 312 - c.toNat) (len := 8) (by omega) (by omega) (by decide)
        (by
          rw [stack_sub_toNat pre.stack (by omega)]
          have hm := Nat.mod_mod_of_dvd ((stackPtr s).toNat - (312 - c.toNat))
            (show 8 ∣ 4096 by decide)
          omega)) state.allocated
    have addr := scalar_stack_address (frameOffset := 312) state.rsp
      (offset := c.toNat) (by decide) (by omega)
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq] at addr
    change MemWritable t (stackPtr t + c) len
    rw [addr]
    have hlen := h.2.2.1
    exact ⟨by have := hw.low; omega, fun i hi => hw.mem i (by omega),
      hw.tables.sub (Nat.le_refl _) (by omega)⟩
  · intro c len h off ilen hoff
    have bound : c.toNat + len ≤ 264 := by simpa [SlotIn] using h.1
    have hr := stack_code (frameOffset := 312) pre state (offset := c.toNat) (len := len)
      (codeOffset := codeOffset + off) (codeLen := ilen)
      (by decide) (by omega) (by omega)
    change RangeApart (stackPtr t + c) len _ ilen
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.ofNat_add, BitVec.add_assoc] using hr

def EncodingComponent (base : BitVec 64) : Component → Prop
  | .reg r => r.toNat < 16
  | .rip | .flags => True
  | .mem address len => ∃ offset : Nat, address = base + BitVec.ofNat 64 offset ∧ offset + len ≤ 264
  | _ => False

omit [Bindings] in
theorem encodingComponent_covers {base a : BitVec 64} {c : Component}
    (h : EncodingComponent base c) (ha : c.Covers a) :
    (Component.mem base 264).Covers a := by
  cases c <;> try exact ha.elim
  obtain ⟨offset, rfl, hl⟩ := h
  obtain ⟨i, hi, rfl⟩ := ha
  exact ⟨offset+i, by omega, by rw [BitVec.ofNat_add, BitVec.add_assoc]⟩

theorem state_of_encoding {e : Effect}
    (pre : CalleePre s boundary 0x110d70 72 65 328)
    (state : FrameState s t 65 328 312) (ready : ReadyToStep u) (effect : e.Holds t u)
    (hcs : ∀ c ∈ e.components, EncodingComponent (rspOf t) c)
    (rsp : Component.reg 4 ∉ e.components) : FrameState s u 65 328 312 := by
  apply state.after_effect pre (by decide) ready effect.agrees ?_ rsp
    (hdf := fun hc => hcs _ hc) (hmxcsr := fun hc => hcs _ hc)
    (hfcw := fun hc => hcs _ hc)
  · intro c hc a ha
    have cover := encodingComponent_covers (hcs c hc) ha
    change (Component.mem (stackPtr t) 264).Covers a at cover
    rw [state.rsp] at cover
    exact ⟨workRegion s 328, by simp, work_contains pre (by decide) (by decide) cover⟩

end P256.Proofs.Sec1Serialize.Prepare
