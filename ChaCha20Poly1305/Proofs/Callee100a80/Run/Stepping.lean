import ChaCha20Poly1305.Proofs.Callee100a80.Defs
import ChaCha20Poly1305.Proofs.Callee100a80.Run.Shared
import ChaCha20Poly1305.Proofs.Callee100a80.Cuts.Rounds
import ChaCha20Poly1305.Proofs.Callee100a80.Cuts.Xor
import ChaCha20Poly1305.Proofs.Callee100a80.Cuts.Tail
import X86Proofs.Instructions.Mov.Generated.MR.Triple
import X86Proofs.Instructions.Mov.Generated.RM.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.NopMem.Triple
import X86Proofs.Instructions.Cmp.Generated.MR.Triple
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.MovStore.Triple

namespace ChaCha20Poly1305.Proofs.Callee100a80.Run

open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Spec.Program
open Standards.RFC.ChaCha20Poly1305 ChaCha20Poly1305.Proofs.ChaCha20

section Helpers

theorem region_addr (r : MemoryRegion) (off i : Nat) :
    BitVec.ofNat 64 (r.start + off) + BitVec.ofNat 64 i = BitVec.ofNat 64 (r.start + (off + i)) := by
  rw [← BitVec.ofNat_add, Nat.add_assoc]

theorem region_toNat {r : MemoryRegion} (hl : r.start + r.size ≤ 2 ^ 32) {off : Nat}
    (h : off ≤ r.size) : (BitVec.ofNat 64 (r.start + off)).toNat = r.start + off := by
  rw [BitVec.toNat_ofNat]; omega

                                                                                            
                             
theorem region_writable {s t : RamState} {r : MemoryRegion} (hw : Writable s r)
    (hg : ∀ x : BitVec 64, (s.external[x]?).isSome → (t.external[x]?).isSome)
    (off n : Nat) (hn : 0 < n) (h : off + n ≤ r.size) :
    MemWritable t (BitVec.ofNat 64 (r.start + off)) n ∧
      ∀ i < n, ¬ InProgram (BitVec.ofNat 64 (r.start + off) + BitVec.ofNat 64 i) := by
  have hl := hw.low
  have ht := region_toNat hl (off := off) (by omega)
  refine ⟨⟨by omega, fun i hi => ?_, ?_⟩, fun i hi => ?_⟩
  · rw [region_addr r off i]
    exact hg _ (hw.present _ (by omega))
  · rw [ht]
    refine Classical.byContradiction fun hc => ?_
    simp only [PageTableEntriesApart] at hc
    have hx : r.Contains (max (r.start + off) 0x1000) := by
      simp only [MemoryRegion.Contains]; omega
    have := hw.avoids (BitVec.ofNat 64 (max (r.start + off) 0x1000))
      (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hx)
    apply this
    right
    simp only [pageTables, MemoryRegion.Contains]
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    omega
  · have := hw.avoids (BitVec.ofNat 64 (r.start + off) + BitVec.ofNat 64 i) (by
      rw [region_addr r off i, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      simp only [MemoryRegion.Contains]; omega)
    exact fun hp => this (.inl hp)

theorem sp_eq {s : RamState} (hlow : frameBytes ≤ (stackPtr s).toNat) :
    sp s = BitVec.ofNat 64 (stackRegion s).start := by
  unfold sp stackRegion
  apply BitVec.eq_of_toNat_eq
  rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; unfold frameBytes at hlow ⊢; omega)]
  simp only [BitVec.toNat_ofNat]
  unfold frameBytes at hlow ⊢
  omega

                                                                                             
theorem frame_stack_writable [Bindings] {s t : RamState} {key : Vector UInt8 32} {counter : UInt32}
    {nonce : Vector UInt8 12} {input output : BitVec 64} {message : ByteArray}
    (h : CallPre s key counter nonce input output message)
    (hg : ∀ x : BitVec 64, (s.external[x]?).isSome → (t.external[x]?).isSome)
    (off n : Nat) (hpos : 0 < n) (hn : off + n ≤ frameBytes) :
    MemWritable t (sp s + BitVec.ofNat 64 off) n ∧
      ∀ i < n, ¬ InProgram (sp s + BitVec.ofNat 64 off + BitVec.ofNat 64 i) := by
  have hr := region_writable h.stack hg off n hpos (by simp only [stackRegion]; omega)
  have he : sp s + BitVec.ofNat 64 off = BitVec.ofNat 64 ((stackRegion s).start + off) := by
    rw [sp_eq h.stackLow, ← BitVec.ofNat_add]
  rw [he]
  exact hr

                                                                                                
                                                             
def StackLocal (base : BitVec 64) (F : Nat → Prop) (O : BitVec 64 → Prop) (L : List Component) :
    Prop :=
  Component.reg 4 ∉ L ∧ (∀ c ∈ L, c.isMem = false → c ∈ Cuts.Rounds.regScratch) ∧
    ∀ c ∈ L, ∀ x, c.Covers x → (∃ i, F i ∧ i < 0x170 ∧ x = base + BitVec.ofNat 64 i) ∨ O x

theorem StackLocal.nc_slot {base : BitVec 64} {F : Nat → Prop} {O : BitVec 64 → Prop}
    {L : List Component} (h : StackLocal base F O L) {m : Nat} (hm : m < 2 ^ 32) (hF : ¬ F m)
    (hO : ¬ O (base + BitVec.ofNat 64 m)) :
    ∀ c ∈ L, ¬ c.Covers (base + BitVec.ofNat 64 m) := by
  intro c hc hcv
  rcases h.2.2 c hc _ hcv with ⟨i, hi, hl, he⟩ | ho
  · have := congrArg BitVec.toNat ((BitVec.add_right_inj base).mp he)
    simp only [BitVec.toNat_ofNat] at this
    rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
    subst this
    exact hF hi
  · exact hO ho

theorem StackLocal.nc_far {base : BitVec 64} {F : Nat → Prop} {O : BitVec 64 → Prop}
    {L : List Component} (h : StackLocal base F O L) (hb : base.toNat + 0x170 ≤ 2 ^ 32)
    {x : BitVec 64} (hx : x.toNat < base.toNat ∨ base.toNat + 0x170 ≤ x.toNat) (hO : ¬ O x) :
    ∀ c ∈ L, ¬ c.Covers x := by
  intro c hc hcv
  rcases h.2.2 c hc _ hcv with ⟨i, -, hl, rfl⟩ | ho
  · rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := i) (by omega),
      Nat.mod_eq_of_lt (by omega)] at hx
    omega
  · exact hO ho

theorem StackLocal.load {base : BitVec 64} {F : Nat → Prop} {O : BitVec 64 → Prop}
    {L : List Component} (h : StackLocal base F O L) {t u : RamState} (hag : AgreesExcept L t u)
    (n off : Nat) (hoff : off + n / 8 < 2 ^ 32) (hF : ∀ i < n / 8, ¬ F (off + i))
    (hO : ∀ i < n / 8, ¬ O (base + BitVec.ofNat 64 (off + i))) :
    memLoad u.external (base + BitVec.ofNat 64 off) n =
      memLoad t.external (base + BitVec.ofNat 64 off) n :=
  Cuts.Tail.slot_keep n hag off fun i hi => h.nc_slot (by omega) (hF i hi) (hO i hi)

                                                       
theorem out_far [Bindings] {s : RamState} {key : Vector UInt8 32} {counter : UInt32}
    {nonce : Vector UInt8 12} {input output : BitVec 64} {message : ByteArray}
    (h : CallPre s key counter nonce input output message) {i : Nat} (hi : i < message.size) :
    (output + BitVec.ofNat 64 i).toNat = output.toNat + i ∧
      (output.toNat + i < (stackRegion s).start ∨
        (stackRegion s).start + (stackRegion s).size ≤ output.toNat + i) := by
  have hl := h.out.low
  simp only [outputRegion] at hl
  have ht : (output + BitVec.ofNat 64 i).toNat = output.toNat + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := i) (by omega),
      Nat.mod_eq_of_lt (by omega)]
  refine ⟨ht, ?_⟩
  have := h.outStack (output.toNat + i) (by simp only [outputRegion, MemoryRegion.Contains]; omega)
  simp only [MemoryRegion.Contains] at this
  omega

theorem frame_transfer [Bindings] {s t u : RamState} {key : Vector UInt8 32} {counter : UInt32}
    {nonce : Vector UInt8 12} {input output : BitVec 64} {message : ByteArray}
    (h : CallPre s key counter nonce input output message) {F : Nat → Prop}
    {O : BitVec 64 → Prop} {L : List Component} (hf : Frame s t output message.size)
    (hL : StackLocal (sp s) F O L)
    (hO : ∀ x, O x → (∃ c ∈ callChanges s output message.size, c.Covers x) ∧
      (x.toNat < (sp s).toNat ∨ (sp s).toNat + frameBytes ≤ x.toNat))
    (hag : AgreesExcept L t u) (hr : ReadyToStep u) (hc : CodeIn Extracted.programImage u) :
    Frame s u output message.size := by
  have hlow := h.stackLow
  have hsl := h.stack.low
  simp only [stackRegion] at hsl
  have hspn : (sp s).toNat = (stackPtr s).toNat - frameBytes := by
    rw [sp_eq hlow, BitVec.toNat_ofNat]; simp only [stackRegion]; unfold frameBytes at *; omega
  refine ⟨hr, hc, (Cuts.Tail.stackPtr_agrees hag hL.1).trans hf.rsp, ?_, ?_⟩
  · refine ⟨fun c hc' hm => ?_, fun x hx => ?_, hag.rest.trans hf.agrees.rest,
      fun x hx => hag.grow x (hf.agrees.grow x hx)⟩
    · have hn : c ∉ L := fun hcL => hc' (by
        have := hL.2.1 c hcL hm
        simp only [Cuts.Rounds.regScratch, List.mem_cons, List.not_mem_nil, or_false] at this
        rcases this with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
          subst h <;> simp [callChanges, savedChanges])
      exact (hf.agrees.agree c hc' hm).trans (hag.agree c hn hm)
    · refine (hag.memory x fun c hcL hcv => ?_).trans (hf.agrees.memory x hx)
      rcases hL.2.2 c hcL _ hcv with ⟨i, -, hi, rfl⟩ | ho
      · apply hx (.mem (stackPtr s - BitVec.ofNat 64 frameBytes) frameBytes) (by simp [callChanges])
        exact ⟨i, by unfold frameBytes; omega, rfl⟩
      · obtain ⟨⟨c', hc', hcov'⟩, -⟩ := hO x ho
        exact hx c' (List.mem_append_left _ hc') hcov'
  · intro e he
    rw [← hf.saved e he]
    change memLoad u.external _ 64 = memLoad t.external _ 64
    have hoff : 8 ≤ e.2 ∧ e.2 ≤ 0x30 := by
      simp only [savedSlots, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with h | h | h | h | h | h <;> subst h <;> decide
    have ha : stackPtr s - BitVec.ofNat 64 e.2 = sp s + BitVec.ofNat 64 (frameBytes - e.2) := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, hspn, BitVec.toNat_sub_of_le (by
        rw [BitVec.le_def, BitVec.toNat_ofNat]; unfold frameBytes at hlow; omega)]
      simp only [BitVec.toNat_ofNat]; unfold frameBytes at *; omega
    rw [ha]
    refine Cuts.Tail.slot_keep 64 hag _ fun i hi => hL.nc_far (by unfold frameBytes at *; omega) ?_ ?_
    · rw [BitVec.toNat_add, hspn, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by unfold frameBytes at *; omega),
        Nat.mod_eq_of_lt (by unfold frameBytes at *; omega)]
      unfold frameBytes at *; omega
    · intro ho
      have := (hO _ ho).2
      rw [BitVec.toNat_add, hspn, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by unfold frameBytes at *; omega),
        Nat.mod_eq_of_lt (by unfold frameBytes at *; omega)] at this
      unfold frameBytes at *; omega

theorem allHold_iff {t : RamState} : ∀ {l : List Write},
    Write.AllHold t l ↔ ∀ w ∈ l, w.dst.read t = w.val
  | [] => by simp [Write.AllHold]
  | [w] => by simp [Write.AllHold]
  | w :: w' :: ws => by
    rw [show Write.AllHold t (w :: w' :: ws) ↔ w.dst.read t = w.val ∧ Write.AllHold t (w' :: ws)
      from Iff.rfl, allHold_iff]
    simp

theorem reg32_of_64 {t : RamState} {r : BitVec 5} {w : UInt32}
    (h : Cuts.Xor.reg64 t r = w.toBitVec.setWidth 64) :
    (Operand.reg r : Operand 32).read t = w.toBitVec := by
  have e : (Operand.reg r : Operand 32).read t =
      BitVec.setWidth 32 ((Operand.reg r : Operand 64).read t) := by simp [Operand.read]
  rw [e, show (Operand.reg r : Operand 64).read t = Cuts.Xor.reg64 t r from rfl, h]
  simp

theorem slot32_read {t : RamState} {b : BitVec 64} (hs : stackPtr t = b) (off : Nat) :
    Cuts.Xor.slot32 t off = (Operand.mem (b + BitVec.ofNat 64 off) : Operand 32).read t := by
  unfold Cuts.Xor.slot32 Cuts.Xor.slot; rw [hs]; rfl

theorem slot64_read {t : RamState} {b : BitVec 64} (hs : stackPtr t = b) (off : Nat) :
    Cuts.Xor.slot64 t off = (Operand.mem (b + BitVec.ofNat 64 off) : Operand 64).read t := by
  unfold Cuts.Xor.slot64 Cuts.Xor.slot; rw [hs]; rfl

theorem StackLocal.good {b : BitVec 64} {F : Nat → Prop} {L : List Component}
    (h : StackLocal b F (fun _ => False) L) (hF : ∀ i, F i → i < 0x80) :
    Cuts.Rounds.Good b L := by
  refine ⟨h.1, fun c hc x hx => ?_⟩
  rcases h.2.2 c hc x hx with ⟨i, hi, -, rfl⟩ | ho
  · exact ⟨i, hF i hi, rfl⟩
  · exact ho.elim

theorem sp_toNat [Bindings] {s : RamState} {key : Vector UInt8 32} {counter : UInt32}
    {nonce : Vector UInt8 12} {input output : BitVec 64} {message : ByteArray}
    (h : CallPre s key counter nonce input output message) :
    (sp s).toNat = (stackRegion s).start ∧ (sp s).toNat + 0x1a8 ≤ 2 ^ 32 := by
  have hl := h.stack.low
  have hlow := h.stackLow
  rw [sp_eq hlow, BitVec.toNat_ofNat]
  simp only [stackRegion] at hl ⊢
  unfold frameBytes at *
  omega

                                                                                                
theorem keep_far [Bindings] {s t u : RamState} {key : Vector UInt8 32} {counter : UInt32}
    {nonce : Vector UInt8 12} {input output : BitVec 64} {message : ByteArray}
    (h : CallPre s key counter nonce input output message) {F : Nat → Prop}
    {O : BitVec 64 → Prop} {L : List Component} (hL : StackLocal (sp s) F O L)
    (hag : AgreesExcept L t u) {r : MemoryRegion} (hd : r.Disjoint (stackRegion s))
    {x : BitVec 64} (hx : r.Contains x.toNat) (hO : ¬ O x) : u.external[x]? = t.external[x]? := by
  obtain ⟨h1, h2⟩ := sp_toNat h
  apply hag.byte
  refine hL.nc_far (by omega) ?_ hO
  have := hd _ hx
  simp only [MemoryRegion.Contains, stackRegion] at this
  simp only [stackRegion] at h1
  unfold frameBytes at *
  omega

theorem add_toNat_lt {a : BitVec 64} {i : Nat} (h : a.toNat + i < 2 ^ 64) :
    (a + BitVec.ofNat 64 i).toNat = a.toNat + i := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := i) (by omega),
    Nat.mod_eq_of_lt (by omega)]

end Helpers

section EnterBlock

open ChaCha20Poly1305.Proofs.MemoryRoutines.Machine

def enterBytes : List UInt8 :=
  [0x48, 0x89, 0x7c, 0x24, 0x70, 0xb8, 0x0a, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x78,
    0x8b, 0x5c, 0x24, 0x58, 0x44, 0x89, 0xd5, 0x44, 0x89, 0x64, 0x24, 0x3c, 0x45, 0x89, 0xe1,
    0x44, 0x89, 0x5c, 0x24, 0x04, 0x44, 0x8b, 0x6c, 0x24, 0x10, 0x8b, 0x4c, 0x24, 0x34, 0x44,
    0x89, 0xc7, 0x8b, 0x44, 0x24, 0x28, 0x44, 0x8b, 0x64, 0x24, 0x0c, 0x8b, 0x54, 0x24, 0x30,
    0x44, 0x8b, 0x74, 0x24, 0x1c, 0x8b, 0x74, 0x24, 0x24, 0x44, 0x8b, 0x54, 0x24, 0x40, 0x44,
    0x8b, 0x5c, 0x24, 0x2c, 0x44, 0x8b, 0x7c, 0x24, 0x18, 0x44, 0x8b, 0x44, 0x24, 0x20, 0x0f,
    0x1f, 0x80, 0x00, 0x00, 0x00, 0x00]

def enterEffect : RamState → Effect :=
  (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (movM64R64Effect 0x100c70 7 (.sib 4 none 0 (.d8 0x70))) (movR32Imm32Effect 0x100c75 5 0 0xa)) (movM64R64Effect 0x100c7a 0 (.sib 4 none 0 (.d8 0x78)))) (movR32M32LowEffect 0x100c7f 3 (.sib 4 none 0 (.d8 0x58)))) (movR32R32Effect 0x100c83 3 5 10)) (movM32R32Effect 0x100c86 12 (.sib 4 none 0 (.d8 0x3c)))) (movR32R32Effect 0x100c8b 3 9 12)) (movM32R32Effect 0x100c8e 11 (.sib 4 none 0 (.d8 0x4)))) (movR32M32Effect 0x100c93 13 (.sib 4 none 0 (.d8 0x10)))) (movR32M32LowEffect 0x100c98 1 (.sib 4 none 0 (.d8 0x34)))) (movR32R32Effect 0x100c9c 3 7 8)) (movR32M32LowEffect 0x100c9f 0 (.sib 4 none 0 (.d8 0x28)))) (movR32M32Effect 0x100ca3 12 (.sib 4 none 0 (.d8 0xc)))) (movR32M32LowEffect 0x100ca8 2 (.sib 4 none 0 (.d8 0x30)))) (movR32M32Effect 0x100cac 14 (.sib 4 none 0 (.d8 0x1c)))) (movR32M32LowEffect 0x100cb1 6 (.sib 4 none 0 (.d8 0x24)))) (movR32M32Effect 0x100cb5 10 (.sib 4 none 0 (.d8 0x40)))) (movR32M32Effect 0x100cba 11 (.sib 4 none 0 (.d8 0x2c)))) (movR32M32Effect 0x100cbf 15 (.sib 4 none 0 (.d8 0x18)))) (movR32M32Effect 0x100cc4 8 (.sib 4 none 0 (.d8 0x20)))) (fun _ => nopEffect 0x100cc9 7))

set_option maxHeartbeats 4000000 in
theorem enterBlock [Bindings] (boundary : ReturnBoundary)
    (hb : boundary.rip.toNat < 0x100a80 ∨ 0x1014bc ≤ boundary.rip.toNat) (stack : BitVec 64) :
    AdvancesBlock boundary (fun s => s.RIP = 0x100c70 ∧ Cuts.Rounds.RFrame stack s)
      (codeRange 0x100c70 enterBytes) enterEffect := by
  unfold enterBytes
  rr_begin (mov_m64_r64_effect_step 0x100c70 0x48 (by unfold RexWPrefix; decide) 7 (.sib 4 none 0 (.d8 0x70)) (by decide) (by decide) (by decide))
  rr_then (mov_r32_imm32_effect_step 0x100c75 0xb8 (by decide) 0xa)
  rr_then (mov_m64_r64_effect_step 0x100c7a 0x48 (by unfold RexWPrefix; decide) 0 (.sib 4 none 0 (.d8 0x78)) (by decide) (by decide) (by decide))
  rr_then (mov_r32_m32_low_effect_step 0x100c7f 3 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide))
  rr_then (mov_r32_r32_rex_effect_step 0x100c83 0x44 0xd5 (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (mov_m32_r32_effect_step 0x100c86 0x44 (by unfold RexNoWPrefix; decide) 4 (.sib 4 none 0 (.d8 0x3c)) (by decide) (by decide) (by decide))
  rr_then (mov_r32_r32_rex_effect_step 0x100c8b 0x45 0xe1 (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (mov_m32_r32_effect_step 0x100c8e 0x44 (by unfold RexNoWPrefix; decide) 3 (.sib 4 none 0 (.d8 0x4)) (by decide) (by decide) (by decide))
  rr_then (mov_r32_m32_effect_step 0x100c93 0x44 (by unfold RexNoWPrefix; decide) 5 (.sib 4 none 0 (.d8 0x10)) (by decide) (by decide) (by decide))
  rr_then (mov_r32_m32_low_effect_step 0x100c98 1 (.sib 4 none 0 (.d8 0x34)) (by decide) (by decide) (by decide))
  rr_then (mov_r32_r32_rex_effect_step 0x100c9c 0x44 0xc7 (by unfold RexNoWPrefix; decide) (by decide))
  rr_then (mov_r32_m32_low_effect_step 0x100c9f 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide))
  rr_then (mov_r32_m32_effect_step 0x100ca3 0x44 (by unfold RexNoWPrefix; decide) 4 (.sib 4 none 0 (.d8 0xc)) (by decide) (by decide) (by decide))
  rr_then (mov_r32_m32_low_effect_step 0x100ca8 2 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide))
  rr_then (mov_r32_m32_effect_step 0x100cac 0x44 (by unfold RexNoWPrefix; decide) 6 (.sib 4 none 0 (.d8 0x1c)) (by decide) (by decide) (by decide))
  rr_then (mov_r32_m32_low_effect_step 0x100cb1 6 (.sib 4 none 0 (.d8 0x24)) (by decide) (by decide) (by decide))
  rr_then (mov_r32_m32_effect_step 0x100cb5 0x44 (by unfold RexNoWPrefix; decide) 2 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide))
  rr_then (mov_r32_m32_effect_step 0x100cba 0x44 (by unfold RexNoWPrefix; decide) 3 (.sib 4 none 0 (.d8 0x2c)) (by decide) (by decide) (by decide))
  rr_then (mov_r32_m32_effect_step 0x100cbf 0x44 (by unfold RexNoWPrefix; decide) 7 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide))
  rr_then (mov_r32_m32_effect_step 0x100cc4 0x44 (by unfold RexNoWPrefix; decide) 0 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide))
  refine AdvancesBlock.block_then ?k (nop_m_effect_step 0x100cc9 [] (by decide) (by decide)
    (.base 0 (.d32 0)) (by decide) (by decide) (by decide)) ?loc ?sub ?full ?mid ?boundary
  case loc => x86_local
  case sub => first | x86_sub | rr_sub
  case full =>
    first
    | (intro s _
       apply Effect.Local.full
       repeat' first
         | (solve | x86_local)
         | apply Effect.Local.seq
       done)
    | x86_full
  case mid =>
    intro s s' hP hH hO
    refine ⟨hH.rip_of (by first | rfl | x86_norm), ?_⟩
    exact Effect.Avoids.of_noMem
      (fun c hc x => by simp_all [nopEffect, Effect.components, Component.Covers]) _
  case boundary => rr_bd
  case' k => skip
  rr_finish

def enterPre : List (Fin 16 × Cuts.Rounds.Loc) :=
  [(4, .reg 10), (8, .reg 11), (12, .reg 12), (13, .reg 8), (0, .slot 0x58), (1, .slot 0x10),
    (2, .slot 0xc), (3, .slot 0x40), (5, .slot 0x34), (6, .slot 0x30), (7, .slot 0x2c),
    (9, .slot 0x28), (10, .slot 0x24), (11, .slot 0x20), (14, .slot 0x1c), (15, .slot 0x18)]

set_option maxHeartbeats 2000000 in
set_option linter.unusedVariables false in
set_option linter.unusedSimpArgs false in
theorem enterWords {stack J : BitVec 64} {x : Vector UInt32 16} {s t : RamState}
    (hs : rspOf s = stack)
    (hw : Write.AllHold s (Cuts.Rounds.cut stack enterPre x ++ [⟨(Operand.reg 7 : Operand 64), J⟩]))
    (he : (enterEffect s).Holds s t) :
    Write.AllHold t (Cuts.Rounds.cut stack Cuts.Rounds.mainBase x ++
      [⟨(Operand.mem (stack + 0x70) : Operand 64), J⟩,
        ⟨(Operand.mem (stack + 0x78) : Operand 64), 0xa⟩,
        ⟨(Operand.mem (stack + 0x3c) : Operand 32), x[12].toBitVec⟩]) := by
  have hfull : ∀ w ∈ (enterEffect s).writes, w.Full := by x86_norm [enterEffect]
  have ho := he.obsAfter hfull true
  x86_norm at hs
  simp only [Cuts.Rounds.cut, enterPre, Cuts.Rounds.mainBase, List.map, Cuts.Rounds.Loc.op,
    List.cons_append, List.nil_append, List.append_nil, Write.AllHold, List.append_assoc] at hw ⊢
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16⟩ := hw
  simp only [← ho.read_reg, ← ho.read_mem]
  x86_norm [enterEffect, hs]
  x86_norm at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16
  simp (config := {decide := true}) only [BitVec.setWidth_setWidth_of_le, BitVec.setWidth_eq,
    h0, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15, h16, and_true]
  all_goals first | rfl | (simp; done) | (simp; rfl)

def enterChanges (b : BitVec 64) : List Component :=
  Cuts.Rounds.regScratch ++ [.mem (b + 0x70) 8, .mem (b + 0x78) 8, .mem (b + 0x3c) 4, .mem (b + 4) 4]

def EnterFree (i : Nat) : Prop := (4 ≤ i ∧ i < 8) ∨ (0x3c ≤ i ∧ i < 0x40) ∨ (0x70 ≤ i ∧ i < 0x80)

theorem enterChanges_local (b : BitVec 64) :
    StackLocal b EnterFree (fun _ => False) (enterChanges b) := by
  refine ⟨by simp [enterChanges, Cuts.Rounds.regScratch], fun c hc hm => ?_, fun c hc x hx => ?_⟩
  · simp only [enterChanges, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with hc | hc | hc | hc | hc
    · exact hc
    all_goals (subst hc; simp [Component.isMem] at hm)
  · simp only [enterChanges, Cuts.Rounds.regScratch, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with (h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h) |
      h | h | h | h <;> subst h <;> simp only [Component.Covers] at hx
    all_goals obtain ⟨k, hk, rfl⟩ := hx
    all_goals exact .inl ⟨_, by unfold EnterFree; simp; omega, by simp; omega,
      Cuts.Tail.add_toNat _ _ _⟩

end EnterBlock


section Words

theorem words_12 (key : Vector UInt8 32) (counter : UInt32) (nonce : Vector UInt8 12) (j : Nat) :
    (words key counter nonce j)[12] = counter + j.toUInt32 := by
  simp [words, initialState, chachaState, counterNonceWords]
  apply UInt32.toNat_inj.mp
  simp [UInt32.toNat_add]

theorem words_12_succ (key : Vector UInt8 32) (counter : UInt32) (nonce : Vector UInt8 12)
    (j : Nat) :
    (words key counter nonce j)[12] + (1 : UInt32) = (words key counter nonce (j + 1))[12] := by
  rw [words_12, words_12]
  simp [Nat.toUInt32, UInt32.add_assoc]

theorem words_other (key : Vector UInt8 32) (counter : UInt32) (nonce : Vector UInt8 12)
    (j j' : Nat) (k : Fin 16) (hk : k ≠ 12) :
    (words key counter nonce j)[k] = (words key counter nonce j')[k] := by
  obtain ⟨k, hk16⟩ := k
  simp only [Fin.getElem_fin]
  have hk' : k ≠ 12 := fun h => hk (Fin.ext h)
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k
  all_goals first
    | (exfalso; omega)
    | simp [words, initialState, chachaState, counterNonceWords]

theorem words_other' (key : Vector UInt8 32) (counter : UInt32) (nonce : Vector UInt8 12)
    (j j' k : Nat) (hk : k < 16) (h12 : k ≠ 12) :
    (words key counter nonce j)[k] = (words key counter nonce j')[k] := by
  have := words_other key counter nonce j j' ⟨k, hk⟩ (fun h => h12 (congrArg Fin.val h))
  simpa only [Fin.getElem_fin] using this

theorem words_zero (key : Vector UInt8 32) (counter : UInt32) (nonce : Vector UInt8 12) :
    words key counter nonce 0 = initialState key counter nonce := by
  simp [words]

theorem keystream_words (key : Vector UInt8 32) (counter : UInt32) (nonce : Vector UInt8 12)
    (j : Nat) :
    Cuts.Xor.keystream (mixed (words key counter nonce j)) (words key counter nonce j) =
      keystreamBlock key (counter + j.toUInt32) nonce := rfl

theorem cipher_byte (key : Vector UInt8 32) (counter : UInt32) (nonce : Vector UInt8 12)
    (message : ByteArray) (j i : Nat) (hi : i < 64) (hj : 64 * j + i < message.size) :
    (chacha20Encrypt key counter nonce message)[64 * j + i]! =
      message[64 * j + i]! ^^^ (keystreamBlock key (counter + j.toUInt32) nonce)[i] := by
  rw [chacha20Encrypt_eq_xorKeystream]
  have hs := Common.xorKeystream_size
    (fun j => keystreamBlock key (counter + j.toUInt32) nonce) message
  rw [getElem!_pos _ _ (by omega), getElem!_pos message (64 * j + i) hj,
    Common.xorKeystream_getElem _ _ _ hj]
  have h1 : (64 * j + i) / 64 = j := by omega
  have h2 : (64 * j + i) % 64 = i := by omega
  simp only [h1, h2]

                                                                                        
                           
theorem cipher_block (key : Vector UInt8 32) (counter : UInt32) (nonce : Vector UInt8 12)
    (message : ByteArray) (j : Nat) (i : Fin 64) (hj : 64 * j + 64 ≤ message.size) :
    (block message j)[i] ^^^
        (Cuts.Xor.keystream (mixed (words key counter nonce j)) (words key counter nonce j))[i] =
      (chacha20Encrypt key counter nonce message)[64 * j + i.val]! := by
  rw [cipher_byte key counter nonce message j i.val i.isLt (by omega), keystream_words]
  simp [block]

theorem state_bytes {u : RamState} {st : BitVec 64} {y : Vector UInt32 16}
    (hs : ∀ i < 64, (u.external[st + BitVec.ofNat 64 i]?).isSome)
    (h : ∀ i < 16, memLoad u.external (st + BitVec.ofNat 64 (4 * i)) 32 = y[i]!.toBitVec) :
    Cuts.Tail.BytesAt st (serialize y) u := by
  intro j
  have hj := j.isLt
  have hm := storedByte_memLoad u.external (st + BitVec.ofNat 64 (4 * (j.val / 4)))
    (n := 32) (j.val % 4) (by omega)
  rw [h _ (by omega), Cuts.Tail.tail_add] at hm
  have ha : st + BitVec.ofNat 64 j.val = st + BitVec.ofNat 64 (4 * (j.val / 4) + j.val % 4) := by
    rw [show 4 * (j.val / 4) + j.val % 4 = j.val by omega]
  rw [ha]
  obtain ⟨b, hb⟩ := Option.isSome_iff_exists.mp (hs (4 * (j.val / 4) + j.val % 4) (by omega))
  rw [hb]
  simp only [memByte, PhysicalMemory.read, hb, Option.getD_some] at hm
  rw [← hm, getElem!_pos y (j.val / 4) (by omega)]
  have := Cuts.Tail.serialize_word y (j.val / 4) (by omega) (j.val % 4) (by omega)
  simp only [show 4 * (j.val / 4) + j.val % 4 = j.val by omega] at this
  rw [← this]
  rfl

theorem hasBytes_keep [Bindings] {s t w : RamState} {bs : ByteArray}
    (h : (wordsRegion s).HasBytes t.external bs)
    (hk : ∀ i < 0x40, w.external[st s + BitVec.ofNat 64 i]? = t.external[st s + BitVec.ofNat 64 i]?) :
    (wordsRegion s).HasBytes w.external bs := by
  refine ⟨h.1, fun i => ?_⟩
  have hi : i.val < 0x40 := by
    have := h.1; have := i.isLt; simp only [MemoryRegion.HasLength, wordsRegion] at *; omega
  have ha : BitVec.ofNat 64 ((wordsRegion s).start + i.val) = st s + BitVec.ofNat 64 i.val := by
    simp only [wordsRegion, st]
    rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [ha, hk _ hi, ← ha]
  exact h.2 i

theorem stateBytes_size (key : Vector UInt8 32) (counter : UInt32) (nonce : Vector UInt8 12) :
    (stateBytes key counter nonce).size = 64 := by
  unfold stateBytes
  simp only [ByteArray.size, Vector.size_toArray]

theorem stateBytes_getElem (key : Vector UInt8 32) (counter : UInt32) (nonce : Vector UInt8 12)
    (i : Nat) (h' : i < (stateBytes key counter nonce).size) :
    (stateBytes key counter nonce)[i] =
      (serialize (initialState key counter nonce))[i]'(by
        rw [stateBytes_size] at h'; exact h') := by
  have hd : (stateBytes key counter nonce).data =
      (serialize (initialState key counter nonce)).toArray := rfl
  rw [ByteArray.getElem_eq_getElem_data]
  simp only [hd, Vector.getElem_toArray]

theorem state_bytesAt [Bindings] {s : RamState} {m : Ram} {key : Vector UInt8 32}
    {counter : UInt32} {nonce : Vector UInt8 12}
    (h : (wordsRegion s).HasBytes m (stateBytes key counter nonce)) :
    ∀ i : Fin 64, m[st s + BitVec.ofNat 64 i.val]? =
      some (serialize (initialState key counter nonce))[i] := by
  intro i
  have hi : i.val < (stateBytes key counter nonce).size := by
    rw [stateBytes_size]; exact i.isLt
  have := h.2 ⟨i.val, hi⟩
  simp only [wordsRegion] at this
  rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at this
  rw [show st s = rdi.read s from rfl, this, stateBytes_getElem]
  rfl

end Words

section Exit

def FeedFree (i : Nat) : Prop := 0xb0 ≤ i ∧ i < 0x170

                                                       
def OutBlk (output : BitVec 64) (j : Nat) (x : BitVec 64) : Prop :=
  ∃ k < 64, x = output + BitVec.ofNat 64 (64 * j + k)

                                                                         
def CtrWord (st : BitVec 64) (x : BitVec 64) : Prop :=
  ∃ k < 4, x = st + 0x30 + BitVec.ofNat 64 k

                                                                                            
                                  
def ExitOut (output st : BitVec 64) (j : Nat) (x : BitVec 64) : Prop :=
  OutBlk output j x ∨ CtrWord st x

def exitExtra (st : BitVec 64) : List Component :=
  Cuts.Rounds.regScratch ++ [.mem (st + 0x30) 4]

theorem StackLocal.append {b : BitVec 64} {F : Nat → Prop} {O₁ O₂ : BitVec 64 → Prop}
    {L₁ L₂ : List Component} (h₁ : StackLocal b F O₁ L₁) (h₂ : StackLocal b F O₂ L₂) :
    StackLocal b F (fun x => O₁ x ∨ O₂ x) (L₁ ++ L₂) := by
  refine ⟨by simp only [List.mem_append, not_or]; exact ⟨h₁.1, h₂.1⟩, fun c hc hm => ?_,
    fun c hc x hx => ?_⟩
  · rcases List.mem_append.mp hc with hc | hc
    · exact h₁.2.1 c hc hm
    · exact h₂.2.1 c hc hm
  · rcases List.mem_append.mp hc with hc | hc
    · rcases h₁.2.2 c hc x hx with h | h
      · exact .inl h
      · exact .inr (.inl h)
    · rcases h₂.2.2 c hc x hx with h | h
      · exact .inl h
      · exact .inr (.inr h)

theorem StackLocal.mono {b : BitVec 64} {F : Nat → Prop} {O O' : BitVec 64 → Prop}
    {L L' : List Component} (h : StackLocal b F O L) (hL : ∀ c ∈ L', c ∈ L)
    (hO : ∀ x, O x → O' x) : StackLocal b F O' L' :=
  ⟨fun h4 => h.1 (hL _ h4), fun c hc hm => h.2.1 c (hL c hc) hm, fun c hc x hx =>
    (h.2.2 c (hL c hc) x hx).imp id (hO x)⟩

theorem feed_local {b output : BitVec 64} {t : RamState} {j : Nat} (hb : stackPtr t = b) :
    StackLocal b FeedFree (OutBlk output j) (Cuts.Xor.changes t output j) := by
  refine ⟨by simp [Cuts.Xor.changes], fun c hc hm => ?_, fun c hc x hx => ?_⟩
  · simp only [Cuts.Xor.changes, Cuts.Rounds.regScratch, List.mem_cons, List.not_mem_nil,
      or_false] at hc ⊢
    rcases hc with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
      subst h <;> simp_all [Component.isMem]
  · simp only [Cuts.Xor.changes, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;>
      subst h <;> simp only [Component.Covers] at hx
    all_goals obtain ⟨k, hk, rfl⟩ := hx
    · refine .inl ⟨0xb0 + k, by unfold FeedFree Cuts.Xor.scratchBytes at *; omega,
        by unfold Cuts.Xor.scratchBytes at *; omega, ?_⟩
      unfold Cuts.Xor.slot Cuts.Xor.scratchOff
      rw [hb, Cuts.Tail.tail_add]
    · exact .inr ⟨k, hk, by unfold Cuts.Xor.outBlock; rw [Cuts.Tail.tail_add]⟩

theorem extra_local (b st : BitVec 64) (F : Nat → Prop) :
    StackLocal b F (CtrWord st) (exitExtra st) := by
  refine ⟨by simp [exitExtra, Cuts.Rounds.regScratch], fun c hc hm => ?_, fun c hc x hx => ?_⟩
  · simp only [exitExtra, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with hc | hc
    · exact hc
    · subst hc; simp [Component.isMem] at hm
  · simp only [exitExtra, Cuts.Rounds.regScratch, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with (h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h) | h <;>
      subst h <;> simp only [Component.Covers] at hx
    obtain ⟨k, hk, rfl⟩ := hx
    exact .inr ⟨k, hk, rfl⟩

theorem exit_local {b output st : BitVec 64} {t : RamState} {j : Nat} (hb : stackPtr t = b) :
    StackLocal b FeedFree (ExitOut output st j) (Cuts.Xor.changes t output j ++ exitExtra st) :=
  (feed_local hb).append (extra_local b st FeedFree)

theorem exitOut_far [Bindings] {s : RamState} {key : Vector UInt8 32} {counter : UInt32}
    {nonce : Vector UInt8 12} {input output : BitVec 64} {message : ByteArray}
    (h : CallPre s key counter nonce input output message) {j : Nat}
    (hj : 64 * j + 64 ≤ message.size) {x : BitVec 64} (hx : ExitOut output (st s) j x) :
    (∃ c ∈ callChanges s output message.size, c.Covers x) ∧
      (x.toNat < (sp s).toNat ∨ (sp s).toNat + frameBytes ≤ x.toNat) := by
  obtain ⟨h1, -⟩ := sp_toNat h
  rcases hx with ⟨k, hk, rfl⟩ | ⟨k, hk, rfl⟩
  · refine ⟨⟨.mem output message.size, by simp [callChanges], 64 * j + k, by omega, rfl⟩, ?_⟩
    obtain ⟨ht, hfar⟩ := out_far h (i := 64 * j + k) (by omega)
    rw [ht, h1]
    simp only [stackRegion] at hfar ⊢
    omega
  · refine ⟨⟨.mem (rdi.read s + 0x30) 4, by simp [callChanges], k, hk, rfl⟩, ?_⟩
    have hl := h.cipher.low
    simp only [cipherRegion, cipherBytes] at hl
    have ht : (st s + 0x30 + BitVec.ofNat 64 k).toNat = (st s).toNat + 0x30 + k := by
      unfold st at *; bv_omega
    have := h.cipherStack ((st s).toNat + 0x30 + k) (by
      simp only [cipherRegion, cipherBytes, MemoryRegion.Contains, st]; omega)
    rw [ht, h1]
    simp only [stackRegion, MemoryRegion.Contains] at this ⊢
    unfold frameBytes at *
    omega

theorem far_not_stack {s : RamState} {O : BitVec 64 → Prop}
    (hO : ∀ x, O x → x.toNat < (sp s).toNat ∨ (sp s).toNat + frameBytes ≤ x.toNat)
    (hb : (sp s).toNat + 0x1a0 ≤ 2 ^ 32) {m : Nat} (hm : m < 0x1a0) :
    ¬ O (sp s + BitVec.ofNat 64 m) := by
  intro ho
  have := hO _ ho
  rw [add_toNat_lt (by omega)] at this
  unfold frameBytes at this
  omega

theorem in_not_exit [Bindings] {s : RamState} {key : Vector UInt8 32} {counter : UInt32}
    {nonce : Vector UInt8 12} {input output : BitVec 64} {message : ByteArray}
    (h : CallPre s key counter nonce input output message) {j i : Nat}
    (hj : 64 * j + 64 ≤ message.size) (h1 : 64 * (j + 1) ≤ i) (h2 : i < message.size) :
    ¬ ExitOut output (st s) j (input + BitVec.ofNat 64 i) := by
  have hil := h.messageLow
  have hol := h.out.low
  have hcl := h.cipher.low
  simp only [outputRegion, cipherRegion, cipherBytes] at hol hcl
  rintro (⟨k, hk, he⟩ | ⟨k, hk, he⟩)
  · have := congrArg BitVec.toNat he
    rw [add_toNat_lt (by omega), add_toNat_lt (by omega)] at this
    rcases h.alias with rfl | hd
    · omega
    · exact hd (input.toNat + i) (by simp only [inputRegion, MemoryRegion.Contains]; omega)
        (by simp only [outputRegion, MemoryRegion.Contains]; omega)
  · have := congrArg BitVec.toNat he
    have ht : (st s + 0x30 + BitVec.ofNat 64 k).toNat = (st s).toNat + 0x30 + k := by
      unfold st at *; bv_omega
    rw [add_toNat_lt (by omega), ht] at this
    exact h.inputCipher (input.toNat + i)
      (by simp only [inputRegion, MemoryRegion.Contains]; omega)
      (by simp only [cipherRegion, cipherBytes, MemoryRegion.Contains, st] at this ⊢; omega)

theorem out_not_ctr [Bindings] {s : RamState} {key : Vector UInt8 32} {counter : UInt32}
    {nonce : Vector UInt8 12} {input output : BitVec 64} {message : ByteArray}
    (h : CallPre s key counter nonce input output message) {i : Nat} (hi : i < message.size) :
    ¬ CtrWord (st s) (output + BitVec.ofNat 64 i) := by
  have hol := h.out.low
  have hcl := h.cipher.low
  simp only [outputRegion, cipherRegion, cipherBytes] at hol hcl
  rintro ⟨k, hk, he⟩
  have := congrArg BitVec.toNat he
  have ht : (st s + 0x30 + BitVec.ofNat 64 k).toNat = (st s).toNat + 0x30 + k := by
    unfold st at *; bv_omega
  rw [add_toNat_lt (by omega), ht] at this
  exact h.outCipher (output.toNat + i)
    (by simp only [outputRegion, MemoryRegion.Contains]; omega)
    (by simp only [cipherRegion, cipherBytes, MemoryRegion.Contains, st] at this ⊢; omega)

theorem out_not_exit [Bindings] {s : RamState} {key : Vector UInt8 32} {counter : UInt32}
    {nonce : Vector UInt8 12} {input output : BitVec 64} {message : ByteArray}
    (h : CallPre s key counter nonce input output message) {j i : Nat}
    (hj : 64 * j + 64 ≤ message.size) (hi : i < 64 * j) :
    ¬ ExitOut output (st s) j (output + BitVec.ofNat 64 i) := by
  have hol := h.out.low
  simp only [outputRegion] at hol
  rintro (⟨k, hk, he⟩ | hc)
  · have := congrArg BitVec.toNat he
    rw [add_toNat_lt (by omega), add_toNat_lt (by omega)] at this
    omega
  · exact out_not_ctr h (i := i) (by omega) hc

theorem cipher_not_out [Bindings] {s : RamState} {key : Vector UInt8 32} {counter : UInt32}
    {nonce : Vector UInt8 12} {input output : BitVec 64} {message : ByteArray}
    (h : CallPre s key counter nonce input output message) {j i : Nat}
    (hj : 64 * j + 64 ≤ message.size) (hi : i < 0x80) :
    ¬ OutBlk output j (st s + BitVec.ofNat 64 i) := by
  have hol := h.out.low
  have hcl := h.cipher.low
  simp only [outputRegion, cipherRegion, cipherBytes] at hol hcl
  rintro ⟨k, hk, he⟩
  have := congrArg BitVec.toNat he
  rw [add_toNat_lt (by unfold st; omega), add_toNat_lt (by omega)] at this
  exact h.outCipher (output.toNat + (64 * j + k))
    (by simp only [outputRegion, MemoryRegion.Contains]; omega)
    (by simp only [cipherRegion, cipherBytes, MemoryRegion.Contains, st] at this ⊢; omega)

                                                             
structure ExitFacts [Bindings] (s : RamState) (key : Vector UInt8 32) (counter : UInt32)
    (nonce : Vector UInt8 12) (input output : BitVec 64) (message : ByteArray) (j : Nat)
    (w : RamState) : Prop where
  frame : Frame s w output message.size
  inSlot : Cuts.Xor.slot64 w 0x68 = input
  outSlot : Cuts.Xor.slot64 w 0x60 = output
  count : Cuts.Xor.slot64 w 0x50 = BitVec.ofNat 64 (nblocks message.size)
  inits : ∀ e ∈ Cuts.Xor.initSlot, e.1 ≠ 12 →
    Cuts.Xor.slot32 w e.2 = (words key counter nonce (j + 1))[e.1].toBitVec
  slots : Cuts.Tail.Slots (sp s) (st s) input output message.size w
  rest : Cuts.Tail.Rest input message.size (msg message) (64 * (j + 1)) w
  wrote : Prefix output (chacha20Encrypt key counter nonce message) (64 * (j + 1)) w

set_option maxHeartbeats 4000000 in
theorem exit_facts [Bindings] {s t u w : RamState} {key : Vector UInt8 32} {counter : UInt32}
    {nonce : Vector UInt8 12} {input output : BitVec 64} {message : ByteArray} {j : Nat}
    (h : CallPre s key counter nonce input output message)
    (hk : Kept s key counter nonce input output message j t)
    (hp : Cuts.Xor.FeedPost t u (mixed (words key counter nonce j)) (words key counter nonce j)
      j output (block message j))
    (G : AgreesExcept (Cuts.Xor.changes t output j ++ exitExtra (st s)) t w)
    (G2 : AgreesExcept (exitExtra (st s)) u w) (hrw : ReadyToStep w)
    (hcw : CodeIn Extracted.programImage w) :
    ExitFacts s key counter nonce input output message j w := by
  have hf := hk.frame
  have hsp : stackPtr t = sp s := hf.rsp
  have hjl := hk.lt
  have hnb : 64 * nblocks message.size ≤ message.size := by unfold nblocks; omega
  have hj64 : 64 * j + 64 ≤ message.size := by omega
  have hsize := h.messageLow
  obtain ⟨hsp1, hsp2⟩ := sp_toNat h
  have hL := exit_local (output := output) (st := st s) (j := j) hsp
  have hOfar : ∀ x, ExitOut output (st s) j x →
      x.toNat < (sp s).toNat ∨ (sp s).toNat + frameBytes ≤ x.toNat :=
    fun x hx => (exitOut_far h hj64 hx).2
  have hfw := frame_transfer h hf hL (fun x hx => exitOut_far h hj64 hx) G hrw hcw
  have hspw : stackPtr w = sp s := hfw.rsp
  have kN (n o : Nat) (ho : o + n / 8 ≤ 0xb0) :
      memLoad w.external (sp s + BitVec.ofNat 64 o) n =
        memLoad t.external (sp s + BitVec.ofNat 64 o) n :=
    hL.load G n o (by omega) (fun i hi => by unfold FeedFree; omega)
      (fun i hi => far_not_stack hOfar (by omega) (by omega))
  have k64 (o : Nat) (ho : o + 8 ≤ 0xb0) : Cuts.Xor.slot64 w o = Cuts.Xor.slot64 t o := by
    unfold Cuts.Xor.slot64 Cuts.Xor.slot; rw [hspw, hsp]; exact kN 64 o (by omega)
  have k32 (o : Nat) (ho : o + 4 ≤ 0xb0) : Cuts.Xor.slot32 w o = Cuts.Xor.slot32 t o := by
    unfold Cuts.Xor.slot32 Cuts.Xor.slot; rw [hspw, hsp]; exact kN 32 o (by omega)
  have t64 (o : Nat) (ho : o + 8 ≤ 0xb0) :
      Cuts.Tail.slot64 w (sp s) o = Cuts.Tail.slot64 t (sp s) o := kN 64 o (by omega)
  refine ⟨hfw, (k64 0x68 (by decide)).trans hk.inSlot, (k64 0x60 (by decide)).trans hk.outSlot,
    (k64 0x50 (by decide)).trans hk.count, ?_, ?_, ?_, ?_⟩
  · intro e he h12
    have hle : e.2 + 4 ≤ 0xb0 := by
      simp only [Cuts.Xor.initSlot, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl <;> decide
    rw [k32 _ hle, hk.inits e he, words_other key counter nonce j (j + 1) e.1 h12]
  · have hs0 := hk.slots
    exact ⟨(t64 0x48 (by decide)).trans hs0.state, (t64 0x88 (by decide)).trans hs0.output,
      (t64 0x90 (by decide)).trans hs0.input, (t64 0x98 (by decide)).trans hs0.head,
      (t64 0xa0 (by decide)).trans hs0.tail, (t64 0xa8 (by decide)).trans hs0.length⟩
  · intro i h1 h2
    refine (keep_far h hL G (r := inputRegion input message.size) h.inputStack ?_
      (in_not_exit h hj64 h1 h2)).trans (hk.rest i (by omega) h2)
    simp only [inputRegion, MemoryRegion.Contains]
    rw [add_toNat_lt (by omega)]; omega
  · intro i hi
    have hol := h.out.low
    simp only [outputRegion] at hol
    by_cases hlo : i < 64 * j
    · refine (keep_far h hL G (r := outputRegion output message.size) h.outStack ?_
        (out_not_exit h hj64 hlo)).trans (hk.wrote i hlo)
      simp only [outputRegion, MemoryRegion.Contains]
      rw [add_toNat_lt (by omega)]; omega
    · have hk' : i - 64 * j < 64 := by omega
      have ha : Cuts.Xor.outBlock output j + BitVec.ofNat 64 (i - 64 * j) =
          output + BitVec.ofNat 64 i := by
        unfold Cuts.Xor.outBlock; rw [Cuts.Tail.tail_add]; congr 2; omega
      have hu := hp.output ⟨i - 64 * j, hk'⟩
      rw [ha] at hu
      have hsame : w.external[output + BitVec.ofNat 64 i]? =
          u.external[output + BitVec.ofNat 64 i]? := by
        apply G2.byte
        apply (extra_local (sp s) (st s) (fun _ => False)).nc_far (by omega)
        · obtain ⟨ht, hfar⟩ := out_far h (i := i) (by omega)
          rw [ht, hsp1]; simp only [stackRegion] at hfar ⊢; unfold frameBytes at *; omega
        · exact out_not_ctr h (i := i) (by omega)
      rw [hsame, hu, cipher_block key counter nonce message j ⟨i - 64 * j, hk'⟩ hj64]
      congr 3
      simp only
      omega

theorem rangeApart_of {a b : BitVec 64} {n m : Nat} (ha : a.toNat + n ≤ 2 ^ 32)
    (hb : b.toNat + m ≤ 2 ^ 32) (h : ∀ i < n, ∀ j < m, a.toNat + i ≠ b.toNat + j) :
    RangeApart a n b m := by
  intro i hi j hj he
  have := congrArg BitVec.toNat he
  rw [add_toNat_lt (by omega), add_toNat_lt (by omega)] at this
  exact h i hi j hj this

theorem st_eq (s : RamState) : st s = BitVec.ofNat 64 ((cipherRegion s).start + 0) := by
  simp [st, cipherRegion]

                                                                                             
                                                     
theorem space_of [Bindings] {s w : RamState} {key : Vector UInt8 32} {counter : UInt32}
    {nonce : Vector UInt8 12} {input output : BitVec 64} {message : ByteArray}
    (h : CallPre s key counter nonce input output message)
    (hg : ∀ x : BitVec 64, (s.external[x]?).isSome → (w.external[x]?).isSome)
    (hrsp : stackPtr w = sp s) :
    Cuts.Tail.Space (sp s) (st s) input output message.size w := by
  obtain ⟨hsp1, hsp2⟩ := sp_toNat h
  have hst := frame_stack_writable h hg 0 0x170 (by decide) (by decide)
  simp only [BitVec.add_zero] at hst
  have hcw := region_writable h.cipher hg 0 0x80 (by decide) (by simp [cipherRegion, cipherBytes])
  rw [← st_eq] at hcw
  have hil := h.messageLow
  have hol := h.out.low
  have hcl := h.cipher.low
  simp only [outputRegion, cipherRegion, cipherBytes] at hol hcl
  have hstn : (st s).toNat = (rdi.read s).toNat := rfl
  have hTs : Cuts.Tail.stateBytes = 0x80 := rfl
  have hTf : Cuts.Tail.frameBytes = 0x170 := rfl
  have hF : frameBytes = 0x1a0 := rfl
  have hbase := Cuts.Tail.base_le message.size
  have hot : (Cuts.Tail.outTail output message.size).toNat =
      output.toNat + Cuts.Tail.base message.size := by
    unfold Cuts.Tail.outTail; rw [add_toNat_lt (by omega)]
  have hit : (Cuts.Tail.inTail input message.size).toNat =
      input.toNat + Cuts.Tail.base message.size := by
    unfold Cuts.Tail.inTail; rw [add_toNat_lt (by omega)]
  have hos (k : Nat) (hk : k < message.size) := h.outStack (output.toNat + k)
    (by simp only [outputRegion, MemoryRegion.Contains]; omega)
  have his (k : Nat) (hk : k < message.size) := h.inputStack (input.toNat + k)
    (by simp only [inputRegion, MemoryRegion.Contains]; omega)
  have hoc (k : Nat) (hk : k < message.size) := h.outCipher (output.toNat + k)
    (by simp only [outputRegion, MemoryRegion.Contains]; omega)
  have hic (k : Nat) (hk : k < message.size) := h.inputCipher (input.toNat + k)
    (by simp only [inputRegion, MemoryRegion.Contains]; omega)
  have hcs (k : Nat) (hk : k < 0x80) := h.cipherStack ((rdi.read s).toNat + k)
    (by simp only [cipherRegion, cipherBytes, MemoryRegion.Contains]; omega)
  simp only [stackRegion, cipherRegion, cipherBytes, MemoryRegion.Contains] at hos his hoc hic hcs
  simp only [stackRegion] at hsp1
  have hout : (Cuts.Tail.tail message.size ≠ 0 →
        MemWritable w (Cuts.Tail.outTail output message.size) (Cuts.Tail.tail message.size)) ∧
      Cuts.Tail.NotCode (Cuts.Tail.outTail output message.size) (Cuts.Tail.tail message.size) := by
    by_cases ht : Cuts.Tail.tail message.size = 0
    · rw [ht]
      exact ⟨fun h => absurd rfl h, fun i hi => absurd hi (by omega)⟩
    · have hr := region_writable h.out hg (Cuts.Tail.base message.size)
        (Cuts.Tail.tail message.size) (by omega) (by simp only [outputRegion]; omega)
      have he : BitVec.ofNat 64 ((outputRegion output message.size).start +
          Cuts.Tail.base message.size) = Cuts.Tail.outTail output message.size := by
        unfold Cuts.Tail.outTail
        simp only [outputRegion]
        rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      rw [he] at hr
      exact ⟨fun _ => hr.1, hr.2⟩
  exact { rsp := hrsp
          stack := hst.1
          stackCode := hst.2
          state := hcw.1
          stateCode := by
            intro i hi; have := hcw.2 i hi; simpa using this
          stateStack := rangeApart_of (by omega) (by omega) fun i hi j hj => by
            have := hcs i hi; omega
          out := hout.1
          outCode := hout.2
          outStack := rangeApart_of (by omega) (by omega) fun i hi j hj => by
            rw [hot]; have := hos (Cuts.Tail.base message.size + i) (by omega)
            omega
          outState := rangeApart_of (by omega) (by omega)
            fun i hi j hj => by
              rw [hot]; have := hoc (Cuts.Tail.base message.size + i) (by omega)
              omega
          inLow := hil
          outLow := hol
          inStack := rangeApart_of (by omega) (by omega) fun i hi j hj => by
            rw [hit]; have := his (Cuts.Tail.base message.size + i) (by omega)
            omega
          inState := rangeApart_of (by omega) (by omega)
            fun i hi j hj => by
              rw [hit]; have := hic (Cuts.Tail.base message.size + i) (by omega)
              omega
          alias := by
            rcases h.alias with he | hd
            · exact .inl he
            · refine .inr (rangeApart_of (by omega) (by omega) fun i hi j hj => ?_)
              rw [hit, hot]
              intro he
              exact hd (input.toNat + (Cuts.Tail.base message.size + i))
                (by simp only [inputRegion, MemoryRegion.Contains]; omega)
                (by simp only [outputRegion, MemoryRegion.Contains]; omega) }

end Exit

section Stepping

variable [Bindings] (boundary : ReturnBoundary)
  (hb : boundary.rip.toNat < entry.toNat ∨ codeEnd ≤ boundary.rip.toNat)
  {s : RamState} {key : Vector UInt8 32} {counter : UInt32} {nonce : Vector UInt8 12}
  {input output : BitVec 64} {message : ByteArray}

include hb

theorem enter {j : Nat} {t : RamState} (h : CallPre s key counter nonce input output message)
    (hh : Head s key counter nonce input output message j t) :
    ∃ fuel u, Advances boundary fuel t u ∧
      Mixing s key counter nonce input output message j u := by
  have hb' := hb_cut hb
  have hf := hh.frame
  have hsp : stackPtr t = sp s := hf.rsp
  have hst := frame_stack_writable h hf.agrees.grow 0 0x80 (by decide) (by decide)
  simp only [BitVec.add_zero] at hst
  have hrf : Cuts.Rounds.RFrame (sp s) t := ⟨by rw [Cuts.Tail.rspOf_eq, hsp], hst.1, hst.2⟩
  have hcode : CodeIn (codeRange 0x100c70 enterBytes) t := by
    have h' := MemoryRoutines.Machine.program_text_slice hf.code 0xc70 96
      (by rw [Cuts.Rounds.textBytes_size_eq]; omega)
    rwa [show Extracted.textBytes.toListFrom 0xc70 96 = enterBytes from by decide +kernel,
      show Extracted.textAddress + BitVec.ofNat 64 0xc70 = 0x100c70 from by decide] at h'
  obtain ⟨fuel, u, ha, hru, -, he⟩ := enterBlock boundary hb' (sp s) t hf.ready hcode ⟨hh.rip, hrf⟩
  have hs : rspOf t = sp s := hrf.rsp
  have hag : AgreesExcept (enterChanges (sp s)) t u := by
    have hs' := hs
    have ha' := he.agrees
    x86_norm at hs'
    x86_norm [enterEffect, hs'] at ha'
    exact ha'.mono (by simp (config := {decide := true}) [enterChanges, Cuts.Rounds.regScratch])
  have hL := enterChanges_local (sp s)
  have hcu : CodeIn Extracted.programImage u :=
    hrf.codeIn (hL.good fun i hi => by unfold EnterFree at hi; omega) hag hf.code
  have hfu := frame_transfer h hf hL (fun _ h => h.elim) hag hru hcu
  have hspu : stackPtr u = sp s := hfu.rsp
  have hw : Write.AllHold t (Cuts.Rounds.cut (sp s) enterPre (words key counter nonce j) ++
      [⟨(Operand.reg 7 : Operand 64), BitVec.ofNat 64 j⟩]) := by
    have hi (k : Fin 16) (o : Nat) (hm : (k, o) ∈ Cuts.Xor.initSlot) (h12 : k ≠ 12) :=
      (slot32_read hsp o).symm.trans (hh.inits (k, o) hm h12)
    simp only [Cuts.Rounds.cut, enterPre, List.map, Cuts.Rounds.Loc.op, List.cons_append,
      List.nil_append, Write.AllHold]
    exact ⟨reg32_of_64 hh.r10, reg32_of_64 hh.r11, reg32_of_64 hh.r12, reg32_of_64 hh.r8,
      hi 0 0x58 (by decide) (by decide), hi 1 0x10 (by decide) (by decide),
      hi 2 0xc (by decide) (by decide), hi 3 0x40 (by decide) (by decide),
      hi 5 0x34 (by decide) (by decide), hi 6 0x30 (by decide) (by decide),
      hi 7 0x2c (by decide) (by decide), hi 9 0x28 (by decide) (by decide),
      hi 10 0x24 (by decide) (by decide), hi 11 0x20 (by decide) (by decide),
      hi 14 0x1c (by decide) (by decide), hi 15 0x18 (by decide) (by decide), hh.rdi⟩
  have hpost := allHold_iff.mp (enterWords hs hw he)
  have p70 := hpost ⟨(Operand.mem (sp s + 0x70) : Operand 64), BitVec.ofNat 64 j⟩ (by simp)
  have p78 := hpost ⟨(Operand.mem (sp s + 0x78) : Operand 64), 0xa⟩ (by simp)
  have p3c := hpost ⟨(Operand.mem (sp s + 0x3c) : Operand 32),
    (words key counter nonce j)[12].toBitVec⟩ (by simp)
  have k32 (o : Nat) (ho : ∀ i < 4, ¬ EnterFree (o + i)) (hlt : o < 0x100) :
      Cuts.Xor.slot32 u o = Cuts.Xor.slot32 t o := by
    unfold Cuts.Xor.slot32 Cuts.Xor.slot
    rw [hspu, hsp]
    exact hL.load hag 32 o (by omega) ho (fun _ _ h => h)
  have k64 (o : Nat) (ho : ∀ i < 8, ¬ EnterFree (o + i)) (hlt : o < 0x100) :
      Cuts.Xor.slot64 u o = Cuts.Xor.slot64 t o := by
    unfold Cuts.Xor.slot64 Cuts.Xor.slot
    rw [hspu, hsp]
    exact hL.load hag 64 o (by omega) ho (fun _ _ h => h)
  have t64 (o : Nat) (ho : ∀ i < 8, ¬ EnterFree (o + i)) (hlt : o < 0x100) :
      Cuts.Tail.slot64 u (sp s) o = Cuts.Tail.slot64 t (sp s) o :=
    hL.load hag 64 o (by omega) ho (fun _ _ h => h)
  have hsize := h.messageLow
  have hnb : 64 * nblocks message.size ≤ message.size := by unfold nblocks; omega
  have hjl := hh.lt
  refine ⟨fuel, u, ha, ⟨⟨hfu, hh.lt, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_, ?_, ?_⟩⟩
  · rw [slot64_read hspu]; exact p70
  · intro e he'
    simp only [Cuts.Xor.initSlot, List.mem_cons, List.not_mem_nil, or_false] at he'
    rcases he' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl
    all_goals first
      | (rw [k32 _ (by intro i hi; unfold EnterFree; omega) (by decide)]
         exact hh.inits _ (by decide) (by decide))
      | (rw [slot32_read hspu]; exact p3c)
  · rw [k64 0x68 (by intro i hi; unfold EnterFree; omega) (by decide)]; exact hh.inSlot
  · rw [k64 0x60 (by intro i hi; unfold EnterFree; omega) (by decide)]; exact hh.outSlot
  · rw [k64 0x50 (by intro i hi; unfold EnterFree; omega) (by decide)]; exact hh.count
  · have hs0 := hh.slots
    exact ⟨(t64 0x48 (by intro i hi; unfold EnterFree; omega) (by decide)).trans hs0.state,
      (t64 0x88 (by intro i hi; unfold EnterFree; omega) (by decide)).trans hs0.output,
      (t64 0x90 (by intro i hi; unfold EnterFree; omega) (by decide)).trans hs0.input,
      (t64 0x98 (by intro i hi; unfold EnterFree; omega) (by decide)).trans hs0.head,
      (t64 0xa0 (by intro i hi; unfold EnterFree; omega) (by decide)).trans hs0.tail,
      (t64 0xa8 (by intro i hi; unfold EnterFree; omega) (by decide)).trans hs0.length⟩
  · refine ⟨hh.state.1, fun i => ?_⟩
    have hcl := h.cipher.low
    refine (keep_far h hL hag (r := cipherRegion s) h.cipherStack ?_ id).trans (hh.state.2 i)
    have hi := i.isLt
    have hsz := hh.state.1
    simp only [MemoryRegion.HasLength, wordsRegion] at hsz
    simp only [cipherRegion, wordsRegion, cipherBytes, MemoryRegion.Contains] at hcl ⊢
    rw [BitVec.toNat_ofNat]; omega
  · intro i h1 h2
    refine (keep_far h hL hag (r := inputRegion input message.size) h.inputStack ?_ id).trans
      (hh.rest i h1 h2)
    simp only [inputRegion, MemoryRegion.Contains]
    rw [add_toNat_lt (by omega)]; omega
  · intro i hi
    have hil : i < message.size := by omega
    refine (keep_far h hL hag (r := outputRegion output message.size) h.outStack ?_ id).trans
      (hh.wrote i hi)
    have := h.out.low
    simp only [outputRegion, MemoryRegion.Contains] at this ⊢
    rw [add_toNat_lt (by omega)]; omega
  · rw [he.rip]; x86_norm [enterEffect]
  · exact hrf.of_agrees (hL.good fun i hi => by unfold EnterFree at hi; omega) hag
  · exact allHold_iff.mpr fun w hw => hpost w (List.mem_append_left _ hw)
  · exact p78

set_option maxHeartbeats 8000000 in
                                                                                         
                                                                                            
                  
theorem block_exit {j : Nat} {t u : RamState}
    (h : CallPre s key counter nonce input output message)
    (hk : Kept s key counter nonce input output message j t)
    (hp : Cuts.Xor.FeedPost t u (mixed (words key counter nonce j)) (words key counter nonce j)
      j output (block message j))
    (hr : ReadyToStep u) (hc : CodeIn Extracted.programImage u) :
    ∃ fuel v, Advances boundary fuel u v ∧
      (if j + 1 < nblocks message.size then Head s key counter nonce input output message (j + 1) v
        else AtTail s key counter nonce input output message v) := by
  have hb' := hb_cut hb
  have hf := hk.frame
  have hsp : stackPtr t = sp s := hf.rsp
  have hjl := hk.lt
  have hnb : 64 * nblocks message.size ≤ message.size := by unfold nblocks; omega
  have hj64 : 64 * j + 64 ≤ message.size := by omega
  obtain ⟨hsp1, hsp2⟩ := sp_toNat h
  have hspu : stackPtr u = sp s :=
    (Cuts.Tail.stackPtr_agrees hp.agrees (by simp [Cuts.Xor.changes])).trans hsp
  have hgu : ∀ x : BitVec 64, (s.external[x]?).isSome → (u.external[x]?).isSome :=
    fun x hx => hp.agrees.grow x (hf.agrees.grow x hx)
  have hG0 : AgreesExcept (Cuts.Xor.changes t output j ++ exitExtra (st s)) t u :=
    hp.agrees.mono fun c hc => List.mem_append_left _ hc
  have hfu := exit_facts h hk hp hG0 (AgreesExcept.refl _ _) hr hc
  have hrd := (frame_stack_writable h hgu 0x50 8 (by decide) (by decide)).1.readable
  obtain ⟨u1, a1, r1, c1, e1⟩ := Cuts.Tail.step (boundary := boundary)
    (cmp_m64_r64_effect_step 0x1010a8 0x48 (by unfold RexWPrefix; decide) 7
      (.sib 4 none 0 (.d8 0x50)) (by decide) (by decide) (by decide))
    hr hc (MemoryRoutines.Machine.program_text_slice hc 0x10a8 5 (by decide +kernel))
    ⟨by rw [hp.rip]; rfl, by
      simp only [AddrMode.addr]
      rw [Cuts.Tail.reg64_rsp, hspu]
      exact hrd⟩
    (by
      intro he
      apply Cuts.Tail.ne_boundary hb' (p := 0x1010ad) (by decide) (by decide)
      rw [← he]; rfl)
    (Effect.Avoids.of_noMem (by simp [Component.Covers]) _)
  have hZ : (StatusFlags.ofRFLAGS u1.RFLAGS).ZF = decide (nblocks message.size = j + 1) := by
    have hz := e1.flags
    simp only [Effect.FlagsHold, cmpMREffect, StatusFlagsOutcome.Allows,
      StatusFlagsOutcome.ofStatusFlags, FlagAllows] at hz
    rw [hz.2.2.2.1, cmpSpec_ZF]
    have h50 := hfu.count
    rw [slot64_read hspu] at h50
    have h7 := hp.rdi
    simp only [AddrMode.addr]
    rw [Cuts.Tail.reg64_rsp, hfu.frame.rsp,
      show (Disp.d8 80).value = BitVec.ofNat 64 0x50 from by decide,
      show gprNumber 0 (rexR (UInt8.toBitVec 72)) 7 = 7 from by decide]
    change ((Operand.mem (sp s + BitVec.ofNat 64 0x50) : Operand 64).read u ==
      Cuts.Xor.reg64 u 7) = _
    rw [h50, h7]
    have hsz := h.messageLow
    rw [Bool.eq_iff_iff]
    simp only [beq_iff_eq, decide_eq_true_eq]
    constructor
    · intro he
      have := congrArg BitVec.toNat he
      simp only [BitVec.toNat_ofNat] at this
      rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this
      exact this
    · intro he; rw [he]
  have g1 := e1.agrees
  simp only [cmpMREffect_components] at g1
  have hjr : (jccEffect 0x1010ad 6 5 ((0xfffffbbd : BitVec 32).signExtend 64) u1).rip =
      if j + 1 < nblocks message.size then 0x100c70 else 0x1010b3 := by
    by_cases hq : j + 1 < nblocks message.size
    · simp only [hq, ↓reduceIte]
      have hne : ¬ nblocks message.size = j + 1 := by omega
      simp only [jccEffect, branchEffect, condHolds_5, hZ, hne, decide_false, Bool.not_false,
        ite_true]
      decide
    · simp only [hq, ↓reduceIte]
      have hne : nblocks message.size = j + 1 := by omega
      simp only [jccEffect, branchEffect, condHolds_5, hZ, hne, decide_true, Bool.not_true,
        Bool.false_eq_true, ite_false]
      decide
  obtain ⟨u2, a2, r2, c2, e2⟩ := Cuts.Tail.step (boundary := boundary)
    (jcc_rel32_effect_step 0x1010ad 5 0xfffffbbd) r1 c1
    (MemoryRoutines.Machine.program_text_slice c1 0x10ad 6 (by decide +kernel))
    ⟨e1.rip.trans rfl, fun _ => by decide⟩
    (by
      rw [hjr]
      split
      · exact Cuts.Tail.ne_boundary hb' (by decide) (by decide)
      · exact Cuts.Tail.ne_boundary hb' (by decide) (by decide))
    (Effect.Avoids.of_noMem (by simp [jccEffect, Component.Covers]) _)
  have g2 := e2.agrees
  simp only [jccEffect, branchEffect_components] at g2
  have hip2 := e2.rip.trans hjr
  have g12 : AgreesExcept (exitExtra (st s)) u u2 :=
    (g1.trans g2).mono (by simp [exitExtra, Cuts.Rounds.regScratch])
  have G2 : AgreesExcept (Cuts.Xor.changes t output j ++ exitExtra (st s)) t u2 :=
    (hp.agrees.trans g12).mono fun c hc => hc
  have hfx := exit_facts h hk hp G2 g12 r2 c2
  have hext2 : u2.external = u.external :=
    (g1.trans g2).external (by simp [Component.Covers])
  have rd (r : BitVec 5) : Cuts.Xor.reg64 u2 r = Cuts.Xor.reg64 u r :=
    (g1.trans g2).read (by simp)
  by_cases hq : j + 1 < nblocks message.size
  · simp only [hq, ite_true] at hip2 ⊢
    refine ⟨1 + 1, u2, a1.trans a2, ?_⟩
    have hW (k : Nat) (hk : k < 16) (h12 : k ≠ 12) := words_other' key counter nonce j (j + 1) k hk h12
    exact { frame := hfx.frame
            rip := hip2
            lt := hq
            rdi := (rd 7).trans hp.rdi
            r12 := by
              rw [rd 12, hp.r12, words_12_succ]
            r10 := by rw [rd 10, hp.r10, hW 4 (by decide) (by decide)]
            r11 := by rw [rd 11, hp.r11, hW 8 (by decide) (by decide)]
            r8 := by rw [rd 8, hp.r8, hW 13 (by decide) (by decide)]
            inits := hfx.inits
            inSlot := hfx.inSlot
            outSlot := hfx.outSlot
            count := hfx.count
            slots := hfx.slots
            state := hasBytes_keep hk.state fun i hi => by
              rw [hext2]
              have hcl := h.cipher.low
              refine keep_far h (feed_local hsp) hp.agrees (r := cipherRegion s) h.cipherStack ?_
                (cipher_not_out h hj64 (i := i) (by omega))
              simp only [cipherRegion, cipherBytes, MemoryRegion.Contains] at hcl ⊢
              rw [add_toNat_lt (by unfold st; omega)]; unfold st; omega
            rest := hfx.rest
            wrote := hfx.wrote }
  · simp only [hq, ite_false] at hip2 ⊢
    have hnbj : nblocks message.size = j + 1 := by omega
    have hspu2 : stackPtr u2 = sp s := hfx.frame.rsp
    have hgu2 : ∀ x : BitVec 64, (s.external[x]?).isSome → (u2.external[x]?).isSome :=
      fun x hx => hfx.frame.agrees.grow x hx
    have hrd48 := (frame_stack_writable h hgu2 0x48 8 (by decide) (by decide)).1.readable
    obtain ⟨u3, a3, r3, c3, e3⟩ := Cuts.Tail.step (boundary := boundary)
      (mov_r64_m64_effect_step 0x1010b3 0x48 (by unfold RexWPrefix; decide) 7
        (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide))
      r2 c2 (MemoryRoutines.Machine.program_text_slice c2 0x10b3 5 (by decide +kernel))
      ⟨hip2, by
        simp only [AddrMode.addr]
        rw [Cuts.Tail.reg64_rsp, hspu2]
        exact hrd48⟩
      (by
        intro he
        apply Cuts.Tail.ne_boundary hb' (p := 0x1010b8) (by decide) (by decide)
        rw [← he]; rfl)
      (Effect.Avoids.of_noMem (by simp [Component.Covers]) _)
    have g3 := e3.agrees
    simp only [movR64M64Effect_components,
      show gprNumber 0 (rexR (UInt8.toBitVec 0x48)) 7 = 7 from by decide] at g3
    have hrdi3 : Cuts.Xor.reg64 u3 7 = st s := by
      have hw := e3.writes
      simp only [movR64M64Effect, Write.AllHold,
        show gprNumber 0 (rexR (UInt8.toBitVec 0x48)) 7 = 7 from by decide] at hw
      change (Operand.reg 7 : Operand 64).read u3 = st s
      rw [hw]
      simp only [AddrMode.addr]
      rw [Cuts.Tail.reg64_rsp, hspu2, show (Disp.d8 0x48).value = BitVec.ofNat 64 0x48 from by decide]
      exact hfx.slots.state
    have hgu3 : ∀ x : BitVec 64, (s.external[x]?).isSome → (u3.external[x]?).isSome :=
      fun x hx => g3.grow x (hgu2 x hx)
    have hc0 := region_writable h.cipher hgu3 0 0x80 (by decide)
      (by simp [cipherRegion, cipherBytes])
    rw [← st_eq] at hc0
    have hc30 := region_writable h.cipher hgu3 0x30 4 (by decide)
      (by simp [cipherRegion, cipherBytes])
    have hst30 : BitVec.ofNat 64 ((cipherRegion s).start + 0x30) = st s + 0x30 := by
      simp only [cipherRegion, st]
      rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]; rfl
    rw [hst30] at hc30
    have haddr4 : storeAddrAt 0x1010b8 (.base 7 (.d8 0x30))
        (3 + (AddrMode.base 7 (.d8 0x30)).tail.length) u3 = st s + 0x30 := by
      simp only [storeAddrAt, AddrMode.addr]
      rw [show AddrMode.reg64 7 u3 = Cuts.Xor.reg64 u3 7 from rfl, hrdi3]
      rfl
    obtain ⟨u4, a4, r4, c4, e4⟩ := Cuts.Tail.step (boundary := boundary)
      (mov_m32_r32_effect_step 0x1010b8 0x44 (by unfold RexNoWPrefix; decide) 4
        (.base 7 (.d8 0x30)) (by decide) (by decide) (by decide))
      r3 c3 (MemoryRoutines.Machine.program_text_slice c3 0x10b8 4 (by decide +kernel))
      ⟨e3.rip.trans rfl, by rw [haddr4]; exact hc30.1, by
        rw [haddr4]
        exact Cuts.Rounds.ap_code hc0.2 0x30 4 (by decide) _ (by decide) (by decide)⟩
      (by
        intro he
        apply Cuts.Tail.ne_boundary hb' (p := 0x1010bc) (by decide) (by decide)
        rw [← he]; rfl)
      (Cuts.Tail.store_avoids (by simp only [movM32R32Effect, storeEffect_components]; rw [haddr4])
        (fun i hi => hc30.2 i (by simpa using hi)))
    have g4 := e4.agrees
    simp only [movM32R32Effect, storeEffect_components, haddr4] at g4
    have hw4 : (Operand.mem (st s + 0x30) : Operand 32).read u4 =
        (words key counter nonce (j + 1))[12].toBitVec := by
      have hw := e4.writes
      simp only [movM32R32Effect, storeEffect, Write.AllHold, haddr4,
        show gprNumber 0 (rexR (UInt8.toBitVec 0x44)) 4 = 12 from by decide] at hw
      rw [hw, show (Operand.reg 12 : Operand 32).read u3 = (Operand.reg 12 : Operand 32).read u from
        ((g1.trans g2).trans g3).read (by simp)]
      rw [reg32_of_64 hp.r12, words_12_succ]
    have hspu4 : stackPtr u4 = sp s := by
      rw [Cuts.Tail.stackPtr_agrees (g3.trans g4) (by simp), hspu2]
    have hgu4 : ∀ x : BitVec 64, (s.external[x]?).isSome → (u4.external[x]?).isSome :=
      fun x hx => g4.grow x (hgu3 x hx)
    have hrdA8 := (frame_stack_writable h hgu4 0xa8 8 (by decide) (by decide)).1.readable
    obtain ⟨u5, a5, r5, c5, e5⟩ := Cuts.Tail.step (boundary := boundary)
      (mov_r64_m64_effect_step 0x1010bc 0x4c (by unfold RexWPrefix; decide) 3
        (.sib 4 none 0 (.d32 0xa8)) (by decide) (by decide) (by decide))
      r4 c4 (MemoryRoutines.Machine.program_text_slice c4 0x10bc 8 (by decide +kernel))
      ⟨e4.rip.trans rfl, by
        simp only [AddrMode.addr]
        rw [Cuts.Tail.reg64_rsp, hspu4]
        exact hrdA8⟩
      (by
        intro he
        apply Cuts.Tail.ne_boundary hb' (p := 0x1010c4) (by decide) (by decide)
        rw [← he]; rfl)
      (Effect.Avoids.of_noMem (by simp [Component.Covers]) _)
    have g5 := e5.agrees
    simp only [movR64M64Effect_components,
      show gprNumber 0 (rexR (UInt8.toBitVec 0x4c)) 3 = 11 from by decide] at g5
    have hspu5 : stackPtr u5 = sp s := by
      rw [Cuts.Tail.stackPtr_agrees g5 (by simp), hspu4]
    have hgu5 : ∀ x : BitVec 64, (s.external[x]?).isSome → (u5.external[x]?).isSome :=
      fun x hx => g5.grow x (hgu4 x hx)
    have hrdA0 := (frame_stack_writable h hgu5 0xa0 8 (by decide) (by decide)).1.readable
    obtain ⟨u6, a6, r6, c6, e6⟩ := Cuts.Tail.step (boundary := boundary)
      (mov_r64_m64_effect_step 0x1010c4 0x4c (by unfold RexWPrefix; decide) 7
        (.sib 4 none 0 (.d32 0xa0)) (by decide) (by decide) (by decide))
      r5 c5 (MemoryRoutines.Machine.program_text_slice c5 0x10c4 8 (by decide +kernel))
      ⟨e5.rip.trans rfl, by
        simp only [AddrMode.addr]
        rw [Cuts.Tail.reg64_rsp, hspu5]
        exact hrdA0⟩
      (by
        intro he
        apply Cuts.Tail.ne_boundary hb' (p := 0x1010cc) (by decide) (by decide)
        rw [← he]; rfl)
      (Effect.Avoids.of_noMem (by simp [Component.Covers]) _)
    have g6 := e6.agrees
    simp only [movR64M64Effect_components,
      show gprNumber 0 (rexR (UInt8.toBitVec 0x4c)) 7 = 15 from by decide] at g6
    have hext65 : u6.external = u5.external := g6.external (by simp [Component.Covers])
    have hext54 : u5.external = u4.external := g5.external (by simp [Component.Covers])
    have hsub : ∀ c ∈ [Component.reg 7, .rip] ++ [.mem (st s + 0x30) 4, .rip] ++
        [Component.reg 11, .rip] ++ [Component.reg 15, .rip], c ∈ exitExtra (st s) := by
      intro c hc
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at hc
      rcases hc with h | h | h | h | h | h | h | h <;> subst h <;>
        simp [exitExtra, Cuts.Rounds.regScratch]
    have g36 := (((g3.trans g4).trans g5).trans g6).mono hsub
    have G : AgreesExcept (Cuts.Xor.changes t output j ++ exitExtra (st s)) t u6 :=
      (G2.trans g36).mono fun c hc => by
        rcases List.mem_append.mp hc with h | h
        · exact h
        · exact List.mem_append_right _ h
    have Gu : AgreesExcept (exitExtra (st s)) u u6 :=
      (g12.trans g36).mono fun c hc => by
        rcases List.mem_append.mp hc with h | h <;> exact h
    have hfx6 := exit_facts h hk hp G Gu r6 c6
    have hr11 : Cuts.Xor.reg64 u6 11 = BitVec.ofNat 64 message.size := by
      have hw := e5.writes
      simp only [movR64M64Effect, Write.AllHold,
        show gprNumber 0 (rexR (UInt8.toBitVec 0x4c)) 3 = 11 from by decide] at hw
      change (Operand.reg 11 : Operand 64).read u6 = _
      rw [g6.read (by simp), hw]
      simp only [AddrMode.addr]
      rw [Cuts.Tail.reg64_rsp, hspu4,
        show (Disp.d32 0xa8).value = BitVec.ofNat 64 0xa8 from by decide]
      change memLoad u4.external (sp s + BitVec.ofNat 64 0xa8) 64 = _
      rw [← hext54, ← hext65]
      exact hfx6.slots.length
    have hr15 : Cuts.Xor.reg64 u6 15 = BitVec.ofNat 64 (Cuts.Tail.tail message.size) := by
      have hw := e6.writes
      simp only [movR64M64Effect, Write.AllHold,
        show gprNumber 0 (rexR (UInt8.toBitVec 0x4c)) 7 = 15 from by decide] at hw
      change (Operand.reg 15 : Operand 64).read u6 = _
      rw [hw]
      simp only [AddrMode.addr]
      rw [Cuts.Tail.reg64_rsp, hspu5,
        show (Disp.d32 0xa0).value = BitVec.ofNat 64 0xa0 from by decide]
      change memLoad u5.external (sp s + BitVec.ofNat 64 0xa0) 64 = _
      rw [← hext65]
      exact hfx6.slots.tail
    have hr7 : Cuts.Xor.reg64 u6 7 = st s := by
      rw [show Cuts.Xor.reg64 u6 7 = Cuts.Xor.reg64 u3 7 from
        ((g4.trans g5).trans g6).read (by simp)]
      exact hrdi3
    have hbase : Cuts.Tail.base message.size = 64 * (j + 1) := by
      unfold Cuts.Tail.base; rw [← hnbj]; rfl
    have hgu6 : ∀ x : BitVec 64, (s.external[x]?).isSome → (u6.external[x]?).isSome :=
      fun x hx => hfx6.frame.agrees.grow x hx
    have hcw6 := region_writable h.cipher hgu6 0 0x80 (by decide)
      (by simp [cipherRegion, cipherBytes])
    rw [← st_eq] at hcw6
    have hcl := h.cipher.low
    simp only [cipherRegion, cipherBytes] at hcl
    have hL := exit_local (output := output) (st := st s) (j := j) hsp
    have hwords : Cuts.Tail.BytesAt (st s) (serialize (words key counter nonce
        (nblocks message.size))) u6 := by
      refine state_bytes (fun i hi => hcw6.1.mem i (by omega)) fun i hi => ?_
      rw [getElem!_pos _ i hi]
      by_cases hi12 : i = 12
      · subst hi12
        rw [hext65, hext54, hnbj]
        exact hw4
      · have hfar (k : Nat) (hk : k < 4) :
            (st s + BitVec.ofNat 64 (4 * i + k)).toNat < (sp s).toNat ∨
              (sp s).toNat + 0x170 ≤ (st s + BitVec.ofNat 64 (4 * i + k)).toNat := by
          rw [add_toNat_lt (by unfold st at *; omega)]
          obtain ⟨h1, -⟩ := sp_toNat h
          have := h.cipherStack ((st s).toNat + (4 * i + k))
            (by simp only [cipherRegion, cipherBytes, MemoryRegion.Contains, st]; omega)
          simp only [stackRegion, MemoryRegion.Contains] at this h1
          rw [h1]; unfold frameBytes at *; omega
        have hnout (k : Nat) (hk : k < 4) :
            ¬ ExitOut output (st s) j (st s + BitVec.ofNat 64 (4 * i + k)) := by
          rintro (ho | ⟨k', hk', he⟩)
          · exact cipher_not_out h hj64 (i := 4 * i + k) (by omega) ho
          · have := congrArg BitVec.toNat he
            have ht : (st s + 0x30 + BitVec.ofNat 64 k').toNat = (st s).toNat + 0x30 + k' := by
              unfold st at *; bv_omega
            rw [add_toNat_lt (by unfold st at *; omega), ht] at this
            omega
        have hkeep := Cuts.Tail.slot_keep 32 G (4 * i) fun k hk =>
          hL.nc_far (by obtain ⟨-, h2⟩ := sp_toNat h; omega) (hfar k (by omega)) (hnout k (by omega))
        unfold Cuts.Tail.slot at hkeep
        rw [hkeep]
        have hb := Cuts.Tail.load_word (fun i => state_bytesAt hk.state i) i hi
        rw [hb, ← words_zero, words_other' key counter nonce 0 _ i hi hi12]
    refine ⟨_, u6, ((((a1.trans a2).trans a3).trans a4).trans a5).trans a6, ?_⟩
    exact { frame := hfx6.frame
            cut := { rip := e6.rip.trans rfl
                     space := space_of h hgu6 hfx6.frame.rsp
                     slots := hfx6.slots
                     state := hr7
                     length := hr11
                     tail := hr15
                     words := hwords
                     rest := by rw [hbase]; exact hfx6.rest }
            wrote := by rw [hnbj]; exact hfx6.wrote }

end Stepping

end ChaCha20Poly1305.Proofs.Callee100a80.Run
