import ChaCha20Poly1305.Proofs.Callee100a80.Defs
import ChaCha20Poly1305.Proofs.Callee100a80.Run.Shared
import ChaCha20Poly1305.Proofs.Callee100a80.Cuts.Rounds
import ChaCha20Poly1305.Proofs.Callee100a80.Cuts.Xor
import ChaCha20Poly1305.Proofs.Callee100a80.Cuts.Tail
import ChaCha20Poly1305.Proofs.Common.Keystream
import ChaCha20Poly1305.Proofs.Callee100a80.Run.Stepping

namespace ChaCha20Poly1305.Proofs.Callee100a80.Run

open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Spec.Program
open Standards.RFC.ChaCha20Poly1305 ChaCha20Poly1305.Proofs.ChaCha20

section Geometry

theorem add_toNat (a : BitVec 64) (i : Nat) (h : a.toNat + i < 2 ^ 64) :
    (a + BitVec.ofNat 64 i).toNat = a.toNat + i := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show i < 2 ^ 64 by omega),
    Nat.mod_eq_of_lt h]

theorem add_eq_ofNat (a : BitVec 64) (i : Nat) (h : a.toNat + i < 2 ^ 64) :
    a + BitVec.ofNat 64 i = BitVec.ofNat 64 (a.toNat + i) := by
  apply BitVec.eq_of_toNat_eq
  rw [add_toNat a i h, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h]

theorem sub_toNat (a : BitVec 64) (k : Nat) (hk : k ≤ a.toNat) :
    (a - BitVec.ofNat 64 k).toNat = a.toNat - k := by
  have hl := a.isLt
  rw [BitVec.toNat_sub_of_le (by
    rw [BitVec.le_def, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; exact hk),
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]

theorem add_add (a : BitVec 64) (i k : Nat) :
    a + BitVec.ofNat 64 i + BitVec.ofNat 64 k = a + BitVec.ofNat 64 (i + k) := by
  rw [BitVec.add_assoc, ← BitVec.ofNat_add]

                                                       
theorem keep_byte {cs : List Component} {t u : RamState} (hg : AgreesExcept cs t u)
    {P : Nat → Prop} (hcs : ∀ c ∈ cs, ∀ x, c.Covers x → P x.toNat) {y : BitVec 64}
    (hy : ¬ P y.toNat) : u.external[y]? = t.external[y]? :=
  hg.byte fun c hc hx => hy (hcs c hc y hx)

theorem keep_load {cs : List Component} {t u : RamState} (hg : AgreesExcept cs t u)
    {P : Nat → Prop} (hcs : ∀ c ∈ cs, ∀ x, c.Covers x → P x.toNat) {a : BitVec 64} {n : Nat}
    (hy : ∀ i < n / 8, ¬ P (a + BitVec.ofNat 64 i).toNat) :
    memLoad u.external a n = memLoad t.external a n :=
  memLoad_congr fun i hi => by
    simp only [memByte]
    exact congrArg (fun o => Option.getD o 0) (keep_byte hg hcs (hy i hi))

                                                                       
theorem writable_of {s u : RamState} {R : MemoryRegion} (hw : Writable s R)
    (hgrow : ∀ x : BitVec 64, (s.external[x]?).isSome → (u.external[x]?).isSome)
    {a : BitVec 64} {len : Nat} (hpos : 0 < len) (h₁ : R.start ≤ a.toNat)
    (h₂ : a.toNat + len ≤ R.start + R.size) : MemWritable u a len := by
  have hl := hw.low
  refine ⟨by omega, fun i hi => ?_, ?_⟩
  · rw [add_eq_ofNat a i (by omega), show a.toNat + i = R.start + (a.toNat - R.start + i) by omega]
    exact hgrow _ (hw.present _ (by omega))
  · refine PageTableEntriesApart.of_bytes hpos (by omega) fun i hi => ?_
    have hc : R.Contains (a + BitVec.ofNat 64 i).toNat := by
      rw [add_toNat a i (by omega)]; exact ⟨by omega, by omega⟩
    have hav := hw.avoids _ hc
    simp only [pageTables, MemoryRegion.Contains] at hav
    omega

theorem notCode_of {s : RamState} {R : MemoryRegion} (hw : Writable s R) {a : BitVec 64}
    {len : Nat} (h₁ : R.start ≤ a.toNat) (h₂ : a.toNat + len ≤ R.start + R.size) :
    ∀ i < len, ¬ InProgram (a + BitVec.ofNat 64 i) := by
  intro i hi hp
  have hl := hw.low
  have hc : R.Contains (a + BitVec.ofNat 64 i).toNat := by
    rw [add_toNat a i (by omega)]; exact ⟨by omega, by omega⟩
  exact hw.avoids _ hc (.inl hp)

                                                
theorem apart_of {R R' : MemoryRegion} (hd : R.Disjoint R') (hl : R.start + R.size < 2 ^ 64)
    (hl' : R'.start + R'.size < 2 ^ 64) {a b : BitVec 64} {n m : Nat}
    (h₁ : R.start ≤ a.toNat) (h₂ : a.toNat + n ≤ R.start + R.size)
    (h₃ : R'.start ≤ b.toNat) (h₄ : b.toNat + m ≤ R'.start + R'.size) : RangeApart a n b m := by
  intro i hi j hj he
  have := congrArg BitVec.toNat he
  rw [add_toNat a i (by omega), add_toNat b j (by omega)] at this
  exact hd (a.toNat + i) ⟨by omega, by omega⟩ ⟨by omega, by omega⟩

end Geometry

section Kept

variable [Bindings] {s : RamState} {key : Vector UInt8 32} {counter : UInt32}
  {nonce : Vector UInt8 12} {input output : BitVec 64} {message : ByteArray}

theorem stack_geom (h : CallPre s key counter nonce input output message) :
    frameBytes ≤ (stackPtr s).toNat ∧ (stackPtr s).toNat + 8 ≤ 2 ^ 32 ∧
      (sp s).toNat = (stackPtr s).toNat - frameBytes := by
  have hl := h.stack.low
  have hs := h.stackLow
  simp only [stackRegion] at hl
  refine ⟨hs, by omega, ?_⟩
  exact sub_toNat _ _ hs

                                                                           
def ScratchOff (i : Nat) : Prop := 4 ≤ i ∧ i < 0xc ∨ 0x14 ≤ i ∧ i < 0x18 ∨ 0x78 ≤ i ∧ i < 0x80

theorem mainScratch_covers (h : CallPre s key counter nonce input output message) :
    ∀ c ∈ Cuts.Rounds.mainScratch (sp s), ∀ x, c.Covers x →
      ∃ i, ScratchOff i ∧ x.toNat = (sp s).toNat + i := by
  obtain ⟨-, hh, hsp⟩ := stack_geom h
  intro c hc x hx
  simp only [Cuts.Rounds.mainScratch, Cuts.Rounds.mainQR, Cuts.Rounds.regScratch,
    List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact hx.elim | skip
  all_goals
    obtain ⟨k, hk, rfl⟩ := hx
    unfold frameBytes at hsp
    first
    | (rw [show sp s + (4 : BitVec 64) = sp s + BitVec.ofNat 64 4 from rfl, add_add,
          add_toNat _ _ (by omega)]
       exact ⟨4 + k, by unfold ScratchOff; omega, rfl⟩)
    | (rw [show sp s + (8 : BitVec 64) = sp s + BitVec.ofNat 64 8 from rfl, add_add,
          add_toNat _ _ (by omega)]
       exact ⟨8 + k, by unfold ScratchOff; omega, rfl⟩)
    | (rw [show sp s + (0x14 : BitVec 64) = sp s + BitVec.ofNat 64 0x14 from rfl, add_add,
          add_toNat _ _ (by omega)]
       exact ⟨0x14 + k, by unfold ScratchOff; omega, rfl⟩)
    | (rw [show sp s + (0x78 : BitVec 64) = sp s + BitVec.ofNat 64 0x78 from rfl, add_add,
          add_toNat _ _ (by omega)]
       exact ⟨0x78 + k, by unfold ScratchOff; omega, rfl⟩)

                                                                                              
                                                    
def KeptSlot (i : Nat) : Prop :=
  0xc ≤ i ∧ i < 0x14 ∨ 0x18 ≤ i ∧ i < 0x44 ∨ 0x48 ≤ i ∧ i < 0x5c ∨ 0x60 ≤ i ∧ i < 0x78 ∨
    0x80 ≤ i ∧ i < 0xb0

                                                                                              
                         
structure StackScratch (s : RamState) (Q : Nat → Prop) (cs : List Component) : Prop where
  bound : ∀ i, Q i → i < Cuts.Xor.frameBytes
  regs : ∀ c ∈ cs, c.isMem = false → c ∈ Cuts.Rounds.regScratch
  mem : ∀ c ∈ cs, ∀ x, c.Covers x → ∃ i, Q i ∧ x.toNat = (sp s).toNat + i

theorem mainScratch_stackScratch (h : CallPre s key counter nonce input output message) :
    StackScratch s ScratchOff (Cuts.Rounds.mainScratch (sp s)) := by
  refine ⟨fun i hi => by unfold ScratchOff at hi; unfold Cuts.Xor.frameBytes; omega,
    fun c hc hm => ?_, mainScratch_covers h⟩
  simp only [Cuts.Rounds.mainScratch, Cuts.Rounds.mainQR, List.mem_append] at hc
  rcases hc with (hc | hc) | hc
  · exact hc
  all_goals
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> simp [Component.isMem] at hm

omit [Bindings] in
theorem scratchOff_free (i : Nat) (hk : KeptSlot i) : ¬ ScratchOff i := by
  unfold KeptSlot at hk; unfold ScratchOff; omega

variable {Q : Nat → Prop} {cs : List Component}

theorem stack_slot_keep (h : CallPre s key counter nonce input output message) {t u : RamState}
    (hq : StackScratch s Q cs) (hg : AgreesExcept cs t u) (off n : Nat)
    (hoff : off + n / 8 ≤ frameBytes) (hn : ∀ i, off ≤ i → i < off + n / 8 → ¬ Q i) :
    memLoad u.external (sp s + BitVec.ofNat 64 off) n =
      memLoad t.external (sp s + BitVec.ofNat 64 off) n := by
  obtain ⟨-, hh, hsp⟩ := stack_geom h
  refine keep_load hg (P := fun n => ∃ i, Q i ∧ n = (sp s).toNat + i) hq.mem
    fun i hi ⟨k, hk, he⟩ => ?_
  have := hq.bound k hk
  rw [add_add, add_toNat _ _ (by unfold frameBytes at hsp hoff; omega)] at he
  exact hn k (by omega) (by omega) hk

theorem ext_keep (h : CallPre s key counter nonce input output message) {t u : RamState}
    (hq : StackScratch s Q cs) (hg : AgreesExcept cs t u) {y : BitVec 64}
    (hy : ¬ (stackRegion s).Contains y.toNat) : u.external[y]? = t.external[y]? := by
  obtain ⟨hs, hh, hsp⟩ := stack_geom h
  refine keep_byte hg (P := fun n => ∃ i, Q i ∧ n = (sp s).toNat + i) hq.mem
    fun ⟨k, hk, he⟩ => hy ?_
  have := hq.bound k hk
  simp only [stackRegion, MemoryRegion.Contains]
  unfold Cuts.Xor.frameBytes at this
  unfold frameBytes at hsp hs ⊢
  omega

theorem frame_keep (h : CallPre s key counter nonce input output message) {t u : RamState}
    (hf : Frame s t output message.size) (hq : StackScratch s Q cs) (hg : AgreesExcept cs t u)
    (hr : ReadyToStep u) (hc : CodeIn Extracted.programImage u) : Frame s u output message.size := by
  obtain ⟨hs, hh, hsp⟩ := stack_geom h
  have hrsp : stackPtr u = stackPtr t := hg.agree (.reg 4) (fun hm => by
    have := hq.regs _ hm rfl
    simp [Cuts.Rounds.regScratch] at this) rfl
  refine ⟨hr, hc, hrsp.trans hf.rsp, ?_, fun e he => ?_⟩
  · refine (hf.agrees.trans hg).widen (fun c hc hm => ?_) (fun x c hc hx => ?_)
    · rcases List.mem_append.mp hc with hc | hc
      · exact hc
      · have hc' := hq.regs c hc hm
        simp only [Cuts.Rounds.regScratch, List.mem_cons, List.not_mem_nil, or_false] at hc'
        rcases hc' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl
        all_goals simp [callChanges, savedChanges]
    · rcases List.mem_append.mp hc with hc | hc
      · exact ⟨c, hc, hx⟩
      · obtain ⟨k, hk, he⟩ := hq.mem c hc x hx
        have hkb := hq.bound k hk
        unfold Cuts.Xor.frameBytes at hkb
        refine ⟨.mem (stackPtr s - BitVec.ofNat 64 frameBytes) frameBytes,
          by simp [callChanges], k, by unfold frameBytes; omega, ?_⟩
        apply BitVec.eq_of_toNat_eq
        rw [he, ← sp, add_toNat _ _ (by unfold frameBytes at hsp; omega)]
  · rw [← hf.saved e he]
    simp only [Operand.read]
    have ho : e.2 ≤ 0x30 ∧ 8 ≤ e.2 := by
      simp only [savedSlots, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    refine keep_load hg (P := fun n => ∃ i, Q i ∧ n = (sp s).toNat + i) hq.mem
      fun i hi ⟨k, hk, he'⟩ => ?_
    have hkb := hq.bound k hk
    unfold Cuts.Xor.frameBytes at hkb
    have ha : (stackPtr s - BitVec.ofNat 64 e.2).toNat = (stackPtr s).toNat - e.2 :=
      sub_toNat _ _ (by unfold frameBytes at hs; omega)
    rw [add_toNat _ _ (by omega), ha] at he'
    unfold frameBytes at hsp hs
    omega

                                                                                         
                                                                                 
theorem Kept.transfer {j : Nat} {t u : RamState}
    (h : CallPre s key counter nonce input output message)
    (hk : Kept s key counter nonce input output message j t)
    (hq : StackScratch s Q cs) (hfree : ∀ i, KeptSlot i → ¬ Q i)
    (hg : AgreesExcept cs t u) (hr : ReadyToStep u) (hc : CodeIn Extracted.programImage u) :
    Kept s key counter nonce input output message j u := by
  obtain ⟨hs, hh, hsp⟩ := stack_geom h
  have hfu := frame_keep h hk.frame hq hg hr hc
  have hu : stackPtr u = sp s := hfu.rsp
  have ht : stackPtr t = sp s := hk.frame.rsp
  have sk (off n : Nat) (hoff : off + n / 8 ≤ frameBytes)
      (hn : ∀ i, off ≤ i → i < off + n / 8 → KeptSlot i) :
      memLoad u.external (sp s + BitVec.ofNat 64 off) n =
        memLoad t.external (sp s + BitVec.ofNat 64 off) n :=
    stack_slot_keep h hq hg off n hoff fun i h1 h2 => hfree i (hn i h1 h2)
  have hsl := h.stack.low
  have hcl := h.cipher.low
  have hml := h.messageLow
  have hol := h.out.low
  simp only [stackRegion, cipherRegion, outputRegion, frameBytes, cipherBytes] at hsl hcl hol hs
  refine ⟨hfu, hk.lt, ?_, fun e he => ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold Cuts.Xor.slot64 Cuts.Xor.slot
    rw [hu, sk 0x70 64 (by decide) (by unfold KeptSlot; omega), ← ht]
    exact hk.index
  · have h1 := hk.inits e he
    unfold Cuts.Xor.slot32 Cuts.Xor.slot at h1 ⊢
    rw [hu, sk e.2 32 ?_ ?_, ← ht]
    · exact h1
    all_goals
      simp only [Cuts.Xor.initSlot, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl | rfl | rfl | rfl
      all_goals first | decide | (intro i; unfold KeptSlot; omega)
  · unfold Cuts.Xor.slot64 Cuts.Xor.slot
    rw [hu, sk 0x68 64 (by decide) (by unfold KeptSlot; omega), ← ht]
    exact hk.inSlot
  · unfold Cuts.Xor.slot64 Cuts.Xor.slot
    rw [hu, sk 0x60 64 (by decide) (by unfold KeptSlot; omega), ← ht]
    exact hk.outSlot
  · unfold Cuts.Xor.slot64 Cuts.Xor.slot
    rw [hu, sk 0x50 64 (by decide) (by unfold KeptSlot; omega), ← ht]
    exact hk.count
  · have hS := hk.slots
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> unfold Cuts.Tail.slot64 Cuts.Tail.slot
    · rw [sk 0x48 64 (by decide) (by unfold KeptSlot; omega)]; exact hS.state
    · rw [sk 0x88 64 (by decide) (by unfold KeptSlot; omega)]; exact hS.output
    · rw [sk 0x90 64 (by decide) (by unfold KeptSlot; omega)]; exact hS.input
    · rw [sk 0x98 64 (by decide) (by unfold KeptSlot; omega)]; exact hS.head
    · rw [sk 0xa0 64 (by decide) (by unfold KeptSlot; omega)]; exact hS.tail
    · rw [sk 0xa8 64 (by decide) (by unfold KeptSlot; omega)]; exact hS.length
  · refine ⟨hk.state.1, fun i => ?_⟩
    have hi := i.isLt
    have hsz : (stateBytes key counter nonce).size = 0x40 := by
      simp only [stateBytes, ByteArray.size, Vector.size_toArray]
    rw [← hk.state.2 i]
    refine ext_keep h hq hg fun hcon => h.cipherStack _ ?_ hcon
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by simp only [wordsRegion]; omega)]
    simp only [cipherRegion, wordsRegion, MemoryRegion.Contains, cipherBytes]
    omega
  · intro i hi1 hi2
    rw [← hk.rest i hi1 hi2]
    refine ext_keep h hq hg fun hcon => h.inputStack _ ?_ hcon
    rw [add_toNat _ _ (by omega)]
    simp only [inputRegion, MemoryRegion.Contains]
    omega
  · intro i hi
    have hlt := hk.lt
    unfold nblocks at hlt
    rw [← hk.wrote i hi]
    refine ext_keep h hq hg fun hcon => h.outStack _ ?_ hcon
    rw [add_toNat _ _ (by omega)]
    simp only [outputRegion, MemoryRegion.Contains]
    omega

end Kept

section Regions

variable [Bindings] {s : RamState} {key : Vector UInt8 32} {counter : UInt32}
  {nonce : Vector UInt8 12} {input output : BitVec 64} {message : ByteArray}

theorem stack_writable (h : CallPre s key counter nonce input output message) {u : RamState}
    (hf : Frame s u output message.size) : Cuts.Xor.Frame u := by
  obtain ⟨hs, hh, hsp⟩ := stack_geom h
  have hu : stackPtr u = sp s := hf.rsp
  have hl := h.stack.low
  simp only [stackRegion] at hl
  unfold frameBytes at hsp hs hl
  refine ⟨?_, ?_⟩ <;> rw [hu]
  · exact writable_of h.stack hf.agrees.grow (by decide)
      (by simp only [stackRegion, frameBytes]; omega)
      (by simp only [stackRegion, frameBytes, Cuts.Xor.frameBytes]; omega)
  · exact notCode_of h.stack (by simp only [stackRegion, frameBytes]; omega)
      (by simp only [stackRegion, frameBytes, Cuts.Xor.frameBytes]; omega)

end Regions

section Stubs

variable [Bindings] (boundary : ReturnBoundary)
  (hb : boundary.rip.toNat < entry.toNat ∨ codeEnd ≤ boundary.rip.toNat)
  {s : RamState} {key : Vector UInt8 32} {counter : UInt32} {nonce : Vector UInt8 12}
  {input output : BitVec 64} {message : ByteArray}

include hb

set_option linter.unusedSectionVars false in
                                                                                              
theorem kept_rounds {j : Nat} {t u : RamState}
    (h : CallPre s key counter nonce input output message)
    (hk : Kept s key counter nonce input output message j t)
    (hg : AgreesExcept (Cuts.Rounds.mainScratch (sp s)) t u) (hr : ReadyToStep u)
    (hc : CodeIn Extracted.programImage u) :
    Kept s key counter nonce input output message j u := by
  exact Kept.transfer h hk (mainScratch_stackScratch h) scratchOff_free hg hr hc

set_option linter.unusedSectionVars false in
                                                                                 
                                    
theorem feed_pre {j : Nat} {u : RamState} {m : Vector UInt32 16}
    (h : CallPre s key counter nonce input output message)
    (hk : Kept s key counter nonce input output message j u) (hip : u.RIP = 0x100e19)
    (_hf : Cuts.Rounds.RFrame (sp s) u)
    (hw : Write.AllHold u (Cuts.Rounds.cut (sp s) Cuts.Rounds.mainBase m)) :
    Cuts.Xor.FeedPre m (words key counter nonce j) j input output (block message j) u := by
  obtain ⟨hs, hh, hsp⟩ := stack_geom h
  have hu : stackPtr u = sp s := hk.frame.rsp
  have hlt := hk.lt
  unfold nblocks at hlt
  have hsl := h.stack.low
  have hml := h.messageLow
  have hol := h.out.low
  simp only [stackRegion, outputRegion, frameBytes] at hsl hol hs hsp
  simp only [Cuts.Rounds.cut, Cuts.Rounds.mainBase, Cuts.Rounds.Loc.op, List.map_cons,
    List.map_nil, Write.AllHold] at hw
  obtain ⟨w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15⟩ := hw
  have hin : (Cuts.Xor.inBlock input j).toNat = input.toNat + 64 * j := by
    unfold Cuts.Xor.inBlock; rw [add_toNat _ _ (by omega)]
  have hout : (Cuts.Xor.outBlock output j).toNat = output.toNat + 64 * j := by
    unfold Cuts.Xor.outBlock; rw [add_toNat _ _ (by omega)]
  have hst : (stackPtr u).toNat = (stackPtr s).toNat - 0x1a0 := by rw [hu, hsp]
  refine ⟨by rw [hip]; rfl, stack_writable h hk.frame, fun e he => ?_, ?_, hk.inits, ?_⟩
  · simp only [Cuts.Xor.mixedReg, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl <;> assumption
  · unfold Cuts.Xor.slot32 Cuts.Xor.slot
    rw [hu]
    exact w8
  · refine ⟨hk.index, hk.inSlot, hk.outSlot, by omega, fun i => ?_, ?_, ?_, ?_, ?_⟩
    · unfold Cuts.Xor.inBlock
      rw [add_add, hk.rest _ (by omega) (by omega)]
      simp [block, msg]
    · exact apart_of h.inputStack (by simp only [inputRegion]; omega)
        (by simp only [stackRegion, frameBytes]; omega)
        (by simp only [inputRegion]; omega) (by simp only [inputRegion]; omega)
        (by simp only [stackRegion, frameBytes]; omega)
        (by simp only [stackRegion, frameBytes, Cuts.Xor.frameBytes]; omega)
    · exact writable_of h.out hk.frame.agrees.grow (by decide)
        (by simp only [outputRegion]; omega) (by simp only [outputRegion]; omega)
    · exact apart_of h.outStack (by simp only [outputRegion]; omega)
        (by simp only [stackRegion, frameBytes]; omega)
        (by simp only [outputRegion]; omega) (by simp only [outputRegion]; omega)
        (by simp only [stackRegion, frameBytes]; omega)
        (by simp only [stackRegion, frameBytes, Cuts.Xor.frameBytes]; omega)
    · exact notCode_of h.out (by simp only [outputRegion]; omega)
        (by simp only [outputRegion]; omega)

end Stubs

section Tail

variable [Bindings] {s : RamState} {key : Vector UInt8 32} {counter : UInt32}
  {nonce : Vector UInt8 12} {input output : BitVec 64} {message : ByteArray}

def TailTouched (s : RamState) (output : BitVec 64) (size : Nat) (n : Nat) : Prop :=
  ((stackPtr s).toNat - frameBytes ≤ n ∧ n < (stackPtr s).toNat - 0x30) ∨
    (cipherRegion s).Contains n ∨
    (output.toNat + Cuts.Tail.base size ≤ n ∧ n < output.toNat + size)

theorem tail_covers (h : CallPre s key counter nonce input output message) :
    ∀ c ∈ Cuts.Tail.changes (sp s) (st s) output message.size, ∀ x, c.Covers x →
      TailTouched s output message.size x.toNat := by
  obtain ⟨hs, hh, hsp⟩ := stack_geom h
  have hcl := h.cipher.low
  have hol := h.out.low
  simp only [cipherRegion, outputRegion, cipherBytes] at hcl hol
  intro c hc x hx
  simp only [Cuts.Tail.changes, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | exact hx.elim | skip
  all_goals obtain ⟨k, hk, rfl⟩ := hx
  · left
    rw [add_toNat _ _ (by unfold Cuts.Tail.frameBytes at hk; unfold frameBytes at hsp hs; omega)]
    unfold Cuts.Tail.frameBytes at hk; unfold frameBytes at hsp hs ⊢; omega
  · right; left
    have : st s + 0x30 + BitVec.ofNat 64 k = st s + BitVec.ofNat 64 (0x30 + k) := add_add _ _ _
    rw [this, add_toNat _ _ (by unfold st; omega)]
    simp only [cipherRegion, MemoryRegion.Contains, cipherBytes, st]
    omega
  · right; left
    have : st s + 0x40 + BitVec.ofNat 64 k = st s + BitVec.ofNat 64 (0x40 + k) := add_add _ _ _
    rw [this, add_toNat _ _ (by unfold st; omega)]
    simp only [cipherRegion, MemoryRegion.Contains, cipherBytes, st]
    omega
  · right; right
    have hb : Cuts.Tail.base message.size + Cuts.Tail.tail message.size = message.size := by
      unfold Cuts.Tail.base Cuts.Tail.tail; omega
    unfold Cuts.Tail.outTail
    rw [add_add, add_toNat _ _ (by omega)]
    omega

                                                                                              
theorem tail_done_of {t u : RamState} (h : CallPre s key counter nonce input output message)
    (hacc : Accepted counter message.size)
    (ht : AtTail s key counter nonce input output message t)
    (hg : AgreesExcept (Cuts.Tail.changes (sp s) (st s) output message.size) t u)
    (hr : ReadyToStep u) (hc : CodeIn Extracted.programImage u)
    (hf : Cuts.Tail.Final output message.size (msg message)
      (words key counter nonce (nblocks message.size)) u) :
    Frame s u output message.size ∧ Status s u key counter nonce output message := by
  obtain ⟨hs, hh, hsp⟩ := stack_geom h
  have hcl := h.cipher.low
  have hol := h.out.low
  have hsl := h.stack.low
  simp only [cipherRegion, outputRegion, cipherBytes, stackRegion] at hcl hol hsl
  have hcov := tail_covers h
  have hrsp : stackPtr u = stackPtr t := hg.agree (.reg 4) (by simp [Cuts.Tail.changes]) rfl
  refine ⟨⟨hr, hc, hrsp.trans ht.frame.rsp, ?_, fun e he => ?_⟩, ?_⟩
  · refine (ht.frame.agrees.trans hg).widen (fun c hc hm => ?_) (fun x c hc hx => ?_)
    · rcases List.mem_append.mp hc with hc | hc
      · exact hc
      · simp only [Cuts.Tail.changes, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals first | (simp [callChanges, savedChanges]; done) | simp [Component.isMem] at hm
    · rcases List.mem_append.mp hc with hc | hc
      · exact ⟨c, hc, hx⟩
      · simp only [Cuts.Tail.changes, List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
          rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals first | exact hx.elim | skip
        · obtain ⟨k, hk, rfl⟩ := hx
          exact ⟨.mem (stackPtr s - BitVec.ofNat 64 frameBytes) frameBytes,
            by simp [callChanges], k, by unfold Cuts.Tail.frameBytes at hk; unfold frameBytes; omega,
            rfl⟩
        · exact ⟨.mem (rdi.read s + 0x30) 4, by simp [callChanges], hx⟩
        · exact ⟨.mem (rdi.read s + 0x40) 0x40, by simp [callChanges], hx⟩
        · obtain ⟨k, hk, rfl⟩ := hx
          have hb : Cuts.Tail.base message.size + Cuts.Tail.tail message.size = message.size := by
            unfold Cuts.Tail.base Cuts.Tail.tail; omega
          refine ⟨.mem output message.size, by simp [callChanges], Cuts.Tail.base message.size + k,
            by omega, ?_⟩
          unfold Cuts.Tail.outTail
          rw [add_add]
  · rw [← ht.frame.saved e he]
    simp only [Operand.read]
    have ho : e.2 ≤ 0x30 ∧ 8 ≤ e.2 := by
      simp only [savedSlots, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    refine keep_load hg hcov fun i hi hP => ?_
    have ha : (stackPtr s - BitVec.ofNat 64 e.2).toNat = (stackPtr s).toNat - e.2 :=
      sub_toNat _ _ (by unfold frameBytes at hs; omega)
    rw [add_toNat _ _ (by omega), ha] at hP
    have hin : (stackRegion s).Contains ((stackPtr s).toNat - e.2 + i) := by
      simp only [stackRegion, MemoryRegion.Contains]; unfold frameBytes at hs ⊢; omega
    rcases hP with hP | hP | hP
    · unfold frameBytes at hP; omega
    · exact h.cipherStack _ hP hin
    · exact h.outStack _ ⟨by simp only [outputRegion]; omega, by simp only [outputRegion]; omega⟩ hin
  · unfold Status
    simp only [hacc, ↓reduceIte]
    refine ⟨hf.status, ?_⟩
    rw [chacha20Encrypt_eq_xorKeystream]
    refine ⟨by simp [MemoryRegion.HasLength, outputRegion, Common.xorKeystream_size], fun i => ?_⟩
    have hi : i.val < message.size := by
      have h1 := i.isLt
      have h2 := Common.xorKeystream_size (fun j => keystreamBlock key (counter + j.toUInt32) nonce)
        message
      omega
    simp only [outputRegion]
    rw [← add_eq_ofNat _ _ (by omega)]
    have hb : Cuts.Tail.base message.size = 64 * nblocks message.size := rfl
    have hn : nblocks message.size = message.size / 64 := rfl
    by_cases hlo : i.val < Cuts.Tail.base message.size
    · have hw := ht.wrote i.val (by omega)
      rw [chacha20Encrypt_eq_xorKeystream] at hw
      rw [keep_byte hg hcov ?_, hw]
      · simp [getElem!_pos, hi, Common.xorKeystream_size]
      · rw [add_toNat _ _ (by omega)]
        intro hP
        rcases hP with hP | hP | hP
        · exact h.outStack (output.toNat + i.val)
            ⟨by simp only [outputRegion]; omega, by simp only [outputRegion]; omega⟩
            ⟨by simp only [stackRegion]; unfold frameBytes at hP ⊢; omega,
              by simp only [stackRegion]; unfold frameBytes at hP ⊢; omega⟩
        · exact h.outCipher (output.toNat + i.val) ⟨by simp only [outputRegion]; omega, by simp only [outputRegion]; omega⟩ hP
        · omega
    · rw [hf.wrote i.val (by omega) hi, Common.xorKeystream_getElem _ _ _ hi]
      have hq : i.val / 64 = nblocks message.size := by unfold nblocks; omega
      have hr' : i.val % 64 = i.val - Cuts.Tail.base message.size := by
        unfold Cuts.Tail.base; omega
      have hv : Cuts.Tail.stream (words key counter nonce (nblocks message.size)) =
          keystreamBlock key (counter + (nblocks message.size).toUInt32) nonce := rfl
      have hm : msg message i.val = message[i.val] := getElem!_pos message i.val hi
      rw [hv, hm, getElem!_pos _ _ (by omega)]
      simp only [hq, hr']

end Tail

section TailStub

variable [Bindings] (boundary : ReturnBoundary)
  (hb : boundary.rip.toNat < entry.toNat ∨ codeEnd ≤ boundary.rip.toNat)
  {s : RamState} {key : Vector UInt8 32} {counter : UInt32} {nonce : Vector UInt8 12}
  {input output : BitVec 64} {message : ByteArray}

include hb

                                                                                        
                                                                                           
                                                                                    
                                                                     
theorem tail_done {t u : RamState} (h : CallPre s key counter nonce input output message)
    (hacc : Accepted counter message.size)
    (ht : AtTail s key counter nonce input output message t)
    (hg : AgreesExcept (Cuts.Tail.changes (sp s) (st s) output message.size) t u)
    (hr : ReadyToStep u) (hc : CodeIn Extracted.programImage u)
    (hf : Cuts.Tail.Final output message.size (msg message)
      (words key counter nonce (nblocks message.size)) u) :
    Frame s u output message.size ∧ Status s u key counter nonce output message := by
  exact tail_done_of h hacc ht hg hr hc hf

end TailStub

end ChaCha20Poly1305.Proofs.Callee100a80.Run
