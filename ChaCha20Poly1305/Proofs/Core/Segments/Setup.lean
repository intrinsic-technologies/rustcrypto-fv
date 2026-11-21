import ChaCha20Poly1305.Proofs.Core.Cuts
import ChaCha20Poly1305.Proofs.MemoryRoutines.Machine.Execution
import X86Proofs.Instructions.Push.Triple
import X86Proofs.Instructions.Sub.Generated.Imm32.Triple
import X86Proofs.Instructions.Mov.Generated.MImm32C7.Triple
import X86Proofs.Instructions.Mov.Generated.MR.Triple
import X86Proofs.Instructions.Mov.Generated.RM.Triple
import X86Proofs.Instructions.Call.Triple
import ChaCha20Poly1305.Proofs.Core.Segments.Encrypt
import ChaCha20Poly1305.Proofs.Poly1305.Callee101e40
import ChaCha20Poly1305.Proofs.Core.Keygen
import X86Proofs.Instructions.Movs.Generated.Rep.Triple
import X86Proofs.Instructions.Test.Generated.R8.Triple
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Instructions.Lea.Triple

namespace ChaCha20Poly1305.Proofs.Core.Setup

open ChaCha20Poly1305.Spec.Program Prelude X86 X86.Machine
open X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.MemoryRoutines.Machine

def codeLo : Nat := 0x100650

def codeHi : Nat := 0x100840

structure Frame (lo hi : Nat) (s : RamState) : Prop where
  room : lo ≤ (rspOf s).toNat
  top : (rspOf s).toNat + hi ≤ 2 ^ 32
  present : ∀ i < lo + hi, (s.external[rspOf s - BitVec.ofNat 64 lo + BitVec.ofNat 64 i]?).isSome
  tables : 0x2020 + lo ≤ (rspOf s).toNat ∨ (rspOf s).toNat + hi ≤ 0x1000
  code : codeHi + lo ≤ (rspOf s).toNat ∨ (rspOf s).toNat + hi ≤ codeLo
  outside : ∀ i < lo + hi, ¬ InProgram (rspOf s - BitVec.ofNat 64 lo + BitVec.ofNat 64 i)

namespace Frame

variable {lo hi : Nat} {s : RamState}

theorem slot_toNat (h : Frame lo hi s) {c : BitVec 64} {len : Nat} (hc : SlotIn c len lo hi) :
    (rspOf s + c).toNat = (rspOf s).toNat - lo + (c + BitVec.ofNat 64 lo).toNat := by
  have h1 := hc
  unfold SlotIn at h1
  have hb := h.room
  have ht := h.top
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at h1 ⊢
  have := c.isLt
  omega

theorem slot_byte (h : Frame lo hi s) {c : BitVec 64} {len : Nat} (hc : SlotIn c len lo hi)
    {i : Nat} (hi : i < len) : (s.external[rspOf s + c + BitVec.ofNat 64 i]?).isSome := by
  have hs := h.slot_toNat hc
  have h1 := hc
  unfold SlotIn at h1
  have hp := h.present ((c + BitVec.ofNat 64 lo).toNat + i) (by omega)
  have heq : rspOf s + c + BitVec.ofNat 64 i =
      rspOf s - BitVec.ofNat 64 lo + BitVec.ofNat 64 ((c + BitVec.ofNat 64 lo).toNat + i) := by
    apply BitVec.eq_of_toNat_eq
    have hb := h.room
    have ht := h.top
    rw [BitVec.toNat_add, hs]
    simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat] at h1 ⊢
    have := c.isLt
    have := (rspOf s).isLt
    omega
  rw [heq]
  exact hp

theorem readable (h : Frame lo hi s) (c : BitVec 64) {len : Nat} (hc : SlotIn c len lo hi) :
    MemReadable s (rspOf s + c) len := by
  refine ⟨?_, fun i hi => h.slot_byte hc hi⟩
  rw [h.slot_toNat hc]
  have h1 := hc
  unfold SlotIn at h1
  have := h.top
  have := h.room
  omega

theorem writable (h : Frame lo hi s) (c : BitVec 64) {len : Nat} (hc : SlotIn c len lo hi) :
    MemWritable s (rspOf s + c) len := by
  have hs := h.slot_toNat hc
  have h1 := hc
  unfold SlotIn at h1
  have := h.top
  have := h.room
  have := h.tables
  refine ⟨by omega, fun i hi => h.slot_byte hc hi, ?_⟩
  simp only [PageTableEntriesApart]
  omega

theorem apart (h : Frame lo hi s) (c : BitVec 64) {len : Nat} (hc : SlotIn c len lo hi)
    (q : BitVec 64) (ilen : Nat) (hq : codeLo ≤ q.toNat ∧ q.toNat + ilen ≤ codeHi) :
    RangeApart (rspOf s + c) len q ilen := by
  have hs := h.slot_toNat hc
  have h1 := hc
  unfold SlotIn at h1
  have := h.top
  have := h.room
  have := h.code
  unfold codeLo codeHi at *
  apply RangeApart.of_toNat
  · omega
  · omega
  · rw [hs]
    generalize (c + BitVec.ofNat 64 lo).toNat = d at h1
    omega

theorem slot_addr (h : Frame lo hi s) {c : BitVec 64} {len : Nat} (hc : SlotIn c len lo hi)
    {i : Nat} (_hi : i < len) : rspOf s + c + BitVec.ofNat 64 i =
      rspOf s - BitVec.ofNat 64 lo + BitVec.ofNat 64 ((c + BitVec.ofNat 64 lo).toNat + i) := by
  have hs := h.slot_toNat hc
  have h1 := hc
  unfold SlotIn at h1
  apply BitVec.eq_of_toNat_eq
  have hb := h.room
  have ht := h.top
  rw [BitVec.toNat_add, hs]
  simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat] at h1 ⊢
  have := c.isLt
  have := (rspOf s).isLt
  omega

theorem slot_outside (h : Frame lo hi s) (c : BitVec 64) {len : Nat} (hc : SlotIn c len lo hi)
    (a : BitVec 64) (hcov : (Component.mem (rspOf s + c) len).Covers a) : ¬ InProgram a := by
  obtain ⟨i, hi, rfl⟩ := hcov
  have h1 := hc
  unfold SlotIn at h1
  rw [h.slot_addr hc hi]
  exact h.outside _ (by omega)

theorem same {t : RamState} (h : Frame lo hi s) (hsp : rspOf t = rspOf s)
    (hg : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome) : Frame lo hi t := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> rw [hsp]
  · exact h.room
  · exact h.top
  · exact fun i hi => hg _ (h.present i hi)
  · exact h.tables
  · exact h.code
  · exact h.outside

end Frame

theorem avoids_program {e : Effect}
    (h : ∀ c ∈ e.components, ∀ a, c.Covers a → ¬ InProgram a) :
    e.Avoids Extracted.programImage :=
  fun x hx c hc hcov => h c hc x.1 hcov (inProgram_of_mem hx)

theorem widenBlock [Bindings] {b : ReturnBoundary} {P : RamState → Prop} {p : BitVec 64}
    {bytes : List UInt8} {E : RamState → Effect} (h : AdvancesBlock b P (codeRange p bytes) E)
    (hsub : ∀ s, CodeIn Extracted.programImage s → CodeIn (codeRange p bytes) s)
    (hav : ∀ s, P s → (E s).Avoids Extracted.programImage) :
    AdvancesBlock b P Extracted.programImage E := by
  intro s hr hc hP
  obtain ⟨f, t, ha, hr', -, he⟩ := h s hr (hsub s hc) hP
  exact ⟨f, t, ha, hr', he.codeIn (hav s hP) hc, he⟩

theorem sub_at {p q : BitVec 64} {all bytes : List UInt8} (off : Nat)
    (hq : q = p + BitVec.ofNat 64 off) (hsub : (all.drop off).take bytes.length = bytes) :
    ∀ x ∈ codeRange q bytes, x ∈ codeRange p all :=
  hq ▸ codeRange_mem_of_drop off hsub

structure Away (boundary : ReturnBoundary) : Prop where
  ne : ∀ q : BitVec 64, 0x100000 ≤ q.toNat → q.toNat < 0x102def → q ≠ boundary.rip

theorem readable_off {s : RamState} {a : BitVec 64} {n : Nat} (h : MemReadable s a n)
    (c : BitVec 64) {len : Nat} (hc : c.toNat + len ≤ n) : MemReadable s (a + c) len := by
  refine ⟨?_, fun i hi => ?_⟩
  · have := h.low
    rw [BitVec.toNat_add]
    omega
  · have hm := h.mem (c.toNat + i) (by omega)
    have he : a + c + BitVec.ofNat 64 i = a + BitVec.ofNat 64 (c.toNat + i) := by
      rw [BitVec.add_assoc]
      congr 1
      apply BitVec.eq_of_toNat_eq
      have := h.low
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
      omega
    rw [he]
    exact hm

theorem write_reg_external {n : Nat} (s : RamState) (r : BitVec 5) (v : BitVec n) :
    (Operand.write s (Operand.reg r) v).external = s.external := rfl

theorem write_mem_external {n : Nat} (s : RamState) (a : BitVec 64) (v : BitVec n) :
    (Operand.write s (Operand.mem a) v).external = memStore s.external a v := rfl

theorem Frame.apart_data {lo hi : Nat} {s : RamState} (h : Frame lo hi s) {d : BitVec 64} {m : Nat}
    (hsep : d.toNat + m ≤ (rspOf s).toNat - lo ∨ (rspOf s).toNat + hi ≤ d.toNat)
    (hlow : d.toNat + m ≤ 2 ^ 32) (c : BitVec 64) {n : Nat} (hc : SlotIn c n lo hi)
    (k : BitVec 64) {n' : Nat} (hk : k.toNat + n' ≤ m) :
    RangeApart (rspOf s + c) n (d + k) n' := by
  have hs := h.slot_toNat hc
  have h1 := hc
  unfold SlotIn at h1
  have := h.top
  have := h.room
  have hdk : (d + k).toNat = d.toNat + k.toNat := by
    rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
  apply RangeApart.of_toNat
  · rw [hs]; omega
  · rw [hdk]; omega
  · rw [hs, hdk]
    generalize (c + BitVec.ofNat 64 lo).toNat = g at h1
    rcases hsep with h2 | h2
    · right; omega
    · left; omega

theorem readable_zero {s : RamState} {a : BitVec 64} {n len : Nat} (h : MemReadable s a n)
    (hc : len ≤ n) : MemReadable s a len :=
  ⟨by have := h.low; omega, fun i hi => h.mem i (by omega)⟩

macro "seg_norm" : tactic => `(tactic| (
  try simp only [x86_pre_simp]
  try x86_norm [pushAddr_eq_read]
  try simp only [x86_pre_simp]
  try x86_norm [pushAddr_eq_read]))

macro "seg_full" : tactic => `(tactic| (
  intro _ _
  simp (config := { decide := true }) only [x86_compose, pushAddr_eq_read, List.forall_mem_cons,
    List.forall_mem_nil, List.forall_mem_append, and_true, true_and]))

macro "seg_frame " h:term : tactic => `(tactic| first
  | exact Frame.writable $h _ (by decide +kernel)
  | exact Frame.readable $h _ (by decide +kernel)
  | exact Frame.apart $h _ (by decide +kernel) _ _ (by decide +kernel))

macro "seg_avoid " h:term : tactic => `(tactic| (
  apply Effect.avoids_codeRange
  seg_norm
  repeat' apply And.intro
  all_goals (try seg_frame $h)))

macro "seg_boundary" : tactic => `(tactic| (
  intro _ _
  x86_norm
  exact Away.ne ‹_› _ (by decide +kernel) (by decide +kernel)))

macro "seg_begin " t:term : tactic => `(tactic| (
  refine AdvancesBlock.block_first ?k $t ?sub ?pre ?av ?boundary
  case sub => exact codeRange_mem_of_take (by decide +kernel)
  try (case pre => intro s hP; have hF := hP.frame; (first
    | exact hP.rip
    | (refine ⟨hP.rip, ?_, ?_⟩ <;> seg_norm <;> seg_frame hF)
    | (refine ⟨hP.rip, ?_⟩
       seg_norm
       first
         | seg_frame hF
         | exact readable_off hP.key _ (by decide +kernel)
         | exact readable_zero hP.key (by decide)
         | exact readable_off hP.nonce _ (by decide +kernel)
         | exact readable_zero hP.nonce (by decide))))
  try (case av => intro s hP; have hF := hP.frame; seg_avoid hF)
  try (case boundary => seg_boundary)
  case' k => x86_norm [pushAddr_eq_read]))

macro "seg_then " off:num t:term : tactic => `(tactic| (
  refine AdvancesBlock.block_then ?k $t ?loc ?sub ?full ?mid ?boundary
  case loc => x86_local
  case sub => exact sub_at $off (by decide +kernel) (by decide +kernel)
  case full => seg_full
  try (case mid =>
    intro s s' hP hH hO
    have hF := hP.frame
    refine ⟨?_, Effect.Local.avoids (by x86_local) (hO true) ?_⟩
    · first
      | exact hH.rip_of (by x86_norm [pushAddr_eq_read])
      | (refine StorePre.of_holds hH (hO true) (by x86_norm [pushAddr_eq_read]) (by x86_addr_obs) ?_ ?_ <;>
         seg_norm <;> seg_frame hF)
      | (refine LoadPre.of_holds hH (hO true) (by x86_norm [pushAddr_eq_read]) (by x86_addr_obs) ?_
         seg_norm
         first
           | seg_frame hF
           | exact readable_off hP.key _ (by decide +kernel)
           | exact readable_zero hP.key (by decide)
           | exact readable_off hP.nonce _ (by decide +kernel)
           | exact readable_zero hP.nonce (by decide))
    · seg_avoid hF)
  try (case boundary => seg_boundary)
  case' k => x86_norm [pushAddr_eq_read]))

structure SegPre (p : BitVec 64) (lo hi : Nat) (s : RamState) : Prop where
  rip : s.RIP = p
  frame : Frame lo hi s
  key : MemReadable s ((Operand.reg 6 : Operand 64).read s) 32
  keySep : ((Operand.reg 6 : Operand 64).read s).toNat + 32 ≤ (rspOf s).toNat - lo ∨
    (rspOf s).toNat + hi ≤ ((Operand.reg 6 : Operand 64).read s).toNat
  nonce : MemReadable s ((Operand.reg 2 : Operand 64).read s) 12
  nonceSep : ((Operand.reg 2 : Operand 64).read s).toNat + 12 ≤ (rspOf s).toNat - lo ∨
    (rspOf s).toNat + hi ≤ ((Operand.reg 2 : Operand 64).read s).toNat


structure StackPre (p : BitVec 64) (lo hi : Nat) (s : RamState) : Prop where
  rip : s.RIP = p
  frame : Frame lo hi s

theorem prologue_sp {s t : RamState} (h : Frame 0x1c0 8 s)
    (hsp : rspOf t = rspOf s + 0xffffffffffffffd0 - 0x188) :
    (rspOf t).toNat = (rspOf s).toNat - 0x1b8 ∧
      rspOf t - BitVec.ofNat 64 8 = rspOf s - BitVec.ofNat 64 0x1c0 := by
  have hr := h.room
  have ht := h.top
  have e : rspOf s + 0xffffffffffffffd0 - 0x188 = rspOf s - BitVec.ofNat 64 0x1b8 := by
    bv_omega
  have h1 : (rspOf t).toNat = (rspOf s).toNat - 0x1b8 := by
    rw [hsp, e, BitVec.toNat_sub_of_le (by rw [BitVec.le_def, BitVec.toNat_ofNat]; omega),
      BitVec.toNat_ofNat]
  refine ⟨h1, BitVec.eq_of_toNat_eq ?_⟩
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, h1]
  omega

theorem Frame.prologue {s t : RamState} (h : Frame 0x1c0 8 s)
    (hsp : rspOf t = rspOf s + 0xffffffffffffffd0 - 0x188)
    (hg : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome) :
    Frame 8 0x1c0 t := by
  obtain ⟨h1, h2⟩ := prologue_sp h hsp
  have hr := h.room
  have ht := h.top
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · omega
  · omega
  · intro i hi; rw [h2]; exact hg _ (h.present i (by omega))
  · have := h.tables; omega
  · have := h.code; unfold codeLo codeHi at *; omega
  · intro i hi; rw [h2]; exact h.outside i (by omega)

theorem SegPre.prologue {s t : RamState} (h : SegPre 0x100650 0x1c0 8 s) {p' : BitVec 64}
    (hrip : t.RIP = p') (hsp : rspOf t = rspOf s + 0xffffffffffffffd0 - 0x188)
    (hsi : (Operand.reg 6 : Operand 64).read t = (Operand.reg 6 : Operand 64).read s)
    (hdx : (Operand.reg 2 : Operand 64).read t = (Operand.reg 2 : Operand 64).read s)
    (hg : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome) :
    SegPre p' 8 0x1c0 t := by
  obtain ⟨h1, -⟩ := prologue_sp h.frame hsp
  have hr := h.frame.room
  refine ⟨hrip, h.frame.prologue hsp hg, ?_, ?_, ?_, ?_⟩
  · rw [hsi]; exact ⟨h.key.low, fun i hi => hg _ (h.key.mem i hi)⟩
  · rw [hsi, h1]; have := h.keySep; omega
  · rw [hdx]; exact ⟨h.nonce.low, fun i hi => hg _ (h.nonce.mem i hi)⟩
  · rw [hdx, h1]; have := h.nonceSep; omega

theorem StackPre.prologue {s t : RamState} (h : SegPre 0x100650 0x1c0 8 s) {p' : BitVec 64}
    (hrip : t.RIP = p') (hsp : rspOf t = rspOf s + 0xffffffffffffffd0 - 0x188)
    (hg : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome) :
    StackPre p' 8 0x1c0 t :=
  ⟨hrip, h.frame.prologue hsp hg⟩

theorem slice_code {s : RamState} (hc : CodeIn Extracted.programImage s) (off cnt : Nat)
    {p : BitVec 64} {bytes : List UInt8} (h1 : off + cnt ≤ Extracted.textBytes.size)
    (hp : Extracted.textAddress + BitVec.ofNat 64 off = p)
    (hb : Extracted.textBytes.toListFrom off cnt = bytes) : CodeIn (codeRange p bytes) s :=
  hp ▸ hb ▸ program_text_slice hc off cnt h1

def undefinedFlags : StatusFlagsOutcome := ⟨none, none, none, none, none, none⟩

macro "seg_finish" : tactic => `(tactic| (
  apply AdvancesBlock.block_end
  intro s s' _ hH
  apply hH.weaken
  · x86_norm [pushAddr_eq_read]
  · x86_norm [pushAddr_eq_read]
  · intro i; cases i <;> x86_norm [pushAddr_eq_read, undefinedFlags]
  · x86_norm [pushAddr_eq_read]))

macro "seg_close" : tactic => `(tactic| (
  apply AdvancesBlock.block_end
  intro s t hP hH
  have hF := hP.frame
  x86_norm [pushAddr_eq_read, write_reg_external, write_mem_external] at hH
  exact hH))

macro "seg_close_data" : tactic => `(tactic| (
  apply AdvancesBlock.block_end
  intro s t hP hH
  have hF := hP.frame
  x86_norm [pushAddr_eq_read, write_reg_external, write_mem_external] at hH
  repeat rw [memLoad_memStore_of_rangeApart] at hH
  all_goals try (first
    | (refine Frame.apart_data hF hP.keySep hP.key.low _ ?_ _ ?_ <;> decide +kernel)
    | (refine Frame.apart_data hF hP.nonceSep hP.nonce.low _ ?_ _ ?_ <;> decide +kernel))
  exact hH))

def effA (s : RamState) : Effect :=
  { rip := 1050209#64,
          writes :=
            [{ n := 64, dst := Operand.mem (Operand.read s (Operand.reg 4#5) + 18446744073709551608#64),
                val := Operand.read s (Operand.reg 5#5) },
              { n := 64, dst := Operand.mem (Operand.read s (Operand.reg 4#5) + 18446744073709551600#64),
                val := Operand.read s (Operand.reg 15#5) },
              { n := 64, dst := Operand.mem (Operand.read s (Operand.reg 4#5) + 18446744073709551592#64),
                val := Operand.read s (Operand.reg 14#5) },
              { n := 64, dst := Operand.mem (Operand.read s (Operand.reg 4#5) + 18446744073709551584#64),
                val := Operand.read s (Operand.reg 13#5) },
              { n := 64, dst := Operand.mem (Operand.read s (Operand.reg 4#5) + 18446744073709551576#64),
                val := Operand.read s (Operand.reg 12#5) },
              { n := 64, dst := Operand.mem (Operand.read s (Operand.reg 4#5) + 18446744073709551568#64),
                val := Operand.read s (Operand.reg 3#5) },
              { n := 64, dst := Operand.reg 4#5,
                val := Operand.read s (Operand.reg 4#5) + 18446744073709551568#64 - 392#64 }],
          flags := some undefinedFlags }

def bytesA : List UInt8 :=
  [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53, 0x48, 0x81, 0xec, 0x88, 0x01, 0x00, 0x00]

set_option maxHeartbeats 4000000 in
theorem chunkA [Bindings] (boundary : ReturnBoundary) (hb : Away boundary) :
    AdvancesBlock boundary (SegPre 0x100650 0x1c0 8) (codeRange 0x100650 bytesA) effA := by
  unfold bytesA
  seg_begin (show StepEffect _ _ (pushR64Effect 0x100650 1 5) from push_r64_effect_step 0x100650 0x55 (by decide))
  seg_then 1 (show StepEffect _ _ (pushR64Effect 0x100651 2 15) from push_r64_rex_effect_step 0x100651 0x41 0x57 (by unfold RexPrefix; decide) (by decide))
  seg_then 3 (show StepEffect _ _ (pushR64Effect 0x100653 2 14) from push_r64_rex_effect_step 0x100653 0x41 0x56 (by unfold RexPrefix; decide) (by decide))
  seg_then 5 (show StepEffect _ _ (pushR64Effect 0x100655 2 13) from push_r64_rex_effect_step 0x100655 0x41 0x55 (by unfold RexPrefix; decide) (by decide))
  seg_then 7 (show StepEffect _ _ (pushR64Effect 0x100657 2 12) from push_r64_rex_effect_step 0x100657 0x41 0x54 (by unfold RexPrefix; decide) (by decide))
  seg_then 9 (show StepEffect _ _ (pushR64Effect 0x100659 1 3) from push_r64_effect_step 0x100659 0x53 (by decide))
  seg_then 10 (show StepEffect _ _ (subR64Imm32Effect 0x10065a 4 0x188) from sub_r64_imm32_effect_step 0x10065a 0x48 0xec 0x188 (by unfold RexWPrefix; decide) (by decide) (by decide))
  unfold effA
  seg_finish

def effB (s : RamState) : Effect :=
  { rip := 1050221#64,
          writes :=
            [{ n := 64, dst := Operand.reg 12#5, val := Operand.read s (Operand.reg 9#5) },
              { n := 64, dst := Operand.reg 13#5, val := Operand.read s (Operand.reg 8#5) },
              { n := 64, dst := Operand.reg 5#5, val := Operand.read s (Operand.reg 1#5) },
              { n := 64, dst := Operand.reg 14#5, val := Operand.read s (Operand.reg 7#5) }] }

def bytesB : List UInt8 :=
  [0x4d, 0x89, 0xcc, 0x4d, 0x89, 0xc5, 0x48, 0x89, 0xcd, 0x49, 0x89, 0xfe]

set_option maxHeartbeats 4000000 in
theorem chunkB [Bindings] (boundary : ReturnBoundary) (hb : Away boundary) :
    AdvancesBlock boundary (SegPre 0x100661 8 0x1c0) (codeRange 0x100661 bytesB) effB := by
  unfold bytesB
  seg_begin (show StepEffect _ _ (movR64R64Effect 0x100661 12 9) from mov_r64_r64_effect_step 0x100661 0x4d 0xcc (by unfold RexWPrefix; decide) (by decide))
  seg_then 3 (show StepEffect _ _ (movR64R64Effect 0x100664 13 8) from mov_r64_r64_effect_step 0x100664 0x4d 0xc5 (by unfold RexWPrefix; decide) (by decide))
  seg_then 6 (show StepEffect _ _ (movR64R64Effect 0x100667 5 1) from mov_r64_r64_effect_step 0x100667 0x48 0xcd (by unfold RexWPrefix; decide) (by decide))
  seg_then 9 (show StepEffect _ _ (movR64R64Effect 0x10066a 14 7) from mov_r64_r64_effect_step 0x10066a 0x49 0xfe (by unfold RexWPrefix; decide) (by decide))
  seg_close

def effC (s : RamState) : Effect :=
  { rip := 1050264#64,
          writes :=
            [{ n := 64, dst := Operand.mem (Operand.read s (Operand.reg 4#5) + 216#64), val := 7719281312240119090#64 },
              { n := 64, dst := Operand.mem (Operand.read s (Operand.reg 4#5) + 208#64), val := 3684054920433006693#64 },
              { n := 64, dst := Operand.reg 0#5,
                val := Operand.read s (Operand.mem (Operand.read s (Operand.reg 6#5) + 0#64) : Operand 64) },
              { n := 64, dst := Operand.reg 1#5,
                val := Operand.read s (Operand.mem (Operand.read s (Operand.reg 6#5) + 8#64) : Operand 64) }] }

def bytesC : List UInt8 :=
  [0x48, 0xb8, 0x32, 0x2d, 0x62, 0x79, 0x74, 0x65, 0x20, 0x6b, 0x48, 0x89, 0x84, 0x24, 0xd8, 0x00, 0x00, 0x00, 0x48, 0xb8, 0x65, 0x78, 0x70, 0x61, 0x6e, 0x64, 0x20, 0x33, 0x48, 0x89, 0x84, 0x24, 0xd0, 0x00, 0x00, 0x00, 0x48, 0x8b, 0x06, 0x48, 0x8b, 0x4e, 0x08]

set_option maxHeartbeats 4000000 in
theorem chunkC [Bindings] (boundary : ReturnBoundary) (hb : Away boundary) :
    AdvancesBlock boundary (SegPre 0x10066d 8 0x1c0) (codeRange 0x10066d bytesC) effC := by
  unfold bytesC
  seg_begin (show StepEffect _ _ (movR64Imm64Effect 0x10066d 0 0x6b20657479622d32) from mov_r64_imm64_effect_step 0x10066d 0x48 0xb8 (by unfold RexWPrefix; decide) (by decide) 0x6b20657479622d32)
  seg_then 10 (show StepEffect _ _ (movM64R64Effect 0x100677 0 (.sib 4 none 0 (.d32 0xd8))) from mov_m64_r64_effect_step 0x100677 0x48 (by unfold RexWPrefix; decide) 0 (.sib 4 none 0 (.d32 0xd8)) (by decide) (by decide) (by decide))
  seg_then 18 (show StepEffect _ _ (movR64Imm64Effect 0x10067f 0 0x3320646e61707865) from mov_r64_imm64_effect_step 0x10067f 0x48 0xb8 (by unfold RexWPrefix; decide) (by decide) 0x3320646e61707865)
  seg_then 28 (show StepEffect _ _ (movM64R64Effect 0x100689 0 (.sib 4 none 0 (.d32 0xd0))) from mov_m64_r64_effect_step 0x100689 0x48 (by unfold RexWPrefix; decide) 0 (.sib 4 none 0 (.d32 0xd0)) (by decide) (by decide) (by decide))
  seg_then 36 (show StepEffect _ _ (movR64M64Effect 0x100691 0 (.base 6 .none)) from mov_r64_m64_effect_step 0x100691 0x48 (by unfold RexWPrefix; decide) 0 (.base 6 .none) (by decide) (by decide) (by decide))
  seg_then 39 (show StepEffect _ _ (movR64M64Effect 0x100694 1 (.base 6 (.d8 0x8))) from mov_r64_m64_effect_step 0x100694 0x48 (by unfold RexWPrefix; decide) 1 (.base 6 (.d8 0x8)) (by decide) (by decide) (by decide))
  seg_close_data

def effD (s : RamState) : Effect :=
  { rip := 1050304#64,
          writes :=
            [{ n := 64, dst := Operand.mem (Operand.read s (Operand.reg 4#5) + 224#64),
                val := Operand.read s (Operand.reg 0#5) },
              { n := 64, dst := Operand.mem (Operand.read s (Operand.reg 4#5) + 232#64),
                val := Operand.read s (Operand.reg 1#5) },
              { n := 64, dst := Operand.mem (Operand.read s (Operand.reg 4#5) + 240#64),
                val := Operand.read s (Operand.mem (Operand.read s (Operand.reg 6#5) + 16#64) : Operand 64) },
              { n := 64, dst := Operand.reg 0#5,
                val := Operand.read s (Operand.mem (Operand.read s (Operand.reg 6#5) + 24#64) : Operand 64) },
              { n := 64, dst := Operand.mem (Operand.read s (Operand.reg 4#5) + 248#64),
                val := Operand.read s (Operand.mem (Operand.read s (Operand.reg 6#5) + 24#64) : Operand 64) }] }

def bytesD : List UInt8 :=
  [0x48, 0x89, 0x84, 0x24, 0xe0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x8c, 0x24, 0xe8, 0x00, 0x00, 0x00, 0x48, 0x8b, 0x46, 0x10, 0x48, 0x89, 0x84, 0x24, 0xf0, 0x00, 0x00, 0x00, 0x48, 0x8b, 0x46, 0x18, 0x48, 0x89, 0x84, 0x24, 0xf8, 0x00, 0x00, 0x00]

set_option maxHeartbeats 4000000 in
theorem chunkD [Bindings] (boundary : ReturnBoundary) (hb : Away boundary) :
    AdvancesBlock boundary (SegPre 0x100698 8 0x1c0) (codeRange 0x100698 bytesD) effD := by
  unfold bytesD
  seg_begin (show StepEffect _ _ (movM64R64Effect 0x100698 0 (.sib 4 none 0 (.d32 0xe0))) from mov_m64_r64_effect_step 0x100698 0x48 (by unfold RexWPrefix; decide) 0 (.sib 4 none 0 (.d32 0xe0)) (by decide) (by decide) (by decide))
  seg_then 8 (show StepEffect _ _ (movM64R64Effect 0x1006a0 1 (.sib 4 none 0 (.d32 0xe8))) from mov_m64_r64_effect_step 0x1006a0 0x48 (by unfold RexWPrefix; decide) 1 (.sib 4 none 0 (.d32 0xe8)) (by decide) (by decide) (by decide))
  seg_then 16 (show StepEffect _ _ (movR64M64Effect 0x1006a8 0 (.base 6 (.d8 0x10))) from mov_r64_m64_effect_step 0x1006a8 0x48 (by unfold RexWPrefix; decide) 0 (.base 6 (.d8 0x10)) (by decide) (by decide) (by decide))
  seg_then 20 (show StepEffect _ _ (movM64R64Effect 0x1006ac 0 (.sib 4 none 0 (.d32 0xf0))) from mov_m64_r64_effect_step 0x1006ac 0x48 (by unfold RexWPrefix; decide) 0 (.sib 4 none 0 (.d32 0xf0)) (by decide) (by decide) (by decide))
  seg_then 28 (show StepEffect _ _ (movR64M64Effect 0x1006b4 0 (.base 6 (.d8 0x18))) from mov_r64_m64_effect_step 0x1006b4 0x48 (by unfold RexWPrefix; decide) 0 (.base 6 (.d8 0x18)) (by decide) (by decide) (by decide))
  seg_then 32 (show StepEffect _ _ (movM64R64Effect 0x1006b8 0 (.sib 4 none 0 (.d32 0xf8))) from mov_m64_r64_effect_step 0x1006b8 0x48 (by unfold RexWPrefix; decide) 0 (.sib 4 none 0 (.d32 0xf8)) (by decide) (by decide) (by decide))
  seg_close_data

def effE (s : RamState) : Effect :=
  { rip := 1050319#64,
          writes :=
            [{ n := 64, dst := Operand.mem (Operand.read s (Operand.reg 4#5) + 76#64),
                val := Operand.read s (Operand.mem (Operand.read s (Operand.reg 2#5) + 0#64)) },
              { n := 64, dst := Operand.reg 0#5,
                val := BitVec.setWidth 64 (Operand.read s (Operand.mem (Operand.read s (Operand.reg 2#5) + 8#64) : Operand 32)) },
              { n := 32, dst := Operand.mem (Operand.read s (Operand.reg 4#5) + 84#64),
                val :=
                  BitVec.setWidth 32
                    (BitVec.setWidth 64 (Operand.read s (Operand.mem (Operand.read s (Operand.reg 2#5) + 8#64) : Operand 32))) }] }

def bytesE : List UInt8 :=
  [0x48, 0x8b, 0x02, 0x48, 0x89, 0x44, 0x24, 0x4c, 0x8b, 0x42, 0x08, 0x89, 0x44, 0x24, 0x54]

set_option maxHeartbeats 4000000 in
theorem chunkE [Bindings] (boundary : ReturnBoundary) (hb : Away boundary) :
    AdvancesBlock boundary (SegPre 0x1006c0 8 0x1c0) (codeRange 0x1006c0 bytesE) effE := by
  unfold bytesE
  seg_begin (show StepEffect _ _ (movR64M64Effect 0x1006c0 0 (.base 2 .none)) from mov_r64_m64_effect_step 0x1006c0 0x48 (by unfold RexWPrefix; decide) 0 (.base 2 .none) (by decide) (by decide) (by decide))
  seg_then 3 (show StepEffect _ _ (movM64R64Effect 0x1006c3 0 (.sib 4 none 0 (.d8 0x4c))) from mov_m64_r64_effect_step 0x1006c3 0x48 (by unfold RexWPrefix; decide) 0 (.sib 4 none 0 (.d8 0x4c)) (by decide) (by decide) (by decide))
  seg_then 8 (show StepEffect _ _ (movR32M32LowEffect 0x1006c8 0 (.base 2 (.d8 0x8))) from mov_r32_m32_low_effect_step 0x1006c8 0 (.base 2 (.d8 0x8)) (by decide) (by decide) (by decide))
  seg_then 11 (show StepEffect _ _ (movM32R32LowEffect 0x1006cb 0 (.sib 4 none 0 (.d8 0x54))) from mov_m32_r32_low_effect_step 0x1006cb 0 (.sib 4 none 0 (.d8 0x54)) (by decide) (by decide) (by decide))
  seg_close_data

def effF (s : RamState) : Effect :=
  { rip := 1050388#64,
        writes :=
          [{ n := 64, dst := Operand.mem (Operand.read s (Operand.reg 4#5) + 89#64), val := 0#64 },
            { n := 64, dst := Operand.mem (Operand.read s (Operand.reg 4#5) + 97#64), val := 0#64 },
            { n := 64, dst := Operand.mem (Operand.read s (Operand.reg 4#5) + 105#64), val := 0#64 },
            { n := 64, dst := Operand.mem (Operand.read s (Operand.reg 4#5) + 113#64), val := 0#64 },
            { n := 64, dst := Operand.mem (Operand.read s (Operand.reg 4#5) + 121#64), val := 0#64 },
            { n := 64, dst := Operand.mem (Operand.read s (Operand.reg 4#5) + 129#64), val := 0#64 },
            { n := 64, dst := Operand.mem (Operand.read s (Operand.reg 4#5) + 137#64), val := 0#64 }] }

def bytesF : List UInt8 :=
  [0x48, 0xc7, 0x44, 0x24, 0x59, 0x00, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x44, 0x24, 0x61, 0x00, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x44, 0x24, 0x69, 0x00, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x44, 0x24, 0x71, 0x00, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x44, 0x24, 0x79, 0x00, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x84, 0x24, 0x81, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x84, 0x24, 0x89, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]

set_option maxHeartbeats 4000000 in
theorem chunkF [Bindings] (boundary : ReturnBoundary) (hb : Away boundary) :
    AdvancesBlock boundary (SegPre 0x1006cf 8 0x1c0) (codeRange 0x1006cf bytesF) effF := by
  unfold bytesF
  seg_begin (show StepEffect _ _ (movM64Imm32Effect 0x1006cf (.sib 4 none 0 (.d8 0x59)) 0x0) from mov_m64_imm32_effect_step 0x1006cf 0x48 (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d8 0x59)) (by decide) (by decide) (by decide) 0x0)
  seg_then 9 (show StepEffect _ _ (movM64Imm32Effect 0x1006d8 (.sib 4 none 0 (.d8 0x61)) 0x0) from mov_m64_imm32_effect_step 0x1006d8 0x48 (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d8 0x61)) (by decide) (by decide) (by decide) 0x0)
  seg_then 18 (show StepEffect _ _ (movM64Imm32Effect 0x1006e1 (.sib 4 none 0 (.d8 0x69)) 0x0) from mov_m64_imm32_effect_step 0x1006e1 0x48 (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d8 0x69)) (by decide) (by decide) (by decide) 0x0)
  seg_then 27 (show StepEffect _ _ (movM64Imm32Effect 0x1006ea (.sib 4 none 0 (.d8 0x71)) 0x0) from mov_m64_imm32_effect_step 0x1006ea 0x48 (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d8 0x71)) (by decide) (by decide) (by decide) 0x0)
  seg_then 36 (show StepEffect _ _ (movM64Imm32Effect 0x1006f3 (.sib 4 none 0 (.d8 0x79)) 0x0) from mov_m64_imm32_effect_step 0x1006f3 0x48 (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d8 0x79)) (by decide) (by decide) (by decide) 0x0)
  seg_then 45 (show StepEffect _ _ (movM64Imm32Effect 0x1006fc (.sib 4 none 0 (.d32 0x81)) 0x0) from mov_m64_imm32_effect_step 0x1006fc 0x48 (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d32 0x81)) (by decide) (by decide) (by decide) 0x0)
  seg_then 57 (show StepEffect _ _ (movM64Imm32Effect 0x100708 (.sib 4 none 0 (.d32 0x89)) 0x0) from mov_m64_imm32_effect_step 0x100708 0x48 (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d32 0x89)) (by decide) (by decide) (by decide) 0x0)
  seg_close

def effJ (s : RamState) : Effect :=
  { rip := 1050400#64,
        writes := [{ n := 64, dst := Operand.mem (Operand.read s (Operand.reg 4#5) + 144#64), val := 0#64 }] }

def bytesJ : List UInt8 :=
  [0x48, 0xc7, 0x84, 0x24, 0x90, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]

set_option maxHeartbeats 4000000 in
theorem chunkJ [Bindings] (boundary : ReturnBoundary) (hb : Away boundary) :
    AdvancesBlock boundary (SegPre 0x100714 8 0x1c0) (codeRange 0x100714 bytesJ) effJ := by
  unfold bytesJ
  seg_begin (show StepEffect _ _ (movM64Imm32Effect 0x100714 (.sib 4 none 0 (.d32 0x90)) 0x0) from mov_m64_imm32_effect_step 0x100714 0x48 (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d32 0x90)) (by decide) (by decide) (by decide) 0x0)
  seg_close

def effG (s : RamState) : Effect :=
  { rip := 1050478#64,
          writes :=
            [{ n := 64, dst := Operand.mem (Operand.read s (Operand.reg 4#5) + 64#64),
                val := Operand.read s (Operand.mem (Operand.read s (Operand.reg 4#5) + 248#64)) },
              { n := 64, dst := Operand.mem (Operand.read s (Operand.reg 4#5) + 56#64),
                val := Operand.read s (Operand.mem (Operand.read s (Operand.reg 4#5) + 240#64)) },
              { n := 64, dst := Operand.mem (Operand.read s (Operand.reg 4#5) + 48#64),
                val := Operand.read s (Operand.mem (Operand.read s (Operand.reg 4#5) + 232#64)) },
              { n := 64, dst := Operand.mem (Operand.read s (Operand.reg 4#5) + 40#64),
                val := Operand.read s (Operand.mem (Operand.read s (Operand.reg 4#5) + 224#64)) },
              { n := 64, dst := Operand.reg 0#5,
                val := Operand.read s (Operand.mem (Operand.read s (Operand.reg 4#5) + 208#64)) },
              { n := 64, dst := Operand.reg 1#5,
                val := Operand.read s (Operand.mem (Operand.read s (Operand.reg 4#5) + 216#64)) },
              { n := 64, dst := Operand.mem (Operand.read s (Operand.reg 4#5) + 32#64),
                val := Operand.read s (Operand.mem (Operand.read s (Operand.reg 4#5) + 216#64)) },
              { n := 64, dst := Operand.mem (Operand.read s (Operand.reg 4#5) + 24#64),
                val := Operand.read s (Operand.mem (Operand.read s (Operand.reg 4#5) + 208#64)) }] }

def bytesG : List UInt8 :=
  [0x48, 0x8b, 0x84, 0x24, 0xf8, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x40, 0x48, 0x8b, 0x84, 0x24, 0xf0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x38, 0x48, 0x8b, 0x84, 0x24, 0xe8, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x30, 0x48, 0x8b, 0x84, 0x24, 0xe0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x44, 0x24, 0x28, 0x48, 0x8b, 0x84, 0x24, 0xd0, 0x00, 0x00, 0x00, 0x48, 0x8b, 0x8c, 0x24, 0xd8, 0x00, 0x00, 0x00, 0x48, 0x89, 0x4c, 0x24, 0x20, 0x48, 0x89, 0x44, 0x24, 0x18]

set_option maxHeartbeats 4000000 in
theorem chunkG [Bindings] (boundary : ReturnBoundary) (hb : Away boundary) :
    AdvancesBlock boundary (SegPre 0x100720 8 0x1c0) (codeRange 0x100720 bytesG) effG := by
  unfold bytesG
  seg_begin (show StepEffect _ _ (movR64M64Effect 0x100720 0 (.sib 4 none 0 (.d32 0xf8))) from mov_r64_m64_effect_step 0x100720 0x48 (by unfold RexWPrefix; decide) 0 (.sib 4 none 0 (.d32 0xf8)) (by decide) (by decide) (by decide))
  seg_then 8 (show StepEffect _ _ (movM64R64Effect 0x100728 0 (.sib 4 none 0 (.d8 0x40))) from mov_m64_r64_effect_step 0x100728 0x48 (by unfold RexWPrefix; decide) 0 (.sib 4 none 0 (.d8 0x40)) (by decide) (by decide) (by decide))
  seg_then 13 (show StepEffect _ _ (movR64M64Effect 0x10072d 0 (.sib 4 none 0 (.d32 0xf0))) from mov_r64_m64_effect_step 0x10072d 0x48 (by unfold RexWPrefix; decide) 0 (.sib 4 none 0 (.d32 0xf0)) (by decide) (by decide) (by decide))
  seg_then 21 (show StepEffect _ _ (movM64R64Effect 0x100735 0 (.sib 4 none 0 (.d8 0x38))) from mov_m64_r64_effect_step 0x100735 0x48 (by unfold RexWPrefix; decide) 0 (.sib 4 none 0 (.d8 0x38)) (by decide) (by decide) (by decide))
  seg_then 26 (show StepEffect _ _ (movR64M64Effect 0x10073a 0 (.sib 4 none 0 (.d32 0xe8))) from mov_r64_m64_effect_step 0x10073a 0x48 (by unfold RexWPrefix; decide) 0 (.sib 4 none 0 (.d32 0xe8)) (by decide) (by decide) (by decide))
  seg_then 34 (show StepEffect _ _ (movM64R64Effect 0x100742 0 (.sib 4 none 0 (.d8 0x30))) from mov_m64_r64_effect_step 0x100742 0x48 (by unfold RexWPrefix; decide) 0 (.sib 4 none 0 (.d8 0x30)) (by decide) (by decide) (by decide))
  seg_then 39 (show StepEffect _ _ (movR64M64Effect 0x100747 0 (.sib 4 none 0 (.d32 0xe0))) from mov_r64_m64_effect_step 0x100747 0x48 (by unfold RexWPrefix; decide) 0 (.sib 4 none 0 (.d32 0xe0)) (by decide) (by decide) (by decide))
  seg_then 47 (show StepEffect _ _ (movM64R64Effect 0x10074f 0 (.sib 4 none 0 (.d8 0x28))) from mov_m64_r64_effect_step 0x10074f 0x48 (by unfold RexWPrefix; decide) 0 (.sib 4 none 0 (.d8 0x28)) (by decide) (by decide) (by decide))
  seg_then 52 (show StepEffect _ _ (movR64M64Effect 0x100754 0 (.sib 4 none 0 (.d32 0xd0))) from mov_r64_m64_effect_step 0x100754 0x48 (by unfold RexWPrefix; decide) 0 (.sib 4 none 0 (.d32 0xd0)) (by decide) (by decide) (by decide))
  seg_then 60 (show StepEffect _ _ (movR64M64Effect 0x10075c 1 (.sib 4 none 0 (.d32 0xd8))) from mov_r64_m64_effect_step 0x10075c 0x48 (by unfold RexWPrefix; decide) 1 (.sib 4 none 0 (.d32 0xd8)) (by decide) (by decide) (by decide))
  seg_then 68 (show StepEffect _ _ (movM64R64Effect 0x100764 1 (.sib 4 none 0 (.d8 0x20))) from mov_m64_r64_effect_step 0x100764 0x48 (by unfold RexWPrefix; decide) 1 (.sib 4 none 0 (.d8 0x20)) (by decide) (by decide) (by decide))
  seg_then 73 (show StepEffect _ _ (movM64R64Effect 0x100769 0 (.sib 4 none 0 (.d8 0x18))) from mov_m64_r64_effect_step 0x100769 0x48 (by unfold RexWPrefix; decide) 0 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide))
  seg_close

def effH (s : RamState) : Effect :=
  { rip := 1050539#64,
          writes :=
            [{ n := 32, dst := Operand.mem (Operand.read s (Operand.reg 4#5) + 72#64), val := 0#32 },
              { n := 8, dst := Operand.mem (Operand.read s (Operand.reg 4#5) + 88#64), val := 64#8 },
              { n := 64, dst := Operand.mem (Operand.read s (Operand.reg 4#5) + 200#64), val := 0#64 },
              { n := 64, dst := Operand.mem (Operand.read s (Operand.reg 4#5) + 192#64), val := 0#64 },
              { n := 64, dst := Operand.mem (Operand.read s (Operand.reg 4#5) + 184#64), val := 0#64 },
              { n := 64, dst := Operand.mem (Operand.read s (Operand.reg 4#5) + 176#64), val := 0#64 }] }

def bytesH : List UInt8 :=
  [0xc7, 0x44, 0x24, 0x48, 0x00, 0x00, 0x00, 0x00, 0xc6, 0x44, 0x24, 0x58, 0x40, 0x48, 0xc7, 0x84, 0x24, 0xc8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x84, 0x24, 0xc0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x84, 0x24, 0xb8, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x84, 0x24, 0xb0, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]

set_option maxHeartbeats 4000000 in
theorem chunkH [Bindings] (boundary : ReturnBoundary) (hb : Away boundary) :
    AdvancesBlock boundary (SegPre 0x10076e 8 0x1c0) (codeRange 0x10076e bytesH) effH := by
  unfold bytesH
  seg_begin (show StepEffect _ _ (movM32Imm32Effect 0x10076e 8 (.sib 4 none 0 (.d8 0x48)) 0x0) from mov_m32_imm32_effect_step 0x10076e (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide) (by decide) 0x0)
  seg_then 8 (show StepEffect _ _ (movM8Imm8Effect 0x100776 (.sib 4 none 0 (.d8 0x58)) 0x40) from mov_m8_imm8_effect_step 0x100776 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide) (by decide) 0x40)
  seg_then 13 (show StepEffect _ _ (movM64Imm32Effect 0x10077b (.sib 4 none 0 (.d32 0xc8)) 0x0) from mov_m64_imm32_effect_step 0x10077b 0x48 (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d32 0xc8)) (by decide) (by decide) (by decide) 0x0)
  seg_then 25 (show StepEffect _ _ (movM64Imm32Effect 0x100787 (.sib 4 none 0 (.d32 0xc0)) 0x0) from mov_m64_imm32_effect_step 0x100787 0x48 (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d32 0xc0)) (by decide) (by decide) (by decide) 0x0)
  seg_then 37 (show StepEffect _ _ (movM64Imm32Effect 0x100793 (.sib 4 none 0 (.d32 0xb8)) 0x0) from mov_m64_imm32_effect_step 0x100793 0x48 (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d32 0xb8)) (by decide) (by decide) (by decide) 0x0)
  seg_then 49 (show StepEffect _ _ (movM64Imm32Effect 0x10079f (.sib 4 none 0 (.d32 0xb0)) 0x0) from mov_m64_imm32_effect_step 0x10079f 0x48 (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide) 0x0)
  seg_close

def effI (s : RamState) : Effect :=
  { rip := 1050588#64,
          writes :=
            [{ n := 64, dst := Operand.reg 0#5, val := Operand.read s (Operand.reg 4#5) + 176#64 },
              { n := 64, dst := Operand.mem (Operand.read s (Operand.reg 4#5) + 208#64),
                val := Operand.read s (Operand.reg 4#5) + 176#64 },
              { n := 64, dst := Operand.mem (Operand.read s (Operand.reg 4#5) + 216#64),
                val := Operand.read s (Operand.reg 4#5) + 176#64 },
              { n := 64, dst := Operand.mem (Operand.read s (Operand.reg 4#5) + 224#64), val := 32#64 },
              { n := 64, dst := Operand.reg 7#5, val := Operand.read s (Operand.reg 4#5) + 24#64 },
              { n := 64, dst := Operand.reg 6#5, val := Operand.read s (Operand.reg 4#5) + 208#64 }] }

def bytesI : List UInt8 :=
  [0x48, 0x8d, 0x84, 0x24, 0xb0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0xd0, 0x00, 0x00, 0x00, 0x48, 0x89, 0x84, 0x24, 0xd8, 0x00, 0x00, 0x00, 0x48, 0xc7, 0x84, 0x24, 0xe0, 0x00, 0x00, 0x00, 0x20, 0x00, 0x00, 0x00, 0x48, 0x8d, 0x7c, 0x24, 0x18, 0x48, 0x8d, 0xb4, 0x24, 0xd0, 0x00, 0x00, 0x00]

set_option maxHeartbeats 4000000 in
theorem chunkI [Bindings] (boundary : ReturnBoundary) (hb : Away boundary) :
    AdvancesBlock boundary (SegPre 0x1007ab 8 0x1c0) (codeRange 0x1007ab bytesI) effI := by
  unfold bytesI
  seg_begin (show StepEffect _ _ (leaR64Effect 0x1007ab 0 (.sib 4 none 0 (.d32 0xb0))) from lea_r64_effect_step 0x1007ab 0x48 (by unfold RexWPrefix; decide) 0 (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide))
  seg_then 8 (show StepEffect _ _ (movM64R64Effect 0x1007b3 0 (.sib 4 none 0 (.d32 0xd0))) from mov_m64_r64_effect_step 0x1007b3 0x48 (by unfold RexWPrefix; decide) 0 (.sib 4 none 0 (.d32 0xd0)) (by decide) (by decide) (by decide))
  seg_then 16 (show StepEffect _ _ (movM64R64Effect 0x1007bb 0 (.sib 4 none 0 (.d32 0xd8))) from mov_m64_r64_effect_step 0x1007bb 0x48 (by unfold RexWPrefix; decide) 0 (.sib 4 none 0 (.d32 0xd8)) (by decide) (by decide) (by decide))
  seg_then 24 (show StepEffect _ _ (movM64Imm32Effect 0x1007c3 (.sib 4 none 0 (.d32 0xe0)) 0x20) from mov_m64_imm32_effect_step 0x1007c3 0x48 (by unfold RexWPrefix; decide) (.sib 4 none 0 (.d32 0xe0)) (by decide) (by decide) (by decide) 0x20)
  seg_then 36 (show StepEffect _ _ (leaR64Effect 0x1007cf 7 (.sib 4 none 0 (.d8 0x18))) from lea_r64_effect_step 0x1007cf 0x48 (by unfold RexWPrefix; decide) 7 (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide))
  seg_then 41 (show StepEffect _ _ (leaR64Effect 0x1007d4 6 (.sib 4 none 0 (.d32 0xd0))) from lea_r64_effect_step 0x1007d4 0x48 (by unfold RexWPrefix; decide) 6 (.sib 4 none 0 (.d32 0xd0)) (by decide) (by decide) (by decide))
  seg_close

def effK (s : RamState) : Effect :=
  { rip := 1051264#64,
        writes :=
          [{ n := 64, dst := Operand.reg 4#5, val := Operand.read s (Operand.reg 4#5) + 18446744073709551608#64 },
            { n := 64, dst := Operand.mem (Operand.read s (Operand.reg 4#5) + 18446744073709551608#64),
              val := 1050593#64 }] }

def bytesK : List UInt8 := [0xe8, 0x9f, 0x02, 0x00, 0x00]

set_option maxHeartbeats 4000000 in
theorem chunkK [Bindings] (boundary : ReturnBoundary) (hb : Away boundary) :
    AdvancesBlock boundary (StackPre 0x1007dc 8 0x1c0) (codeRange 0x1007dc bytesK) effK := by
  unfold bytesK
  seg_begin (show StepEffect _ _ (callEffect (fun _ => branchTarget 0x1007dc 5 ((0x29f : BitVec 32).signExtend 64)) (0x1007dc + BitVec.ofNat 64 5)) from call_rel32_effect_step 0x1007dc 0x29f (by decide))
  seg_close

theorem effB_local : Effect.Local effB := by effect_local [effB]

theorem effC_local : Effect.Local effC := by effect_local [effC]

theorem effD_local : Effect.Local effD := by effect_local [effD]

theorem effE_local : Effect.Local effE := by effect_local [effE]

theorem effG_local : Effect.Local effG := by effect_local [effG]

theorem effH_local : Effect.Local effH := by effect_local [effH]

theorem effI_local : Effect.Local effI := by effect_local [effI]

theorem effF_local : Effect.Local effF := by effect_local [effF]

theorem effJ_local : Effect.Local effJ := by effect_local [effJ]

theorem effK_local : Effect.Local effK := by effect_local [effK]

set_option linter.unusedSimpArgs false in
theorem effA_avoids (t : RamState) (h : Frame 0x1c0 8 t) :
    (effA t).Avoids Extracted.programImage := by
  apply avoids_program
  intro c hc a hcov
  simp only [effA, Effect.components, List.map_cons, List.map_nil, Write.component_reg,
    Write.component_mem, List.cons_append, List.nil_append, List.append_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact h.slot_outside _ (by decide +kernel) _ hcov
    | simp [Component.Covers] at hcov

theorem chunkA_program [Bindings] (boundary : ReturnBoundary) (hb : Away boundary) :
    AdvancesBlock boundary (SegPre 0x100650 0x1c0 8) Extracted.programImage effA :=
  widenBlock (chunkA boundary hb)
    (fun _ hc => slice_code hc 0x650 17 (by decide +kernel) (by decide) (by decide +kernel))
    (fun t h => effA_avoids t h.frame)

set_option linter.unusedSimpArgs false in
theorem effB_avoids (t : RamState) (_h : Frame 8 0x1c0 t) :
    (effB t).Avoids Extracted.programImage := by
  apply avoids_program
  intro c hc a hcov
  simp only [effB, Effect.components, List.map_cons, List.map_nil, Write.component_reg,
    Write.component_mem, List.cons_append, List.nil_append, List.append_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact h.slot_outside _ (by decide +kernel) _ hcov
    | simp [Component.Covers] at hcov

theorem chunkB_program [Bindings] (boundary : ReturnBoundary) (hb : Away boundary) :
    AdvancesBlock boundary (SegPre 0x100661 8 0x1c0) Extracted.programImage effB :=
  widenBlock (chunkB boundary hb)
    (fun _ hc => slice_code hc 0x661 12 (by decide +kernel) (by decide) (by decide +kernel))
    (fun t h => effB_avoids t h.frame)

set_option linter.unusedSimpArgs false in
theorem effC_avoids (t : RamState) (h : Frame 8 0x1c0 t) :
    (effC t).Avoids Extracted.programImage := by
  apply avoids_program
  intro c hc a hcov
  simp only [effC, Effect.components, List.map_cons, List.map_nil, Write.component_reg,
    Write.component_mem, List.cons_append, List.nil_append, List.append_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact h.slot_outside _ (by decide +kernel) _ hcov
    | simp [Component.Covers] at hcov

theorem chunkC_program [Bindings] (boundary : ReturnBoundary) (hb : Away boundary) :
    AdvancesBlock boundary (SegPre 0x10066d 8 0x1c0) Extracted.programImage effC :=
  widenBlock (chunkC boundary hb)
    (fun _ hc => slice_code hc 0x66d 43 (by decide +kernel) (by decide) (by decide +kernel))
    (fun t h => effC_avoids t h.frame)

set_option linter.unusedSimpArgs false in
theorem effD_avoids (t : RamState) (h : Frame 8 0x1c0 t) :
    (effD t).Avoids Extracted.programImage := by
  apply avoids_program
  intro c hc a hcov
  simp only [effD, Effect.components, List.map_cons, List.map_nil, Write.component_reg,
    Write.component_mem, List.cons_append, List.nil_append, List.append_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact h.slot_outside _ (by decide +kernel) _ hcov
    | simp [Component.Covers] at hcov

theorem chunkD_program [Bindings] (boundary : ReturnBoundary) (hb : Away boundary) :
    AdvancesBlock boundary (SegPre 0x100698 8 0x1c0) Extracted.programImage effD :=
  widenBlock (chunkD boundary hb)
    (fun _ hc => slice_code hc 0x698 40 (by decide +kernel) (by decide) (by decide +kernel))
    (fun t h => effD_avoids t h.frame)

set_option linter.unusedSimpArgs false in
theorem effE_avoids (t : RamState) (h : Frame 8 0x1c0 t) :
    (effE t).Avoids Extracted.programImage := by
  apply avoids_program
  intro c hc a hcov
  simp only [effE, Effect.components, List.map_cons, List.map_nil, Write.component_reg,
    Write.component_mem, List.cons_append, List.nil_append, List.append_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  all_goals first
    | exact h.slot_outside _ (by decide +kernel) _ hcov
    | simp [Component.Covers] at hcov

theorem chunkE_program [Bindings] (boundary : ReturnBoundary) (hb : Away boundary) :
    AdvancesBlock boundary (SegPre 0x1006c0 8 0x1c0) Extracted.programImage effE :=
  widenBlock (chunkE boundary hb)
    (fun _ hc => slice_code hc 0x6c0 15 (by decide +kernel) (by decide) (by decide +kernel))
    (fun t h => effE_avoids t h.frame)

set_option linter.unusedSimpArgs false in
theorem effF_avoids (t : RamState) (h : Frame 8 0x1c0 t) :
    (effF t).Avoids Extracted.programImage := by
  apply avoids_program
  intro c hc a hcov
  simp only [effF, Effect.components, List.map_cons, List.map_nil, Write.component_reg,
    Write.component_mem, List.cons_append, List.nil_append, List.append_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact h.slot_outside _ (by decide +kernel) _ hcov
    | simp [Component.Covers] at hcov

theorem chunkF_program [Bindings] (boundary : ReturnBoundary) (hb : Away boundary) :
    AdvancesBlock boundary (SegPre 0x1006cf 8 0x1c0) Extracted.programImage effF :=
  widenBlock (chunkF boundary hb)
    (fun _ hc => slice_code hc 0x6cf 69 (by decide +kernel) (by decide) (by decide +kernel))
    (fun t h => effF_avoids t h.frame)

set_option linter.unusedSimpArgs false in
theorem effJ_avoids (t : RamState) (h : Frame 8 0x1c0 t) :
    (effJ t).Avoids Extracted.programImage := by
  apply avoids_program
  intro c hc a hcov
  simp only [effJ, Effect.components, List.map_cons, List.map_nil, Write.component_reg,
    Write.component_mem, List.cons_append, List.nil_append, List.append_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  all_goals first
    | exact h.slot_outside _ (by decide +kernel) _ hcov
    | simp [Component.Covers] at hcov

theorem chunkJ_program [Bindings] (boundary : ReturnBoundary) (hb : Away boundary) :
    AdvancesBlock boundary (SegPre 0x100714 8 0x1c0) Extracted.programImage effJ :=
  widenBlock (chunkJ boundary hb)
    (fun _ hc => slice_code hc 0x714 12 (by decide +kernel) (by decide) (by decide +kernel))
    (fun t h => effJ_avoids t h.frame)

set_option linter.unusedSimpArgs false in
theorem effG_avoids (t : RamState) (h : Frame 8 0x1c0 t) :
    (effG t).Avoids Extracted.programImage := by
  apply avoids_program
  intro c hc a hcov
  simp only [effG, Effect.components, List.map_cons, List.map_nil, Write.component_reg,
    Write.component_mem, List.cons_append, List.nil_append, List.append_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact h.slot_outside _ (by decide +kernel) _ hcov
    | simp [Component.Covers] at hcov

theorem chunkG_program [Bindings] (boundary : ReturnBoundary) (hb : Away boundary) :
    AdvancesBlock boundary (SegPre 0x100720 8 0x1c0) Extracted.programImage effG :=
  widenBlock (chunkG boundary hb)
    (fun _ hc => slice_code hc 0x720 78 (by decide +kernel) (by decide) (by decide +kernel))
    (fun t h => effG_avoids t h.frame)

set_option linter.unusedSimpArgs false in
theorem effH_avoids (t : RamState) (h : Frame 8 0x1c0 t) :
    (effH t).Avoids Extracted.programImage := by
  apply avoids_program
  intro c hc a hcov
  simp only [effH, Effect.components, List.map_cons, List.map_nil, Write.component_reg,
    Write.component_mem, List.cons_append, List.nil_append, List.append_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact h.slot_outside _ (by decide +kernel) _ hcov
    | simp [Component.Covers] at hcov

theorem chunkH_program [Bindings] (boundary : ReturnBoundary) (hb : Away boundary) :
    AdvancesBlock boundary (SegPre 0x10076e 8 0x1c0) Extracted.programImage effH :=
  widenBlock (chunkH boundary hb)
    (fun _ hc => slice_code hc 0x76e 61 (by decide +kernel) (by decide) (by decide +kernel))
    (fun t h => effH_avoids t h.frame)

set_option linter.unusedSimpArgs false in
theorem effI_avoids (t : RamState) (h : Frame 8 0x1c0 t) :
    (effI t).Avoids Extracted.programImage := by
  apply avoids_program
  intro c hc a hcov
  simp only [effI, Effect.components, List.map_cons, List.map_nil, Write.component_reg,
    Write.component_mem, List.cons_append, List.nil_append, List.append_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact h.slot_outside _ (by decide +kernel) _ hcov
    | simp [Component.Covers] at hcov

theorem chunkI_program [Bindings] (boundary : ReturnBoundary) (hb : Away boundary) :
    AdvancesBlock boundary (SegPre 0x1007ab 8 0x1c0) Extracted.programImage effI :=
  widenBlock (chunkI boundary hb)
    (fun _ hc => slice_code hc 0x7ab 49 (by decide +kernel) (by decide) (by decide +kernel))
    (fun t h => effI_avoids t h.frame)

set_option linter.unusedSimpArgs false in
theorem effK_avoids (t : RamState) (h : Frame 8 0x1c0 t) :
    (effK t).Avoids Extracted.programImage := by
  apply avoids_program
  intro c hc a hcov
  simp only [effK, Effect.components, List.map_cons, List.map_nil, Write.component_reg,
    Write.component_mem, List.cons_append, List.nil_append, List.append_nil, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  all_goals first
    | exact h.slot_outside _ (by decide +kernel) _ hcov
    | simp [Component.Covers] at hcov

theorem chunkK_program [Bindings] (boundary : ReturnBoundary) (hb : Away boundary) :
    AdvancesBlock boundary (StackPre 0x1007dc 8 0x1c0) Extracted.programImage effK :=
  widenBlock (chunkK boundary hb)
    (fun _ hc => slice_code hc 0x7dc 5 (by decide +kernel) (by decide) (by decide +kernel))
    (fun t h => effK_avoids t h.frame)

def effPre : RamState → Effect :=
  Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (Effect.seq (effA) effB) effC) effD) effE) effF) effJ) effG) effH) effI) effK

macro "seg_cnorm" : tactic => `(tactic|
  simp (config := { decide := true, maxSteps := 4000000 }) only [x86_compose, pushAddr_eq_read, effA, effB, effC, effD, effE, effF, effJ, effG, effH, effI, effK])

macro "seg_av" h:term : tactic => `(tactic| first
  | exact effB_avoids _ $h | exact effC_avoids _ $h | exact effD_avoids _ $h
  | exact effE_avoids _ $h | exact effF_avoids _ $h | exact effJ_avoids _ $h
  | exact effG_avoids _ $h | exact effH_avoids _ $h | exact effI_avoids _ $h
  | exact effK_avoids _ $h)

macro "seg_mid" : tactic => `(tactic| (
  intro s t hP hH hO
  have hg := hH.agrees.grow
  have hsp : rspOf t = rspOf s + 0xffffffffffffffd0 - 0x188 := by
    simp only [rspOf]; rw [← (hO true).read_reg]; seg_cnorm
  have hfr := hP.frame.prologue hsp hg
  first
    | (refine ⟨SegPre.prologue hP ?_ hsp ?_ ?_ hg, ?_⟩
       exact hH.rip_of (by seg_cnorm)
       (rw [← (hO true).read_reg]; seg_cnorm)
       (rw [← (hO true).read_reg]; seg_cnorm)
       seg_av hfr)
    | (refine ⟨StackPre.prologue hP ?_ hsp hg, ?_⟩
       exact hH.rip_of (by seg_cnorm)
       seg_av hfr)))

macro "seg_full_all" : tactic => `(tactic| (
  intro _ _
  simp (config := { decide := true, maxSteps := 4000000 }) only [x86_compose, pushAddr_eq_read, effA, effB, effC, effD, effE, effF, effJ, effG, effH, effI, effK,
    List.forall_mem_cons, List.forall_mem_nil, List.forall_mem_append, and_true, true_and]))

set_option maxHeartbeats 40000000 in
theorem prefix_block [Bindings] (boundary : ReturnBoundary) (hb : Away boundary) :
    AdvancesBlock boundary (SegPre 0x100650 0x1c0 8) Extracted.programImage effPre := by
  have h0 := chunkA_program boundary hb
  have h1 := AdvancesBlock.seq_block h0 (chunkB_program boundary hb) effB_local (fun _ h => h) (by seg_full_all) (by seg_mid)
  have h2 := AdvancesBlock.seq_block h1 (chunkC_program boundary hb) effC_local (fun _ h => h) (by seg_full_all) (by seg_mid)
  have h3 := AdvancesBlock.seq_block h2 (chunkD_program boundary hb) effD_local (fun _ h => h) (by seg_full_all) (by seg_mid)
  have h4 := AdvancesBlock.seq_block h3 (chunkE_program boundary hb) effE_local (fun _ h => h) (by seg_full_all) (by seg_mid)
  have h5 := AdvancesBlock.seq_block h4 (chunkF_program boundary hb) effF_local (fun _ h => h) (by seg_full_all) (by seg_mid)
  have h6 := AdvancesBlock.seq_block h5 (chunkJ_program boundary hb) effJ_local (fun _ h => h) (by seg_full_all) (by seg_mid)
  have h7 := AdvancesBlock.seq_block h6 (chunkG_program boundary hb) effG_local (fun _ h => h) (by seg_full_all) (by seg_mid)
  have h8 := AdvancesBlock.seq_block h7 (chunkH_program boundary hb) effH_local (fun _ h => h) (by seg_full_all) (by seg_mid)
  have h9 := AdvancesBlock.seq_block h8 (chunkI_program boundary hb) effI_local (fun _ h => h) (by seg_full_all) (by seg_mid)
  have h10 := AdvancesBlock.seq_block h9 (chunkK_program boundary hb) effK_local (fun _ h => h) (by seg_full_all) (by seg_mid)
  exact h10

end ChaCha20Poly1305.Proofs.Core.Setup

set_option maxRecDepth 100000

namespace ChaCha20Poly1305.Proofs.Core.Setup


open ChaCha20Poly1305.Spec.Program Standards.RFC.ChaCha20Poly1305 Prelude X86 X86.Machine
open X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CoreContract
open ChaCha20Poly1305.Proofs.MemoryRoutines.Machine

theorem away_of {boundary : ReturnBoundary} (h : ¬ InProgram boundary.rip) : Away boundary :=
  ⟨fun q h₁ h₂ he => h (he ▸ Encrypt.inProgram_of_toNat h₁ (by omega))⟩

theorem sep_of_overlap {a n b m : Nat}
    (h : ∀ x, a ≤ x → x < a + n → b ≤ x → x < b + m → False) :
    a + n ≤ b ∨ b + m ≤ a ∨ n = 0 ∨ m = 0 := by
  refine Classical.byContradiction fun hc => h (max a b) ?_ ?_ ?_ ?_ <;> omega

section Entry

variable [bindings : Machine.Bindings] {s : RamState} {key : Vector UInt8 32}
  {nonce : Vector UInt8 12} {associatedData plaintext : ByteArray} {inPtr outPtr : BitVec 64}

omit bindings in
theorem rspOf_eq (t : RamState) : rspOf t = stackPtr t := (stackPtr_eq_read t).symm

theorem frame_of_core (hPre : CorePre s key nonce associatedData plaintext inPtr outPtr) :
    Frame 0x1c0 8 s := by
  have hS := Encrypt.stack_facts hPre
  have hroom := hS.room
  have htop := hS.top
  have htab := hS.tables
  rw [show Frame 0x1c0 8 s = Frame 0x1c0 8 s from rfl]
  have hsp : rspOf s = stackPtr s := rspOf_eq s
  have haddr (i : Nat) (hi : i < 0x1c8) :
      (rspOf s - BitVec.ofNat 64 0x1c0 + BitVec.ofNat 64 i).toNat = (stackPtr s).toNat - 0x1c0 + i := by
    rw [hsp, Encrypt.toNat_add_ofNat, Encrypt.toNat_sub_ofNat] <;>
      first | omega | (rw [Encrypt.toNat_sub_ofNat] <;> omega)
  refine ⟨by rw [hsp]; omega, by rw [hsp]; omega, fun i hi => ?_, by rw [hsp]; omega, ?_,
    fun i hi => ?_⟩
  · obtain ⟨b, hb⟩ := hPre.stack.2.1 _ (Encrypt.stack_contains.mpr (by rw [haddr i hi]; omega))
    rw [hb]; rfl
  · rw [hsp]
    unfold codeLo codeHi
    refine Classical.byContradiction fun hc => ?_
    have hx : max ((stackPtr s).toNat - 0x1c0) 0x100650 < 2 ^ 64 := by omega
    apply hS.outside (BitVec.ofNat 64 (max ((stackPtr s).toNat - 0x1c0) 0x100650))
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx]; omega
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx]; omega
    · apply Encrypt.inProgram_of_toNat <;> rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx] <;> omega
  · apply hS.outside <;> rw [haddr i hi] <;> omega

theorem segPre_of_core (hPre : CorePre s key nonce associatedData plaintext inPtr outPtr) :
    SegPre 0x100650 0x1c0 8 s := by
  have hS := Encrypt.stack_facts hPre
  have hroom := hS.room
  have htop := hS.top
  have hsp : rspOf s = stackPtr s := rspOf_eq s
  have hk := hPre.keyInMemory
  have hn := hPre.nonceInMemory
  have hsi : (Operand.reg 6 : Operand 64).read s = s.regValue .rsi := rfl
  have hdx : (Operand.reg 2 : Operand 64).read s = s.regValue .rdx := rfl
  simp only [ValidInput, keyRegion, nonceRegion, registerRegion, MemoryRegion.Bounded,
    userAddressLimit] at hk hn
  have hks := hPre.separation.2.1 (Stack.region s coreStackBytes) (by simp [coreWritten])
    (keyRegion s) (by simp [coreRead])
  have hns := hPre.separation.2.1 (Stack.region s coreStackBytes) (by simp [coreWritten])
    (nonceRegion s) (by simp [coreRead])
  have hmem (r : BitVec 64) (n : Nat) (hlow : r.toNat + n < 2 ^ 32) {bytes : ByteArray}
      (hsz : bytes.size = n)
      (hb : ∀ i : Fin bytes.size, s.external[BitVec.ofNat 64 (r.toNat + i.val)]? = some bytes[i.val]) :
      MemReadable s r n := by
    refine ⟨by omega, fun i hi => ?_⟩
    have := hb ⟨i, by omega⟩
    rw [show r + BitVec.ofNat 64 i = BitVec.ofNat 64 (r.toNat + i) by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega]
    rw [this]; rfl
  have hstack (x : Nat) (h₁ : (stackPtr s).toNat - 992 ≤ x) (h₂ : x < (stackPtr s).toNat + 8) :
      (Stack.region s coreStackBytes).Contains x := Encrypt.stack_contains.mpr ⟨h₁, h₂⟩
  refine ⟨hPre.entry, frame_of_core hPre, ?_, ?_, ?_, ?_⟩
  · rw [hsi]
    exact hmem _ 32 hk.1 (by simp [ByteArray.size]) hk.2.2
  · rw [hsi, hsp]
    have h := sep_of_overlap (a := (s.regValue .rsi).toNat) (n := 32)
      (b := (stackPtr s).toNat - 992) (m := 1000) fun x h₁ h₂ h₃ h₄ =>
        hks x (hstack x h₃ (by omega)) ⟨h₁, h₂⟩
    generalize (s.regValue .rsi).toNat = a at h ⊢
    generalize (stackPtr s).toNat = b at h hroom ⊢
    omega
  · rw [hdx]
    exact hmem _ 12 hn.1 (by simp [ByteArray.size]) hn.2.2
  · rw [hdx, hsp]
    have h := sep_of_overlap (a := (s.regValue .rdx).toNat) (n := 12)
      (b := (stackPtr s).toNat - 992) (m := 1000) fun x h₁ h₂ h₃ h₄ =>
        hns x (hstack x h₃ (by omega)) ⟨h₁, h₂⟩
    generalize (s.regValue .rdx).toNat = a at h ⊢
    generalize (stackPtr s).toNat = b at h hroom ⊢
    omega

end Entry

section Chain

variable [bindings : Machine.Bindings]

omit bindings in
theorem SegPre.step {p p' : BitVec 64} {lo hi : Nat} {t u : RamState} {cs : List Component}
    (h : SegPre p lo hi t) (hrip : u.RIP = p') (hag : AgreesExcept cs t u)
    (h4 : Component.reg 4 ∉ cs) (h6 : Component.reg 6 ∉ cs) (h2 : Component.reg 2 ∉ cs) :
    SegPre p' lo hi u := by
  have hsp : rspOf u = rspOf t := hag.read h4
  have hsi : (Operand.reg 6 : Operand 64).read u = (Operand.reg 6 : Operand 64).read t :=
    hag.read h6
  have hdx : (Operand.reg 2 : Operand 64).read u = (Operand.reg 2 : Operand 64).read t :=
    hag.read h2
  refine ⟨hrip, h.frame.same hsp hag.grow, ?_, ?_, ?_, ?_⟩
  · rw [hsi]; exact ⟨h.key.low, fun i hi => hag.grow _ (h.key.mem i hi)⟩
  · rw [hsi, hsp]; exact h.keySep
  · rw [hdx]; exact ⟨h.nonce.low, fun i hi => hag.grow _ (h.nonce.mem i hi)⟩
  · rw [hdx, hsp]; exact h.nonceSep

omit bindings in
theorem StackPre.of_seg {p p' : BitVec 64} {lo hi : Nat} {t u : RamState} {cs : List Component}
    (h : SegPre p lo hi t) (hrip : u.RIP = p') (hag : AgreesExcept cs t u)
    (h4 : Component.reg 4 ∉ cs) : StackPre p' lo hi u :=
  ⟨hrip, h.frame.same (hag.read h4) hag.grow⟩

theorem ready_of_core {s : RamState} {key : Vector UInt8 32} {nonce : Vector UInt8 12}
    {associatedData plaintext : ByteArray} {inPtr outPtr : BitVec 64}
    (hPre : CorePre s key nonce associatedData plaintext inPtr outPtr) : ReadyToStep s :=
  ReadyToStep.of_supported hPre.machine hPre.environment.smrr hPre.environment.memoryType
    (DecoderFeatures.of_supported hPre.machine hPre.environment.leadingZeroCount)

def Win (s : RamState) (lo hi : Nat) (x : Nat) : Prop :=
  frameBase s + lo ≤ x ∧ x < frameBase s + hi

macro "comp_simp" e:term : tactic => `(tactic|
  simp [$e:term, Effect.components])

theorem prefix_states (boundary : ReturnBoundary) (hb : Away boundary) {s : RamState}
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s) (hSeg : SegPre 0x100650 0x1c0 8 s) :
    ∃ t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 : RamState, ∃ fuel, Advances boundary fuel s t11 ∧
      ReadyToStep t11 ∧ CodeIn Extracted.programImage t11 ∧
      (effA s).Holds s t1 ∧ (effB t1).Holds t1 t2 ∧ (effC t2).Holds t2 t3 ∧
      (effD t3).Holds t3 t4 ∧ (effE t4).Holds t4 t5 ∧ (effF t5).Holds t5 t6 ∧
      (effJ t6).Holds t6 t7 ∧ (effG t7).Holds t7 t8 ∧ (effH t8).Holds t8 t9 ∧
      (effI t9).Holds t9 t10 ∧ (effK t10).Holds t10 t11 ∧ SegPre 0x1007ab 8 0x1c0 t9 := by
  obtain ⟨f1, t1, a1, r1, c1, h1⟩ := chunkA_program boundary hb s hr hc hSeg
  have p2 : SegPre 0x100661 8 0x1c0 t1 :=
    SegPre.prologue hSeg h1.rip h1.writes.2.2.2.2.2.2 (h1.agrees.read (by comp_simp effA))
      (h1.agrees.read (by comp_simp effA)) h1.agrees.grow
  obtain ⟨f2, t2, a2, r2, c2, h2⟩ := chunkB_program boundary hb t1 r1 c1 p2
  have p3 : SegPre 0x10066d 8 0x1c0 t2 := SegPre.step p2 h2.rip h2.agrees
    (by comp_simp effB) (by comp_simp effB) (by comp_simp effB)
  obtain ⟨f3, t3, a3, r3, c3, h3⟩ := chunkC_program boundary hb t2 r2 c2 p3
  have p4 : SegPre 0x100698 8 0x1c0 t3 := SegPre.step p3 h3.rip h3.agrees
    (by comp_simp effC) (by comp_simp effC) (by comp_simp effC)
  obtain ⟨f4, t4, a4, r4, c4, h4⟩ := chunkD_program boundary hb t3 r3 c3 p4
  have p5 : SegPre 0x1006c0 8 0x1c0 t4 := SegPre.step p4 h4.rip h4.agrees
    (by comp_simp effD) (by comp_simp effD) (by comp_simp effD)
  obtain ⟨f5, t5, a5, r5, c5, h5⟩ := chunkE_program boundary hb t4 r4 c4 p5
  have p6 : SegPre 0x1006cf 8 0x1c0 t5 := SegPre.step p5 h5.rip h5.agrees
    (by comp_simp effE) (by comp_simp effE) (by comp_simp effE)
  obtain ⟨f6, t6, a6, r6, c6, h6⟩ := chunkF_program boundary hb t5 r5 c5 p6
  have p7 : SegPre 0x100714 8 0x1c0 t6 := SegPre.step p6 h6.rip h6.agrees
    (by comp_simp effF) (by comp_simp effF) (by comp_simp effF)
  obtain ⟨f7, t7, a7, r7, c7, h7⟩ := chunkJ_program boundary hb t6 r6 c6 p7
  have p8 : SegPre 0x100720 8 0x1c0 t7 := SegPre.step p7 h7.rip h7.agrees
    (by comp_simp effJ) (by comp_simp effJ) (by comp_simp effJ)
  obtain ⟨f8, t8, a8, r8, c8, h8⟩ := chunkG_program boundary hb t7 r7 c7 p8
  have p9 : SegPre 0x10076e 8 0x1c0 t8 := SegPre.step p8 h8.rip h8.agrees
    (by comp_simp effG) (by comp_simp effG) (by comp_simp effG)
  obtain ⟨f9, t9, a9, r9, c9, h9⟩ := chunkH_program boundary hb t8 r8 c8 p9
  have p10 : SegPre 0x1007ab 8 0x1c0 t9 := SegPre.step p9 h9.rip h9.agrees
    (by comp_simp effH) (by comp_simp effH) (by comp_simp effH)
  obtain ⟨f10, t10, a10, r10, c10, h10⟩ := chunkI_program boundary hb t9 r9 c9 p10
  have p11 : StackPre 0x1007dc 8 0x1c0 t10 := StackPre.of_seg p10 h10.rip h10.agrees
    (by comp_simp effI)
  obtain ⟨f11, t11, a11, r11, c11, h11⟩ := chunkK_program boundary hb t10 r10 c10 p11
  exact ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, _,
    a1.trans (a2.trans (a3.trans (a4.trans (a5.trans (a6.trans (a7.trans (a8.trans
      (a9.trans (a10.trans a11))))))))), r11, c11, h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11,
    p10⟩

end Chain

end ChaCha20Poly1305.Proofs.Core.Setup

namespace ChaCha20Poly1305.Proofs.Core.Setup


open ChaCha20Poly1305.Spec.Program Standards.RFC.ChaCha20Poly1305 Prelude X86 X86.Machine
open X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CoreContract
open ChaCha20Poly1305.Proofs.MemoryRoutines.Machine

section Facts

abbrev rg (u : RamState) (r : BitVec 5) : BitVec 64 := Operand.read u (Operand.reg r : Operand 64)

abbrev ld (u : RamState) (a : BitVec 64) (n : Nat) : BitVec n := memLoad u.external a n

variable {s : RamState}

theorem fp_off (hS : Encrypt.StackFacts s) {k i : Nat} (h : k + i ≤ 0x1c0) :
    (framePointer s + BitVec.ofNat 64 k + BitVec.ofNat 64 i).toNat = frameBase s + k + i := by
  have h1 := Encrypt.framePointer_add_toNat hS (k := k) (by omega)
  have := hS.top
  have := hS.room
  rw [Encrypt.toNat_add_ofNat (by rw [h1]; unfold frameBase frameBytes; omega), h1]

theorem keep_load {W : Nat → Prop} {a b : RamState} (h : Encrypt.Same W a b)
    (hS : Encrypt.StackFacts s) {k n : Nat} (hk : k + n / 8 ≤ 0x1c0)
    (hw : ∀ i < n / 8, ¬ W (frameBase s + k + i)) :
    ld b (framePointer s + BitVec.ofNat 64 k) n = ld a (framePointer s + BitVec.ofNat 64 k) n :=
  h.load fun i hi => by rw [fp_off hS (by omega)]; exact hw i hi

theorem wrap_toNat {a : BitVec 64} {c : Nat} (h₁ : c < 2 ^ 64) (h₂ : 2 ^ 64 ≤ a.toNat + c) :
    (a + BitVec.ofNat 64 c).toNat = a.toNat + c - 2 ^ 64 := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt h₁]
  have := a.isLt
  omega

def WinK (s : RamState) (x : Nat) : Prop := frameBase s - 8 ≤ x ∧ x < frameBase s

def WinH (s : RamState) (x : Nat) : Prop :=
  Win s 0x48 0x4c x ∨ Win s 0x58 0x59 x ∨ Win s 0xb0 0xd0 x

macro "same_tac" e:ident hF:ident : tactic => `(tactic| (
  simp only [$e:ident, Effect.components, List.map_cons, List.map_nil, Write.component_reg,
    Write.component_mem, List.cons_append, List.nil_append, List.append_nil,
    List.forall_mem_cons, List.forall_mem_nil, and_true]
  repeat' apply And.intro
  all_goals first
    | exact fun x hx => absurd hx (Encrypt.nonmem_not_covers rfl x)
    | (rw [$hF:ident]
       apply Encrypt.mem_within
       all_goals rw [Encrypt.framePointer_add_toNat ‹Encrypt.StackFacts _› (by decide)]
       all_goals (try intro j hj)
       all_goals simp only [Win, WinH, frameBase, frameBytes]
       all_goals omega)
    | exact fun c hc => absurd hc List.not_mem_nil))

theorem sameC (hS : Encrypt.StackFacts s) {t u : RamState} (h : (effC t).Holds t u)
    (hF : Operand.read t (Operand.reg 4#5 : Operand 64) = framePointer s) :
    Encrypt.Same (Win s 0xd0 0xe0) t u := by
  have := hS.room; have := hS.top
  exact Encrypt.Same.of_agrees h.agrees (by same_tac effC hF)


theorem sameD (hS : Encrypt.StackFacts s) {t u : RamState} (h : (effD t).Holds t u)
    (hF : Operand.read t (Operand.reg 4#5 : Operand 64) = framePointer s) :
    Encrypt.Same (Win s 0xe0 0x100) t u := by
  have := hS.room; have := hS.top
  exact Encrypt.Same.of_agrees h.agrees (by same_tac effD hF)

theorem sameE (hS : Encrypt.StackFacts s) {t u : RamState} (h : (effE t).Holds t u)
    (hF : Operand.read t (Operand.reg 4#5 : Operand 64) = framePointer s) :
    Encrypt.Same (Win s 0x4c 0x58) t u := by
  have := hS.room; have := hS.top
  exact Encrypt.Same.of_agrees h.agrees (by same_tac effE hF)

theorem sameF (hS : Encrypt.StackFacts s) {t u : RamState} (h : (effF t).Holds t u)
    (hF : Operand.read t (Operand.reg 4#5 : Operand 64) = framePointer s) :
    Encrypt.Same (Win s 0x59 0x91) t u := by
  have := hS.room; have := hS.top
  exact Encrypt.Same.of_agrees h.agrees (by same_tac effF hF)

theorem sameJ (hS : Encrypt.StackFacts s) {t u : RamState} (h : (effJ t).Holds t u)
    (hF : Operand.read t (Operand.reg 4#5 : Operand 64) = framePointer s) :
    Encrypt.Same (Win s 0x90 0x98) t u := by
  have := hS.room; have := hS.top
  exact Encrypt.Same.of_agrees h.agrees (by same_tac effJ hF)

theorem sameG (hS : Encrypt.StackFacts s) {t u : RamState} (h : (effG t).Holds t u)
    (hF : Operand.read t (Operand.reg 4#5 : Operand 64) = framePointer s) :
    Encrypt.Same (Win s 0x18 0x48) t u := by
  have := hS.room; have := hS.top
  exact Encrypt.Same.of_agrees h.agrees (by same_tac effG hF)

theorem sameI (hS : Encrypt.StackFacts s) {t u : RamState} (h : (effI t).Holds t u)
    (hF : Operand.read t (Operand.reg 4#5 : Operand 64) = framePointer s) :
    Encrypt.Same (Win s 0xd0 0xe8) t u := by
  have := hS.room; have := hS.top
  exact Encrypt.Same.of_agrees h.agrees (by same_tac effI hF)

theorem sameB (hS : Encrypt.StackFacts s) {t u : RamState} (h : (effB t).Holds t u)
    (_hF : Operand.read t (Operand.reg 4#5 : Operand 64) = framePointer s) :
    Encrypt.Same (Win s 0 0) t u := by
  have := hS.room; have := hS.top
  exact Encrypt.Same.of_agrees h.agrees (by same_tac effB _hF)

theorem sameH (hS : Encrypt.StackFacts s) {t u : RamState} (h : (effH t).Holds t u)
    (hF : Operand.read t (Operand.reg 4#5 : Operand 64) = framePointer s) :
    Encrypt.Same (WinH s) t u := by
  have := hS.room; have := hS.top
  exact Encrypt.Same.of_agrees h.agrees (by same_tac effH hF)

theorem fp_neg8 (hS : Encrypt.StackFacts s) :
    (framePointer s + 18446744073709551608#64).toNat = frameBase s - 8 := by
  have h1 := Encrypt.framePointer_toNat hS
  have := hS.room
  rw [wrap_toNat (by decide) (by rw [h1]; unfold frameBase frameBytes; omega), h1]
  omega

theorem fp_neg8_eq (hS : Encrypt.StackFacts s) :
    framePointer s + 18446744073709551608#64 = framePointer s - BitVec.ofNat 64 8 := by
  apply BitVec.eq_of_toNat_eq
  rw [fp_neg8 hS, Encrypt.framePointer_sub_toNat hS (by decide)]

set_option linter.unusedSimpArgs false in
theorem sameK (hS : Encrypt.StackFacts s) {t u : RamState} (h : (effK t).Holds t u)
    (hF : Operand.read t (Operand.reg 4#5 : Operand 64) = framePointer s) :
    Encrypt.Same (WinK s) t u := by
  have := hS.room; have := hS.top
  apply Encrypt.Same.of_agrees h.agrees
  simp only [effK, Effect.components, List.map_cons, List.map_nil, Write.component_reg,
    Write.component_mem, List.cons_append, List.nil_append, List.append_nil,
    List.forall_mem_cons, List.forall_mem_nil, and_true]
  refine ⟨fun x hx => absurd hx (Encrypt.nonmem_not_covers rfl x), ?_,
    fun x hx => absurd hx (Encrypt.nonmem_not_covers rfl x), fun c hc => absurd hc List.not_mem_nil⟩
  rw [hF]
  apply Encrypt.mem_within <;> rw [fp_neg8 hS]
  · unfold frameBase frameBytes; omega
  · intro j hj; simp only [WinK, frameBase, frameBytes]; omega

set_option linter.unusedSimpArgs false in
theorem sameA (hS : Encrypt.StackFacts s) {u : RamState} (h : (effA s).Holds s u) :
    Encrypt.Same (Win s 0x188 0x1b8) s u := by
  have := hS.room; have := hS.top
  have hsA : Operand.read s (Operand.reg 4#5 : Operand 64) = stackPtr s :=
    (stackPtr_eq_read s).symm
  apply Encrypt.Same.of_agrees h.agrees
  simp only [effA, Effect.components, List.map_cons, List.map_nil, Write.component_reg,
    Write.component_mem, List.cons_append, List.nil_append, List.append_nil,
    List.forall_mem_cons, List.forall_mem_nil, and_true]
  repeat' apply And.intro
  all_goals first
    | exact fun x hx => absurd hx (Encrypt.nonmem_not_covers rfl x)
    | (rw [hsA]
       apply Encrypt.mem_within
       all_goals rw [wrap_toNat (by decide) (by omega)]
       all_goals (try intro j hj)
       all_goals (try simp only [Win, frameBase, frameBytes])
       all_goals omega)
    | exact fun c hc => absurd hc List.not_mem_nil


theorem rg_keep {cs : List Component} {u v : RamState} (h : AgreesExcept cs u v) {r : BitVec 5}
    (hr : Component.reg r ∉ cs) : rg v r = rg u r := h.read hr

macro "comps " e:ident : term => `(by simp [$e:ident, Effect.components])

theorem key_keep {W : Nat → Prop} {a b : RamState} (h : Encrypt.Same W a b) {r : BitVec 64}
    {k n : Nat} (hlow : r.toNat + k + n / 8 < 2 ^ 64)
    (hw : ∀ i < n / 8, ¬ W (r.toNat + k + i)) :
    ld b (r + BitVec.ofNat 64 k) n = ld a (r + BitVec.ofNat 64 k) n :=
  h.load fun i hi => by
    rw [Encrypt.toNat_add_ofNat (by rw [Encrypt.toNat_add_ofNat (by omega)]; omega),
      Encrypt.toNat_add_ofNat (by omega)]
    exact hw i hi

structure Loads (s v : RamState) : Prop where
  rsp : rg v 4 = framePointer s - BitVec.ofNat 64 8
  rdi : rg v 7 = framePointer s + BitVec.ofNat 64 0x18
  rsi : rg v 6 = framePointer s + BitVec.ofNat 64 0xd0
  rbp : rg v 5 = rg s 1
  r12 : rg v 12 = rg s 9
  r13 : rg v 13 = rg s 8
  r14 : rg v 14 = rg s 7
  w18 : ld v (framePointer s + BitVec.ofNat 64 0x18) 64 = 3684054920433006693#64
  w20 : ld v (framePointer s + BitVec.ofNat 64 0x20) 64 = 7719281312240119090#64
  w28 : ld v (framePointer s + BitVec.ofNat 64 0x28) 64 = ld s (rg s 6 + BitVec.ofNat 64 0) 64
  w30 : ld v (framePointer s + BitVec.ofNat 64 0x30) 64 = ld s (rg s 6 + BitVec.ofNat 64 8) 64
  w38 : ld v (framePointer s + BitVec.ofNat 64 0x38) 64 = ld s (rg s 6 + BitVec.ofNat 64 16) 64
  w40 : ld v (framePointer s + BitVec.ofNat 64 0x40) 64 = ld s (rg s 6 + BitVec.ofNat 64 24) 64
  w48 : ld v (framePointer s + BitVec.ofNat 64 0x48) 32 = 0#32
  w4c : ld v (framePointer s + BitVec.ofNat 64 0x4c) 64 = ld s (rg s 2 + BitVec.ofNat 64 0) 64
  w54 : ld v (framePointer s + BitVec.ofNat 64 0x54) 32 = ld s (rg s 2 + BitVec.ofNat 64 8) 32
  w58 : ld v (framePointer s + BitVec.ofNat 64 0x58) 8 = 64#8
  wb0 : ld v (framePointer s + BitVec.ofNat 64 0xb0) 64 = 0#64
  wb8 : ld v (framePointer s + BitVec.ofNat 64 0xb8) 64 = 0#64
  wc0 : ld v (framePointer s + BitVec.ofNat 64 0xc0) 64 = 0#64
  wc8 : ld v (framePointer s + BitVec.ofNat 64 0xc8) 64 = 0#64
  wd0 : ld v (framePointer s + BitVec.ofNat 64 0xd0) 64 = framePointer s + 176#64
  wd8 : ld v (framePointer s + BitVec.ofNat 64 0xd8) 64 = framePointer s + 176#64
  we0 : ld v (framePointer s + BitVec.ofNat 64 0xe0) 64 = 32#64
  ret : ld v (framePointer s - BitVec.ofNat 64 8) 64 = 1050593#64
  s188 : ld v (framePointer s + BitVec.ofNat 64 0x188) 64 = rg s 3
  s190 : ld v (framePointer s + BitVec.ofNat 64 0x190) 64 = rg s 12
  s198 : ld v (framePointer s + BitVec.ofNat 64 0x198) 64 = rg s 13
  s1a0 : ld v (framePointer s + BitVec.ofNat 64 0x1a0) 64 = rg s 14
  s1a8 : ld v (framePointer s + BitVec.ofNat 64 0x1a8) 64 = rg s 15
  s1b0 : ld v (framePointer s + BitVec.ofNat 64 0x1b0) 64 = rg s 5

theorem push_addr (hS : Encrypt.StackFacts s) (k c : Nat) (hk : 8 ≤ k ∧ k ≤ 0x30)
    (hc : c + k = 2 ^ 64) :
    rg s 4 + BitVec.ofNat 64 c = framePointer s + BitVec.ofNat 64 (0x1b8 - k) := by
  have := hS.room
  have h1 := Encrypt.framePointer_add_toNat hS (k := 0x1b8 - k) (by omega)
  apply BitVec.eq_of_toNat_eq
  rw [h1, show rg s 4 = stackPtr s from (stackPtr_eq_read s).symm,
    wrap_toNat (by omega) (by omega)]
  unfold frameBase frameBytes
  omega

macro "kp " h:ident : tactic => `(tactic|
  rw [keep_load $h ‹Encrypt.StackFacts _› (by decide)
    (by intro i hi; (try simp only [Win, WinH, WinK]); omega)])

macro "kk " h:ident : tactic => `(tactic|
  rw [key_keep $h (by omega)
    (by intro i hi; (try simp only [Win, WinH, WinK, frameBase, frameBytes]); omega)])

set_option maxHeartbeats 4000000 in
theorem prefix_loads (hS : Encrypt.StackFacts s) (hSeg : SegPre 0x100650 0x1c0 8 s)
    {t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 : RamState}
    (h1 : (effA s).Holds s t1) (h2 : (effB t1).Holds t1 t2) (h3 : (effC t2).Holds t2 t3)
    (h4 : (effD t3).Holds t3 t4) (h5 : (effE t4).Holds t4 t5) (h6 : (effF t5).Holds t5 t6)
    (h7 : (effJ t6).Holds t6 t7) (h8 : (effG t7).Holds t7 t8) (h9 : (effH t8).Holds t8 t9)
    (h10 : (effI t9).Holds t9 t10) (h11 : (effK t10).Holds t10 t11) : Loads s t11 := by
  have hroom := hS.room
  have htop := hS.top
  have hsA : rg s 4 = stackPtr s := (stackPtr_eq_read s).symm
  have hF1 : rg t1 4 = framePointer s := by
    have w : rg t1 4 = Operand.read s (Operand.reg 4#5 : Operand 64) +
        18446744073709551568#64 - 392#64 := h1.writes.2.2.2.2.2.2
    rw [w]
    change rg s 4 + _ - _ = _
    rw [hsA, framePointer, frameBytes, BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg,
      BitVec.add_assoc]
    rfl
  have hF2 : rg t2 4 = framePointer s := (rg_keep h2.agrees (comps effB)).trans hF1
  have hF3 : rg t3 4 = framePointer s := (rg_keep h3.agrees (comps effC)).trans hF2
  have hF4 : rg t4 4 = framePointer s := (rg_keep h4.agrees (comps effD)).trans hF3
  have hF5 : rg t5 4 = framePointer s := (rg_keep h5.agrees (comps effE)).trans hF4
  have hF6 : rg t6 4 = framePointer s := (rg_keep h6.agrees (comps effF)).trans hF5
  have hF7 : rg t7 4 = framePointer s := (rg_keep h7.agrees (comps effJ)).trans hF6
  have hF8 : rg t8 4 = framePointer s := (rg_keep h8.agrees (comps effG)).trans hF7
  have hF9 : rg t9 4 = framePointer s := (rg_keep h9.agrees (comps effH)).trans hF8
  have hF10 : rg t10 4 = framePointer s := (rg_keep h10.agrees (comps effI)).trans hF9
  have sA := sameA hS h1
  have sB := sameB hS h2 hF1
  have sC := sameC hS h3 hF2
  have sD := sameD hS h4 hF3
  have sE := sameE hS h5 hF4
  have sF := sameF hS h6 hF5
  have sJ := sameJ hS h7 hF6
  have sG := sameG hS h8 hF7
  have sH := sameH hS h9 hF8
  have sI := sameI hS h10 hF9
  have sK := sameK hS h11 hF10
  have hks : (rg s 6).toNat + 32 ≤ (stackPtr s).toNat - 0x1c0 ∨
      (stackPtr s).toNat + 8 ≤ (rg s 6).toNat := by
    have := hSeg.keySep; rw [rspOf_eq] at this; exact this
  have hns : (rg s 2).toNat + 12 ≤ (stackPtr s).toNat - 0x1c0 ∨
      (stackPtr s).toNat + 8 ≤ (rg s 2).toNat := by
    have := hSeg.nonceSep; rw [rspOf_eq] at this; exact this
  have hkl : (rg s 6).toNat + 32 ≤ 2 ^ 32 := hSeg.key.low
  have hnl : (rg s 2).toNat + 12 ≤ 2 ^ 32 := hSeg.nonce.low
  have hsi2 : rg t2 6 = rg s 6 := by
    rw [rg_keep h2.agrees (r := 6) (comps effB), rg_keep h1.agrees (r := 6) (comps effA)]
  have hsi3 : rg t3 6 = rg s 6 := by rw [rg_keep h3.agrees (r := 6) (comps effC), hsi2]
  have hdx4 : rg t4 2 = rg s 2 := by
    rw [rg_keep h4.agrees (r := 2) (comps effD), rg_keep h3.agrees (r := 2) (comps effC),
      rg_keep h2.agrees (r := 2) (comps effB), rg_keep h1.agrees (r := 2) (comps effA)]
  obtain ⟨a1, a2, a3, a4, a5, a6, -⟩ := h1.writes
  obtain ⟨b1, b2, b3, b4⟩ := h2.writes
  obtain ⟨c1, c2, c3, c4⟩ := h3.writes
  obtain ⟨d1, d2, d3, -, d5⟩ := h4.writes
  obtain ⟨e1, -, e3⟩ := h5.writes
  obtain ⟨g1, g2, g3, g4, -, -, g7, g8⟩ := h8.writes
  obtain ⟨k1, k2, k3, k4, k5, k6⟩ := h9.writes
  obtain ⟨i1, i2, i3, i4, i5, i6⟩ := h10.writes
  obtain ⟨l1, l2⟩ := h11.writes
  have c1' : ld t3 (framePointer s + 216#64) 64 = 7719281312240119090#64 := by
    rw [← hF2]; exact c1
  have c2' : ld t3 (framePointer s + 208#64) 64 = 3684054920433006693#64 := by
    rw [← hF2]; exact c2
  have c3' : rg t3 0 = ld t2 (rg s 6 + 0#64) 64 := by rw [← hsi2]; exact c3
  have c4' : rg t3 1 = ld t2 (rg s 6 + 8#64) 64 := by rw [← hsi2]; exact c4
  have d1' : ld t4 (framePointer s + 224#64) 64 = rg t3 0 := by rw [← hF3]; exact d1
  have d2' : ld t4 (framePointer s + 232#64) 64 = rg t3 1 := by rw [← hF3]; exact d2
  have d3' : ld t4 (framePointer s + 240#64) 64 = ld t3 (rg s 6 + 16#64) 64 := by
    rw [← hF3, ← hsi3]; exact d3
  have d5' : ld t4 (framePointer s + 248#64) 64 = ld t3 (rg s 6 + 24#64) 64 := by
    rw [← hF3, ← hsi3]; exact d5
  have e1' : ld t5 (framePointer s + 76#64) 64 = ld t4 (rg s 2 + 0#64) 64 := by
    rw [← hF4, ← hdx4]; exact e1
  have e3' : ld t5 (framePointer s + 84#64) 32 = ld t4 (rg s 2 + 8#64) 32 := by
    rw [← hF4, ← hdx4, ← ChaCha20Poly1305.Proofs.Poly1305.Callee101e40.sw3264 (ld t4 (rg t4 2 + 8#64) 32)]; exact e3
  have g1' : ld t8 (framePointer s + 64#64) 64 = ld t7 (framePointer s + 248#64) 64 := by
    rw [← hF7]; exact g1
  have g2' : ld t8 (framePointer s + 56#64) 64 = ld t7 (framePointer s + 240#64) 64 := by
    rw [← hF7]; exact g2
  have g3' : ld t8 (framePointer s + 48#64) 64 = ld t7 (framePointer s + 232#64) 64 := by
    rw [← hF7]; exact g3
  have g4' : ld t8 (framePointer s + 40#64) 64 = ld t7 (framePointer s + 224#64) 64 := by
    rw [← hF7]; exact g4
  have g7' : ld t8 (framePointer s + 32#64) 64 = ld t7 (framePointer s + 216#64) 64 := by
    rw [← hF7]; exact g7
  have g8' : ld t8 (framePointer s + 24#64) 64 = ld t7 (framePointer s + 208#64) 64 := by
    rw [← hF7]; exact g8
  have k1' : ld t9 (framePointer s + 72#64) 32 = 0#32 := by rw [← hF8]; exact k1
  have k2' : ld t9 (framePointer s + 88#64) 8 = 64#8 := by rw [← hF8]; exact k2
  have k3' : ld t9 (framePointer s + 200#64) 64 = 0#64 := by rw [← hF8]; exact k3
  have k4' : ld t9 (framePointer s + 192#64) 64 = 0#64 := by rw [← hF8]; exact k4
  have k5' : ld t9 (framePointer s + 184#64) 64 = 0#64 := by rw [← hF8]; exact k5
  have k6' : ld t9 (framePointer s + 176#64) 64 = 0#64 := by rw [← hF8]; exact k6
  have i2' : ld t10 (framePointer s + 208#64) 64 = framePointer s + 176#64 := by
    rw [← hF9]; exact i2
  have i3' : ld t10 (framePointer s + 216#64) 64 = framePointer s + 176#64 := by
    rw [← hF9]; exact i3
  have i4' : ld t10 (framePointer s + 224#64) 64 = 32#64 := by rw [← hF9]; exact i4
  have i5' : rg t10 7 = framePointer s + 24#64 := by rw [← hF9]; exact i5
  have i6' : rg t10 6 = framePointer s + 208#64 := by rw [← hF9]; exact i6
  have l1' : rg t11 4 = framePointer s - BitVec.ofNat 64 8 := by
    rw [← fp_neg8_eq hS, ← hF10]; exact l1
  have l2' : ld t11 (framePointer s - BitVec.ofNat 64 8) 64 = 1050593#64 := by
    rw [← fp_neg8_eq hS, ← hF10]; exact l2
  have a1' : ld t1 (framePointer s + BitVec.ofNat 64 0x1b0) 64 = rg s 5 := by
    rw [← push_addr hS 8 18446744073709551608 (by decide) rfl]; exact a1
  have a2' : ld t1 (framePointer s + BitVec.ofNat 64 0x1a8) 64 = rg s 15 := by
    rw [← push_addr hS 16 18446744073709551600 (by decide) rfl]; exact a2
  have a3' : ld t1 (framePointer s + BitVec.ofNat 64 0x1a0) 64 = rg s 14 := by
    rw [← push_addr hS 24 18446744073709551592 (by decide) rfl]; exact a3
  have a4' : ld t1 (framePointer s + BitVec.ofNat 64 0x198) 64 = rg s 13 := by
    rw [← push_addr hS 32 18446744073709551584 (by decide) rfl]; exact a4
  have a5' : ld t1 (framePointer s + BitVec.ofNat 64 0x190) 64 = rg s 12 := by
    rw [← push_addr hS 40 18446744073709551576 (by decide) rfl]; exact a5
  have a6' : ld t1 (framePointer s + BitVec.ofNat 64 0x188) 64 = rg s 3 := by
    rw [← push_addr hS 48 18446744073709551568 (by decide) rfl]; exact a6
  have sA := sameA hS h1
  have sB := sameB hS h2 hF1
  have sC := sameC hS h3 hF2
  have sD := sameD hS h4 hF3
  have sE := sameE hS h5 hF4
  have sF := sameF hS h6 hF5
  have sJ := sameJ hS h7 hF6
  have sG := sameG hS h8 hF7
  have sH := sameH hS h9 hF8
  have sI := sameI hS h10 hF9
  have sK := sameK hS h11 hF10
  refine ⟨l1', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, l2', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [rg_keep h11.agrees (r := 7) (comps effK), i5']
  · rw [rg_keep h11.agrees (r := 6) (comps effK), i6']
  · rw [rg_keep h11.agrees (r := 5) (comps effK), rg_keep h10.agrees (r := 5) (comps effI),
      rg_keep h9.agrees (r := 5) (comps effH), rg_keep h8.agrees (r := 5) (comps effG),
      rg_keep h7.agrees (r := 5) (comps effJ), rg_keep h6.agrees (r := 5) (comps effF),
      rg_keep h5.agrees (r := 5) (comps effE), rg_keep h4.agrees (r := 5) (comps effD),
      rg_keep h3.agrees (r := 5) (comps effC)]
    exact b3.trans (rg_keep h1.agrees (r := 1) (comps effA))
  · rw [rg_keep h11.agrees (r := 12) (comps effK), rg_keep h10.agrees (r := 12) (comps effI),
      rg_keep h9.agrees (r := 12) (comps effH), rg_keep h8.agrees (r := 12) (comps effG),
      rg_keep h7.agrees (r := 12) (comps effJ), rg_keep h6.agrees (r := 12) (comps effF),
      rg_keep h5.agrees (r := 12) (comps effE), rg_keep h4.agrees (r := 12) (comps effD),
      rg_keep h3.agrees (r := 12) (comps effC)]
    exact b1.trans (rg_keep h1.agrees (r := 9) (comps effA))
  · rw [rg_keep h11.agrees (r := 13) (comps effK), rg_keep h10.agrees (r := 13) (comps effI),
      rg_keep h9.agrees (r := 13) (comps effH), rg_keep h8.agrees (r := 13) (comps effG),
      rg_keep h7.agrees (r := 13) (comps effJ), rg_keep h6.agrees (r := 13) (comps effF),
      rg_keep h5.agrees (r := 13) (comps effE), rg_keep h4.agrees (r := 13) (comps effD),
      rg_keep h3.agrees (r := 13) (comps effC)]
    exact b2.trans (rg_keep h1.agrees (r := 8) (comps effA))
  · rw [rg_keep h11.agrees (r := 14) (comps effK), rg_keep h10.agrees (r := 14) (comps effI),
      rg_keep h9.agrees (r := 14) (comps effH), rg_keep h8.agrees (r := 14) (comps effG),
      rg_keep h7.agrees (r := 14) (comps effJ), rg_keep h6.agrees (r := 14) (comps effF),
      rg_keep h5.agrees (r := 14) (comps effE), rg_keep h4.agrees (r := 14) (comps effD),
      rg_keep h3.agrees (r := 14) (comps effC)]
    exact b4.trans (rg_keep h1.agrees (r := 7) (comps effA))
  · kp sK; kp sI; kp sH; rw [g8']; kp sJ; kp sF; kp sE; kp sD; exact c2'
  · kp sK; kp sI; kp sH; rw [g7']; kp sJ; kp sF; kp sE; kp sD; exact c1'
  · kp sK; kp sI; kp sH; rw [g4']; kp sJ; kp sF; kp sE; rw [d1', c3']; kk sB; kk sA
  · kp sK; kp sI; kp sH; rw [g3']; kp sJ; kp sF; kp sE; rw [d2', c4']; kk sB; kk sA
  · kp sK; kp sI; kp sH; rw [g2']; kp sJ; kp sF; kp sE; rw [d3']; kk sC; kk sB; kk sA
  · kp sK; kp sI; kp sH; rw [g1']; kp sJ; kp sF; kp sE; rw [d5']; kk sC; kk sB; kk sA
  · kp sK; kp sI; exact k1'
  · kp sK; kp sI; kp sH; kp sG; kp sJ; kp sF; rw [e1']; kk sD; kk sC; kk sB; kk sA
  · kp sK; kp sI; kp sH; kp sG; kp sJ; kp sF; rw [e3']; kk sD; kk sC; kk sB; kk sA
  · kp sK; kp sI; exact k2'
  · kp sK; kp sI; exact k6'
  · kp sK; kp sI; exact k5'
  · kp sK; kp sI; exact k4'
  · kp sK; kp sI; exact k3'
  · kp sK; exact i2'
  · kp sK; exact i3'
  · kp sK; exact i4'
  all_goals kp sK; kp sI; kp sH; kp sG; kp sJ; kp sF; kp sE; kp sD; kp sC; kp sB
  · exact a6'
  · exact a5'
  · exact a4'
  · exact a3'
  · exact a2'
  · exact a1'

def WinS (s : RamState) (x : Nat) : Prop := frameBase s - 8 ≤ x ∧ x < frameBase s + 0x1b8

theorem prefix_misc [bindings : Machine.Bindings] (hS : Encrypt.StackFacts s)
    {t1 t2 t3 t4 t5 t6 t7 t8 t9 t10 t11 : RamState}
    (h1 : (effA s).Holds s t1) (h2 : (effB t1).Holds t1 t2) (h3 : (effC t2).Holds t2 t3)
    (h4 : (effD t3).Holds t3 t4) (h5 : (effE t4).Holds t4 t5) (h6 : (effF t5).Holds t5 t6)
    (h7 : (effJ t6).Holds t6 t7) (h8 : (effG t7).Holds t7 t8) (h9 : (effH t8).Holds t8 t9)
    (h10 : (effI t9).Holds t9 t10) (h11 : (effK t10).Holds t10 t11)
    (hdf : DirectionFlagUnset s) (hsse : SupportedSSE bindings.processor s) :
    Encrypt.Same (WinS s) s t11 ∧
      (∀ x : BitVec 64, (s.external[x]?).isSome → (t11.external[x]?).isSome) ∧
      DirectionFlagUnset t11 ∧ SupportedSSE bindings.processor t11 := by
  have hroom := hS.room
  have hsA : rg s 4 = stackPtr s := (stackPtr_eq_read s).symm
  have hF1 : rg t1 4 = framePointer s := by
    have w : rg t1 4 = Operand.read s (Operand.reg 4#5 : Operand 64) +
        18446744073709551568#64 - 392#64 := h1.writes.2.2.2.2.2.2
    rw [w]
    change rg s 4 + _ - _ = _
    rw [hsA, framePointer, frameBytes, BitVec.sub_eq_add_neg, BitVec.sub_eq_add_neg,
      BitVec.add_assoc]
    rfl
  have hF2 : rg t2 4 = framePointer s := (rg_keep h2.agrees (comps effB)).trans hF1
  have hF3 : rg t3 4 = framePointer s := (rg_keep h3.agrees (comps effC)).trans hF2
  have hF4 : rg t4 4 = framePointer s := (rg_keep h4.agrees (comps effD)).trans hF3
  have hF5 : rg t5 4 = framePointer s := (rg_keep h5.agrees (comps effE)).trans hF4
  have hF6 : rg t6 4 = framePointer s := (rg_keep h6.agrees (comps effF)).trans hF5
  have hF7 : rg t7 4 = framePointer s := (rg_keep h7.agrees (comps effJ)).trans hF6
  have hF8 : rg t8 4 = framePointer s := (rg_keep h8.agrees (comps effG)).trans hF7
  have hF9 : rg t9 4 = framePointer s := (rg_keep h9.agrees (comps effH)).trans hF8
  have hF10 : rg t10 4 = framePointer s := (rg_keep h10.agrees (comps effI)).trans hF9
  have mono {W : Nat → Prop} {a b : RamState} (h : Encrypt.Same W a b)
      (hw : ∀ x, W x → WinS s x) : Encrypt.Same (WinS s) a b := h.mono hw
  refine ⟨?_, ?_, ?_, ?_⟩
  · refine (mono (sameA hS h1) ?_).trans <| (mono (sameB hS h2 hF1) ?_).trans <|
      (mono (sameC hS h3 hF2) ?_).trans <| (mono (sameD hS h4 hF3) ?_).trans <|
      (mono (sameE hS h5 hF4) ?_).trans <| (mono (sameF hS h6 hF5) ?_).trans <|
      (mono (sameJ hS h7 hF6) ?_).trans <| (mono (sameG hS h8 hF7) ?_).trans <|
      (mono (sameH hS h9 hF8) ?_).trans <| (mono (sameI hS h10 hF9) ?_).trans <|
      mono (sameK hS h11 hF10) ?_
    all_goals intro x hx; simp only [Win, WinH, WinK, WinS] at hx ⊢; omega
  · intro x hx
    exact h11.agrees.grow _ (h10.agrees.grow _ (h9.agrees.grow _ (h8.agrees.grow _
      (h7.agrees.grow _ (h6.agrees.grow _ (h5.agrees.grow _ (h4.agrees.grow _
      (h3.agrees.grow _ (h2.agrees.grow _ (h1.agrees.grow _ hx))))))))))
  · exact h11.agrees.directionFlagClear (comps effK) <| h10.agrees.directionFlagClear (comps effI) <|
      h9.agrees.directionFlagClear (comps effH) <| h8.agrees.directionFlagClear (comps effG) <|
      h7.agrees.directionFlagClear (comps effJ) <| h6.agrees.directionFlagClear (comps effF) <|
      h5.agrees.directionFlagClear (comps effE) <| h4.agrees.directionFlagClear (comps effD) <|
      h3.agrees.directionFlagClear (comps effC) <| h2.agrees.directionFlagClear (comps effB) <|
      h1.agrees.directionFlagClear (comps effA) hdf
  · exact SupportedSSE.of_agreesExcept h11.agrees <| SupportedSSE.of_agreesExcept h10.agrees <|
      SupportedSSE.of_agreesExcept h9.agrees <| SupportedSSE.of_agreesExcept h8.agrees <|
      SupportedSSE.of_agreesExcept h7.agrees <| SupportedSSE.of_agreesExcept h6.agrees <|
      SupportedSSE.of_agreesExcept h5.agrees <| SupportedSSE.of_agreesExcept h4.agrees <|
      SupportedSSE.of_agreesExcept h3.agrees <| SupportedSSE.of_agreesExcept h2.agrees <|
      SupportedSSE.of_agreesExcept h1.agrees hsse

end Facts

end ChaCha20Poly1305.Proofs.Core.Setup

namespace ChaCha20Poly1305.Proofs.Core.Setup


open ChaCha20Poly1305.Spec.Program Standards.RFC.ChaCha20Poly1305 Prelude X86 X86.Machine
open X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CoreContract
open ChaCha20Poly1305.Proofs.MemoryRoutines.Machine

section Bytes

set_option linter.unusedSimpArgs false in
theorem le_byte (a b c d : UInt8) (j : Nat) (hj : j < 4) :
    ((littleEndianWord a b c d) >>> (8 * j).toUInt32).toUInt8 = #[a, b, c, d][j]! := by
  apply UInt8.toBitVec_inj.mp
  simp only [littleEndianWord]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have g (x : UInt8) (k : Nat) (hk : 8 ≤ k) : x.toBitVec.getLsbD k = false :=
    BitVec.getLsbD_of_ge _ _ hk
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl <;>
  simp [hi, show i < 32 by omega, show 8 + i < 32 by omega, show 16 + i < 32 by omega,
    show 24 + i < 32 by omega, show ¬ 8 + i < 8 by omega, show 8 + i < 16 by omega,
    show ¬ 16 + i < 16 by omega, show 16 + i < 24 by omega, show ¬ 24 + i < 24 by omega,
    show ¬ 16 + i < 8 by omega, show ¬ 24 + i < 8 by omega, show ¬ 24 + i < 16 by omega,
    show 16 + i - 16 = i by omega, show 24 + i - 24 = i by omega, show 8 + i - 8 = i by omega,
    show ¬ 24 ≤ 8 + i by omega, show 16 + i - 8 = 8 + i by omega, show 24 + i - 8 = 16 + i by omega,
    show 24 + i - 16 = 8 + i by omega, g _ (8 + i) (by omega), g _ (16 + i) (by omega),
    g _ (24 + i) (by omega)]

theorem serialize_key (key : Vector UInt8 32) (counter : UInt32) (nonce : Vector UInt8 12)
    (i : Nat) (hi : 16 ≤ i) (hi' : i < 48) :
    (serialize (initialState key counter nonce))[i]'(by omega) = key[i - 16]'(by omega) := by
  simp only [serialize, Vector.getElem_ofFn]
  have : (initialState key counter nonce)[i / 4]'(by omega) = littleEndianWord key[4 * (i/4 - 4)]! key[4 * (i/4-4) + 1]! key[4 * (i/4-4) + 2]! key[4 * (i/4-4) + 3]! := by
    simp only [initialState, chachaState]
    rcases (by omega : i / 4 = 4 ∨ i / 4 = 5 ∨ i / 4 = 6 ∨ i / 4 = 7 ∨ i / 4 = 8 ∨ i / 4 = 9 ∨ i / 4 = 10 ∨ i / 4 = 11) with h | h | h | h | h | h | h | h <;> simp [h]
  rw [this, le_byte _ _ _ _ _ (by omega)]
  have hk : i - 16 = 4 * (i / 4 - 4) + i % 4 := by omega
  rcases (by omega : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3) with h | h | h | h <;>
    simp only [h, hk] <;> simp <;> exact getElem!_pos key _ (by omega)

theorem serialize_nonce (key : Vector UInt8 32) (counter : UInt32) (nonce : Vector UInt8 12)
    (i : Nat) (hi : 52 ≤ i) (hi' : i < 64) :
    (serialize (initialState key counter nonce))[i]'(by omega) = nonce[i - 52]'(by omega) := by
  simp only [serialize, Vector.getElem_ofFn]
  have : (initialState key counter nonce)[i / 4]'(by omega) = littleEndianWord nonce[4 * (i/4 - 13)]! nonce[4 * (i/4-13) + 1]! nonce[4 * (i/4-13) + 2]! nonce[4 * (i/4-13) + 3]! := by
    simp only [initialState, chachaState, counterNonceWords]
    rcases (by omega : i / 4 = 13 ∨ i / 4 = 14 ∨ i / 4 = 15) with h | h | h <;> simp [h]
  rw [this, le_byte _ _ _ _ _ (by omega)]
  have hk : i - 52 = 4 * (i / 4 - 13) + i % 4 := by omega
  rcases (by omega : i % 4 = 0 ∨ i % 4 = 1 ∨ i % 4 = 2 ∨ i % 4 = 3) with h | h | h | h <;>
    simp only [h, hk] <;> simp <;> exact getElem!_pos nonce _ (by omega)

theorem serialize_const (key : Vector UInt8 32) (counter : UInt32) (nonce : Vector UInt8 12)
    (i : Nat) (hi : i < 16) :
    (serialize (initialState key counter nonce))[i]'(by omega) =
      #[0x65, 0x78, 0x70, 0x61, 0x6e, 0x64, 0x20, 0x33, 0x32, 0x2d, 0x62, 0x79, 0x74, 0x65, 0x20, 0x6b][i]! := by
  simp only [serialize, Vector.getElem_ofFn, initialState, chachaState]
  rcases (by omega : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨ i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15) with h|h|h|h|h|h|h|h|h|h|h|h|h|h|h|h <;> subst h <;> simp <;> rfl

theorem ld_byte {m : Ram} {a : BitVec 64} {n : Nat} {v : BitVec n} (h : memLoad m a n = v)
    (i : Nat) (hi : i < n / 8) : memByte m (a + BitVec.ofNat 64 i) = storedByte v i := by
  rw [← storedByte_memLoad m a i hi, h]

theorem addr_assoc (a : BitVec 64) (k i : Nat) :
    a + BitVec.ofNat 64 k + BitVec.ofNat 64 i = a + BitVec.ofNat 64 (k + i) := by
  rw [BitVec.add_assoc, BitVec.ofNat_add_ofNat]

theorem some_of_memByte {m : Ram} {a : BitVec 64} {b : UInt8} (hs : (m[a]?).isSome)
    (hb : memByte m a = b) : m[a]? = some b := by
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hs
  simp only [memByte] at hb
  change (m[a]?).getD 0 = b at hb
  rw [hx] at hb ⊢
  simp only [Option.getD_some] at hb
  rw [hb]

theorem hasBytes_of_memByte {m : Ram} {start n : Nat} {bytes : ByteArray} (hn : bytes.size = n)
    (hs : ∀ i < n, (m[BitVec.ofNat 64 (start + i)]?).isSome)
    (hb : ∀ i (h : i < n), memByte m (BitVec.ofNat 64 (start + i)) = bytes[i]'(by omega)) :
    (⟨start, n⟩ : MemoryRegion).HasBytes m bytes :=
  ⟨hn, fun i => some_of_memByte (hs i (by omega)) (hb i (by omega))⟩

end Bytes

section Words

variable [bindings : Machine.Bindings] {s : RamState} {key : Vector UInt8 32}
  {nonce : Vector UInt8 12} {associatedData plaintext : ByteArray} {inPtr outPtr : BitVec 64}

omit bindings in
theorem memByte_of_some {m : Ram} {a : BitVec 64} {b : UInt8} (h : m[a]? = some b) :
    memByte m a = b := by
  simp [memByte, PhysicalMemory.read, h]

omit bindings in
theorem input_byte {r : BitVec 64} {bytes : ByteArray} {n : Nat}
    (_hb : (⟨r.toNat, n⟩ : MemoryRegion).Bounded)
    (h : (⟨r.toNat, n⟩ : MemoryRegion).HasBytes s.external bytes) (k : Nat)
    (hk : k < bytes.size) : memByte s.external (r + BitVec.ofNat 64 k) = bytes[k] := by
  have e := h.2 ⟨k, hk⟩
  have hn : bytes.size = n := h.1
  rw [show r + BitVec.ofNat 64 k = BitVec.ofNat 64 (r.toNat + k) by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega]
  exact memByte_of_some e

theorem key_byte (hPre : CorePre s key nonce associatedData plaintext inPtr outPtr) (k : Nat)
    (hk : k < 32) : memByte s.external (rg s 6 + BitVec.ofNat 64 k) = key[k] := by
  have h := input_byte (r := rg s 6) (bytes := ⟨key.toArray⟩) hPre.keyInMemory.1
    hPre.keyInMemory.2 k (by simpa [ByteArray.size] using hk)
  rw [h]
  simp [ByteArray.getElem_eq_getElem_data]

theorem nonce_byte (hPre : CorePre s key nonce associatedData plaintext inPtr outPtr) (k : Nat)
    (hk : k < 12) : memByte s.external (rg s 2 + BitVec.ofNat 64 k) = nonce[k] := by
  have h := input_byte (r := rg s 2) (bytes := ⟨nonce.toArray⟩) hPre.nonceInMemory.1
    hPre.nonceInMemory.2 k (by simpa [ByteArray.size] using hk)
  rw [h]
  simp [ByteArray.getElem_eq_getElem_data]

theorem frame_some (hPre : CorePre s key nonce associatedData plaintext inPtr outPtr) {v : RamState}
    (hgrow : ∀ x : BitVec 64, (s.external[x]?).isSome → (v.external[x]?).isSome) (x : Nat)
    (h₁ : (stackPtr s).toNat - 992 ≤ x) (h₂ : x < (stackPtr s).toNat + 8) :
    (v.external[BitVec.ofNat 64 x]?).isSome := by
  have hS := Encrypt.stack_facts hPre
  have := hS.top
  apply hgrow
  obtain ⟨b, hb⟩ := hPre.stack.2.1 (BitVec.ofNat 64 x) (Encrypt.stack_contains.mpr
    (by rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega))
  rw [hb]; rfl

omit bindings in
theorem stateBytes_get (key : Vector UInt8 32) (counter : UInt32) (nonce : Vector UInt8 12)
    (j : Nat) (hj : j < 64) :
    (Callee100a80.stateBytes key counter nonce)[j]'(by simp [Callee100a80.stateBytes, ByteArray.size]; omega) =
      (serialize (initialState key counter nonce))[j] := by
  simp [Callee100a80.stateBytes, ByteArray.getElem_eq_getElem_data]

set_option maxHeartbeats 4000000 in
theorem words_of_loads (hPre : CorePre s key nonce associatedData plaintext inPtr outPtr)
    {v : RamState} (L : Loads s v)
    (hgrow : ∀ x : BitVec 64, (s.external[x]?).isSome → (v.external[x]?).isSome) :
    (⟨frameBase s + 0x18, 0x40⟩ : MemoryRegion).HasBytes v.external
      (Callee100a80.stateBytes key 0 nonce) := by
  have hS := Encrypt.stack_facts hPre
  have hroom := hS.room
  have htop := hS.top
  apply hasBytes_of_memByte (by simp [Callee100a80.stateBytes, ByteArray.size])
  · intro i hi
    exact frame_some hPre hgrow _ (by unfold frameBase frameBytes; omega)
      (by unfold frameBase frameBytes; omega)
  intro j hj
  rw [stateBytes_get key 0 nonce j hj]
  rw [show frameBase s + 0x18 + j = frameBase s + (0x18 + j) by omega,
    ← Encrypt.framePointer_add_eq hS (by omega)]
  have split (k i : Nat) (h : k + i = 0x18 + j) :
      framePointer s + BitVec.ofNat 64 (0x18 + j) =
        framePointer s + BitVec.ofNat 64 k + BitVec.ofNat 64 i := by
    rw [addr_assoc, h]
  rcases (by omega : j < 8 ∨ (8 ≤ j ∧ j < 16) ∨ (16 ≤ j ∧ j < 24) ∨ (24 ≤ j ∧ j < 32) ∨
      (32 ≤ j ∧ j < 40) ∨ (40 ≤ j ∧ j < 48) ∨ (48 ≤ j ∧ j < 52) ∨ (52 ≤ j ∧ j < 60) ∨
      (60 ≤ j ∧ j < 64)) with h | h | h | h | h | h | h | h | h
  · rw [split 0x18 j (by omega), ld_byte L.w18 j (by omega), serialize_const key 0 nonce j (by omega)]
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [split 0x20 (j - 8) (by omega), ld_byte L.w20 (j - 8) (by omega),
      serialize_const key 0 nonce j (by omega)]
    rcases (by omega : j = 8 ∨ j = 9 ∨ j = 10 ∨ j = 11 ∨ j = 12 ∨ j = 13 ∨ j = 14 ∨ j = 15) with
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  · rw [split 0x28 (j - 16) (by omega), ld_byte L.w28 (j - 16) (by omega),
      storedByte_memLoad _ _ _ (by omega), addr_assoc, key_byte hPre _ (by omega),
      serialize_key key 0 nonce j (by omega) (by omega)]
    congr 1; omega
  · rw [split 0x30 (j - 24) (by omega), ld_byte L.w30 (j - 24) (by omega),
      storedByte_memLoad _ _ _ (by omega), addr_assoc, key_byte hPre _ (by omega),
      serialize_key key 0 nonce j (by omega) (by omega)]
    congr 1; omega
  · rw [split 0x38 (j - 32) (by omega), ld_byte L.w38 (j - 32) (by omega),
      storedByte_memLoad _ _ _ (by omega), addr_assoc, key_byte hPre _ (by omega),
      serialize_key key 0 nonce j (by omega) (by omega)]
    congr 1; omega
  · rw [split 0x40 (j - 40) (by omega), ld_byte L.w40 (j - 40) (by omega),
      storedByte_memLoad _ _ _ (by omega), addr_assoc, key_byte hPre _ (by omega),
      serialize_key key 0 nonce j (by omega) (by omega)]
    congr 1; omega
  · obtain ⟨i, rfl⟩ : ∃ i, j = 48 + i := ⟨j - 48, by omega⟩
    rw [split 0x48 i (by omega), ld_byte L.w48 i (by omega)]
    have hc := Callee100a80.stateBytes_counter key 0 nonce i (by omega)
      (by simp [Callee100a80.stateBytes, ByteArray.size]; omega)
    rw [stateBytes_get key 0 nonce _ hj] at hc
    rw [hc]
    rfl
  · rw [split 0x4c (j - 52) (by omega), ld_byte L.w4c (j - 52) (by omega),
      storedByte_memLoad _ _ _ (by omega), addr_assoc, nonce_byte hPre _ (by omega),
      serialize_nonce key 0 nonce j (by omega) (by omega)]
    congr 1; omega
  · rw [split 0x54 (j - 60) (by omega), ld_byte L.w54 (j - 60) (by omega),
      storedByte_memLoad _ _ _ (by omega), addr_assoc, nonce_byte hPre _ (by omega),
      serialize_nonce key 0 nonce j (by omega) (by omega)]
    congr 1; omega

end Words

section KeyCall

variable [bindings : Machine.Bindings] {s : RamState} {key : Vector UInt8 32}
  {nonce : Vector UInt8 12} {associatedData plaintext : ByteArray} {inPtr outPtr : BitVec 64}

theorem stack_writable (hPre : CorePre s key nonce associatedData plaintext inPtr outPtr)
    {v : RamState} (hgrow : ∀ x : BitVec 64, (s.external[x]?).isSome → (v.external[x]?).isSome)
    {r : MemoryRegion} (h₁ : (stackPtr s).toNat - 992 ≤ r.start)
    (h₂ : r.start + r.size ≤ (stackPtr s).toNat + 8) : Callee100a80.Writable v r := by
  have hS := Encrypt.stack_facts hPre
  have := hS.top
  refine ⟨by omega, fun i hi => frame_some hPre hgrow _ (by omega) (by omega), fun a ha => ?_⟩
  exact Encrypt.stack_avoids hPre a (Encrypt.stack_contains.mpr ⟨by
    simp only [MemoryRegion.Contains] at ha; omega, by
    simp only [MemoryRegion.Contains] at ha; omega⟩)

omit bindings in
theorem fp_toNat' (hS : Encrypt.StackFacts s) {k : Nat} (hk : k ≤ 0x1c0) :
    (framePointer s + BitVec.ofNat 64 k).toNat = frameBase s + k :=
  Encrypt.framePointer_add_toNat hS hk

omit bindings in
theorem zeros32_size : zeros32.size = 32 := by simp [zeros32, ByteArray.size]

set_option maxHeartbeats 4000000 in
theorem keyCallPre (hPre : CorePre s key nonce associatedData plaintext inPtr outPtr)
    {v : RamState} (hr : ReadyToStep v) (hc : CodeIn Extracted.programImage v)
    (hrip : v.RIP = 0x100a80) (L : Loads s v)
    (hgrow : ∀ x : BitVec 64, (s.external[x]?).isSome → (v.external[x]?).isSome)
    (hdf : DirectionFlagUnset v) :
    Callee100a80.CallPre v key 0 nonce (framePointer s + 176#64) (framePointer s + 176#64)
      zeros32 := by
  have hS := Encrypt.stack_facts hPre
  have hroom := hS.room
  have htop := hS.top
  have hFB : frameBase s = (stackPtr s).toNat - 0x1b8 := rfl
  have hspv : (stackPtr v).toNat = frameBase s - 8 := by
    rw [stackPtr_eq_read]; change (rg v 4).toNat = _; rw [L.rsp]
    exact Encrypt.framePointer_sub_toNat hS (by decide)
  have hrdi : (rdi.read v).toNat = frameBase s + 0x18 := by
    change (rg v 7).toNat = _; rw [L.rdi]; exact fp_toNat' hS (by decide)
  have hrsi : (rsi.read v).toNat = frameBase s + 0xd0 := by
    change (rg v 6).toNat = _; rw [L.rsi]; exact fp_toNat' hS (by decide)
  have hin : (framePointer s + 176#64).toNat = frameBase s + 0xb0 := fp_toNat' hS (by decide)
  have hsome (x : Nat) (h₁ : frameBase s - 8 ≤ x) (h₂ : x < frameBase s + 0x1c0) :
      (v.external[BitVec.ofNat 64 x]?).isSome :=
    frame_some hPre hgrow x (by omega) (by omega)
  have hword (k : Nat) (hk : k ≤ 0x1b0) {w : BitVec 64}
      (hw : ld v (framePointer s + BitVec.ofNat 64 k) 64 = w) :
      (⟨frameBase s + k, 8⟩ : MemoryRegion).Word64At v.external w := by
    apply Encrypt.word64At_of_load rfl
    · rw [← Encrypt.framePointer_add_eq hS (by omega)]; exact hw
    · intro i hi
      dsimp only
      rw [← BitVec.ofNat_add]
      exact hsome _ (by omega) (by omega)
  have hsz := zeros32_size
  refine ⟨hr, hc, hrip, hdf, ?stackLow, ?stack, ?cipher, ?words, ?position,
    ?buf, ?inPtr, ?outPtr, ?length, ?messageBytes, ?low, ?out, Or.inl rfl,
    ?inputCipher, ?inputStack, ?outCipher, ?outStack, ?outBuf, ?cipherStack, ?cipherBuf,
    ?bufStack, ?returnLow, ?returnOutside⟩
  case stackLow => unfold Callee100a80.frameBytes; omega
  case stack =>
    apply stack_writable hPre hgrow <;>
      simp only [Callee100a80.stackRegion, Callee100a80.frameBytes, hspv] <;> omega
  case cipher =>
    apply stack_writable hPre hgrow <;>
      simp only [Callee100a80.cipherRegion, Callee100a80.cipherBytes, hrdi] <;> omega
  case words =>
    simp only [Callee100a80.wordsRegion, hrdi]
    exact words_of_loads hPre L hgrow
  case position =>
    simp only [Callee100a80.positionRegion, hrdi]
    refine hasBytes_of_memByte (n := 1) rfl ?_ ?_
    · intro i hi; exact hsome _ (by omega) (by omega)
    · intro i hi
      have hi0 : i = 0 := by omega
      subst hi0
      rw [Nat.add_zero, show frameBase s + 0x18 + 0x40 = frameBase s + 0x58 by omega,
        ← Encrypt.framePointer_add_eq hS (by omega), ← BitVec.add_zero (framePointer s + _)]
      rw [show (0#64 : BitVec 64) = BitVec.ofNat 64 0 from rfl, ld_byte L.w58 0 (by decide)]
      rfl
  case buf =>
    refine ⟨by omega, fun i hi => ?_⟩
    rw [show rsi.read v + BitVec.ofNat 64 i = BitVec.ofNat 64 (frameBase s + 0xd0 + i) by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, hrsi, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega]
    exact hsome _ (by omega) (by omega)
  case inPtr =>
    simp only [Callee100a80.inPtrSlot, hrsi]
    exact hword 0xd0 (by decide) L.wd0
  case outPtr =>
    simp only [Callee100a80.outPtrSlot, hrsi, show frameBase s + 0xd0 + 8 = frameBase s + 0xd8 by omega]
    exact hword 0xd8 (by decide) L.wd8
  case length =>
    simp only [Callee100a80.lengthSlot, hrsi, hsz, show frameBase s + 0xd0 + 16 = frameBase s + 0xe0 by omega]
    exact hword 0xe0 (by decide) L.we0
  case messageBytes =>
    simp only [Callee100a80.inputRegion, hin]
    apply hasBytes_of_memByte hsz
    · intro i hi; exact hsome _ (by omega) (by omega)
    · intro i hi
      have hz : zeros32[i]'(by omega) = 0 := by simp [zeros32, ByteArray.getElem_eq_getElem_data]
      rw [hz]
      have split (k j : Nat) (h : k + j = 0xb0 + i) :
          BitVec.ofNat 64 (frameBase s + 0xb0 + i) =
            framePointer s + BitVec.ofNat 64 k + BitVec.ofNat 64 j := by
        rw [addr_assoc, h, Encrypt.framePointer_add_eq hS (by omega), Nat.add_assoc]
      rcases (by omega : i < 8 ∨ (8 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 24) ∨ (24 ≤ i ∧ i < 32))
        with h | h | h | h
      · rw [split 0xb0 i (by omega), ld_byte L.wb0 _ (by omega)]; exact ChaCha20Poly1305.Proofs.Poly1305.Callee101e40.storedByte_zero _ _
      · rw [split 0xb8 (i - 8) (by omega), ld_byte L.wb8 _ (by omega)]; exact ChaCha20Poly1305.Proofs.Poly1305.Callee101e40.storedByte_zero _ _
      · rw [split 0xc0 (i - 16) (by omega), ld_byte L.wc0 _ (by omega)]; exact ChaCha20Poly1305.Proofs.Poly1305.Callee101e40.storedByte_zero _ _
      · rw [split 0xc8 (i - 24) (by omega), ld_byte L.wc8 _ (by omega)]; exact ChaCha20Poly1305.Proofs.Poly1305.Callee101e40.storedByte_zero _ _
  case low => rw [hin, hsz]; omega
  case out =>
    apply stack_writable hPre hgrow <;>
      simp only [Callee100a80.outputRegion, hin, hsz] <;> omega
  case returnLow =>
    simp only [returnBoundary]
    rw [Encrypt.mem_read_eq, stackPtr_eq_read]
    change (ld v (rg v 4) 64).toNat < _
    rw [L.rsp, L.ret]; decide
  case returnOutside =>
    left
    simp only [returnBoundary]
    rw [Encrypt.mem_read_eq, stackPtr_eq_read]
    change (ld v (rg v 4) 64).toNat < _
    rw [L.rsp, L.ret]; decide
  all_goals
    intro x h₁ h₂
    simp only [Callee100a80.inputRegion, Callee100a80.outputRegion, Callee100a80.cipherRegion,
      Callee100a80.stackRegion, Callee100a80.bufRegion, Callee100a80.cipherBytes,
      Callee100a80.frameBytes, MemoryRegion.Contains, hrdi, hrsi, hspv, hin, hsz] at h₁ h₂
    omega

end KeyCall

end ChaCha20Poly1305.Proofs.Core.Setup

namespace ChaCha20Poly1305.Proofs.Core.Setup


open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem ipt_memStore {m : Ram} (h : IdentityPageTableMemory m)
    (addr : BitVec 64) {n : Nat} (v : BitVec n) (hlow : addr.toNat + n / 8 ≤ 2^32)
    (htables : addr.toNat + n / 8 ≤ 0x1000 ∨ 0x2020 ≤ addr.toNat) :
    IdentityPageTableMemory (X86Proofs.memStore m addr v) := by
  have hf (x : Nat) (hx : (0x1000 ≤ x ∧ x < 0x1008) ∨ (0x2000 ≤ x ∧ x < 0x2020)) :
      (X86Proofs.memStore m addr v)[BitVec.ofNat 64 x]? = m[BitVec.ofNat 64 x]? := by
    apply memStore_getElem?_of_ne
    intro i hi he
    have := congrArg BitVec.toNat he
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat] at this
    rw [Nat.mod_eq_of_lt (a := i) (by omega), Nat.mod_eq_of_lt (by omega),
      Nat.mod_eq_of_lt (by omega)] at this
    omega
  refine ⟨fun i => ?_, fun page i => ?_⟩
  · rw [hf _ (by have := i.isLt; omega)]; exact h.1 i
  · rw [hf _ (by have := i.isLt; have := page.isLt; omega)]; exact h.2 page i

theorem readyMidRep_repMovs [Bindings] {s : RamState} (h : ReadyMidRep s) (n len : Nat)
    (hdst : (rdi.read s).toNat + n / 8 ≤ 2^32)
    (htables : (rdi.read s).toNat + n / 8 ≤ 0x1000 ∨ 0x2020 ≤ (rdi.read s).toNat) :
    ReadyMidRep (repMovsAfter n len s) := by
  have htab : IdentityPageTableMemory (clearRep (repMovsAfter n len s)).external := by
    rw [clearRep_external, repMovsAfter_external]
    exact ipt_memStore (ReadyToStep.memory (s := clearRep s) h).tables _ _
      hdst htables
  have : ReadyToStep (clearRep (repMovsAfter n len s)) :=
    ReadyToStep.of_agreesExcept h.clear (AgreesExcept.repMovs n len s) htab
  exact this


structure MovsdLoop [Bindings] (s : RamState) (count : Nat) : Prop where
  ready : ReadyMidRep s
  df : DirectionFlagClear s.RFLAGS
  code : BytesAt s s.RIP [0xF3, 0xA5]
  codeLow : s.RIP.toNat + 2 ≤ 2^32
  counter : rcx.read s = BitVec.ofNat 64 count
  srcLow : (rsi.read s).toNat + 4 * count ≤ 2^32
  dstLow : (rdi.read s).toNat + 4 * count ≤ 2^32
  dstAlign : (rdi.read s).toNat % 4 = 0
  srcMem : ∀ i < 4 * count, (s.external[rsi.read s + BitVec.ofNat 64 i]?).isSome
  dstMem : ∀ i < 4 * count, (s.external[rdi.read s + BitVec.ofNat 64 i]?).isSome
  disjoint : (rsi.read s).toNat + 4 * count ≤ (rdi.read s).toNat ∨
    (rdi.read s).toNat + 4 * count ≤ (rsi.read s).toNat
  dstTables : (rdi.read s).toNat + 4 * count ≤ 0x1000 ∨ 0x2020 ≤ (rdi.read s).toNat
  dstCode : RangeApart (rdi.read s) (4 * count) s.RIP 2

theorem MovsdLoop.rcx_ne [Bindings] {s : RamState} {count : Nat}
    (h : MovsdLoop s count) (hpos : 0 < count) : rcx.read s ≠ 0 := by
  rw [h.counter]
  exact ofNat_ne_zero hpos (by have := h.dstLow; omega)

theorem MovsdLoop.step [inst : Bindings] (hstride : Prelude.UnitStringStride inst) {s : RamState}
    {count : Nat} (h : MovsdLoop s count) (hpos : 0 < count) :
    X86.Machine.step s = some (.next (repMovsAfter 32 2 s)) := by
  have := h.dstLow
  have := h.dstAlign
  have := h.srcLow
  exact rep_movsd_step hstride s h.ready [0xF3] (by simpa using scanPrefix_f3) (by simp)
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    rfl
    h.df h.code h.codeLow (h.rcx_ne hpos)
    ⟨by omega, fun i hi => h.srcMem i (by omega)⟩
    ⟨by omega, fun i hi => h.dstMem i (by omega), by
      have := h.dstTables; simp only [PageTableEntriesApart]; omega⟩

theorem MovsdLoop.rcx_after [Bindings] {s : RamState} {count : Nat}
    (h : MovsdLoop s (count + 1)) : rcx.read (repMovsAfter 32 2 s) = BitVec.ofNat 64 count := by
  rw [repMovsAfter_rcx, h.counter, ofNat_succ_sub_one]

theorem MovsdLoop.source_frame [Bindings] {s : RamState} {count : Nat}
    (h : MovsdLoop s count) (j : Nat) (hj : j < 4 * count) :
    (repMovsAfter 32 2 s).external[rsi.read s + BitVec.ofNat 64 j]? =
      s.external[rsi.read s + BitVec.ofNat 64 j]? := by
  rw [repMovsAfter_external]
  apply memStore_getElem?_of_ne
  intro i hi he
  have hn := congrArg BitVec.toNat he
  have := h.srcLow
  have := h.dstLow
  have := h.disjoint
  rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at hn
  omega

theorem MovsdLoop.next [Bindings] {s : RamState} {count : Nat}
    (h : MovsdLoop s (count + 2)) : MovsdLoop (repMovsAfter 32 2 s) (count + 1) := by
  have hsl := h.srcLow
  have hdl := h.dstLow
  have hal := h.dstAlign
  have hrip : (repMovsAfter 32 2 s).RIP = s.RIP := by
    rw [repMovsAfter_rip 32 2 s h.ready.msr, h.counter]
    simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := count + 1) (by omega) (by omega), ↓reduceIte]
  have hs : rsi.read (repMovsAfter 32 2 s) = rsi.read s + BitVec.ofNat 64 4 := repMovsAfter_rsi 32 2 s
  have hd : rdi.read (repMovsAfter 32 2 s) = rdi.read s + BitVec.ofNat 64 4 := repMovsAfter_rdi 32 2 s
  have hsn : (rsi.read (repMovsAfter 32 2 s)).toNat = (rsi.read s).toNat + 4 := by
    rw [hs, toNat_add_ofNat _ _ (by omega)]
  have hdn : (rdi.read (repMovsAfter 32 2 s)).toNat = (rdi.read s).toNat + 4 := by
    rw [hd, toNat_add_ofNat _ _ (by omega)]
  refine ⟨readyMidRep_repMovs h.ready 32 2 (by omega) (by have := h.dstTables; omega), h.df, ?_, ?_,
    h.rcx_after, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i hi
    rw [hrip, repMovsAfter_external, memStore_getElem?_of_ne]
    · exact h.code i hi
    · intro j hj he
      exact h.dstCode j (by omega) i (by simpa using hi) he
  · rw [hrip]; exact h.codeLow
  · rw [hsn]; omega
  · rw [hdn]; omega
  · rw [hdn]; omega
  · intro i hi
    rw [hs, add_ofNat_add_ofNat, h.source_frame (4 + i) (by omega)]
    exact h.srcMem (4 + i) (by omega)
  · intro i hi
    rw [hd, add_ofNat_add_ofNat, repMovsAfter_external]
    exact memStore_isSome _ _ _ _ (h.dstMem (4 + i) (by omega))
  · rw [hsn, hdn]; have := h.disjoint; omega
  · rw [hdn]; have := h.dstTables; omega
  · intro i hi j hj
    rw [hd, add_ofNat_add_ofNat, hrip]
    exact h.dstCode (4 + i) (by omega) j hj

structure MovsdDone [Bindings] (s t : RamState) (count : Nat) : Prop where
  ready : ReadyToStep t
  rip : t.RIP = BitVec.add s.RIP (BitVec.ofNat 64 2)
  rcxZero : rcx.read t = 0
  rsiAfter : rsi.read t = rsi.read s + BitVec.ofNat 64 (4 * count)
  rdiAfter : rdi.read t = rdi.read s + BitVec.ofNat 64 (4 * count)
  copy : ∀ i < 4 * count,
    t.external[rdi.read s + BitVec.ofNat 64 i]? = s.external[rsi.read s + BitVec.ofNat 64 i]?
  agrees : AgreesExcept [.reg 1, .reg 6, .reg 7, .mem (rdi.read s) (4 * count), .rip] (clearRep s) t

theorem movsd_loop [inst : Bindings] (hstride : Prelude.UnitStringStride inst) (count : Nat)
    (s : RamState) (h : MovsdLoop s (count + 1)) :
    MovsdDone s (nextStates (count + 1) s) (count + 1) := by
  induction count generalizing s with
  | zero =>
    have hnext : nextState s = (repMovsAfter 32 2 s) :=
      nextState_of_step (h.step hstride (by omega))
    have hsl := h.srcLow
    have hdl := h.dstLow
    rw [nextStates_succ, hnext, nextStates_zero]
    have hc : rcx.read s - 1 = 0 := by
      rw [h.counter]; rfl
    have hflag : (repMovsAfter 32 2 s).Repeat_String_Operation = false := by
      rw [repMovsAfter_repeat, hc]; rfl
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact (readyMidRep_repMovs h.ready 32 2 (by omega) (by have := h.dstTables; omega)).ready hflag
    · rw [repMovsAfter_rip 32 2 s h.ready.msr, hc]; rfl
    · rw [repMovsAfter_rcx, hc]
    · exact repMovsAfter_rsi 32 2 s
    · exact repMovsAfter_rdi 32 2 s
    · intro i hi
      exact repMovsAfter_copy 32 2 s (by decide) i (by omega) (h.srcMem i (by omega))
    · rw [← clearRep_eq hflag]
      exact AgreesExcept.repMovs 32 2 s
  | succ m ih =>
    have hnext : nextState s = (repMovsAfter 32 2 s) :=
      nextState_of_step (h.step hstride (by omega))
    have hsl := h.srcLow
    have hdl := h.dstLow
    have hs : rsi.read (repMovsAfter 32 2 s) = rsi.read s + BitVec.ofNat 64 4 := repMovsAfter_rsi 32 2 s
    have hd : rdi.read (repMovsAfter 32 2 s) = rdi.read s + BitVec.ofNat 64 4 := repMovsAfter_rdi 32 2 s
    have hfirst (i : Nat) (hi : i < 4) :
        (repMovsAfter 32 2 s).external[rdi.read s + BitVec.ofNat 64 i]? =
          s.external[rsi.read s + BitVec.ofNat 64 i]? :=
      repMovsAfter_copy 32 2 s (by decide) i hi (h.srcMem i (by omega))
    have ih' := ih (repMovsAfter 32 2 s) h.next
    rw [nextStates_succ, hnext]
    have hrip : (repMovsAfter 32 2 s).RIP = s.RIP := by
      rw [repMovsAfter_rip 32 2 s h.ready.msr, h.counter]
      simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := m + 1) (by omega) (by omega), ↓reduceIte]
    refine ⟨ih'.ready, by rw [ih'.rip, hrip], ih'.rcxZero, ?_, ?_, ?_, ?_⟩
    · rw [ih'.rsiAfter, hs, add_ofNat_add_ofNat]; congr 2; omega
    · rw [ih'.rdiAfter, hd, add_ofNat_add_ofNat]; congr 2; omega
    · intro i hi
      by_cases hsmall : i < 4
      · refine (ih'.agrees.byte ?_).trans ((clearRep_external _).symm ▸ hfirst i hsmall)
        intro c hc hcov
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl <;> try exact hcov
        obtain ⟨j, hj, he⟩ := hcov
        rw [hd, add_ofNat_add_ofNat] at he
        have hn := congrArg BitVec.toNat he
        rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)] at hn
        omega
      · have hc := ih'.copy (i - 4) (by omega)
        rw [hd, hs, add_ofNat_add_ofNat, add_ofNat_add_ofNat, Nat.add_sub_cancel' (by omega),
          h.source_frame i (by omega)] at hc
        exact hc
    · refine (AgreesExcept.repMovs 32 2 s |>.trans ih'.agrees).widen ?_ ?_
      · intro c hc hm
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          simp_all [Component.isMem]
      · intro x c hc hcov
        refine ⟨.mem (rdi.read s) (4 * (m + 1 + 1)), by simp, ?_⟩
        simp only [List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil,
          or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          try exact absurd hcov id
        · obtain ⟨j, hj, he⟩ := hcov
          exact ⟨j, by omega, he⟩
        · obtain ⟨j, hj, he⟩ := hcov
          rw [hd, add_ofNat_add_ofNat] at he
          exact ⟨4 + j, by omega, he⟩

theorem MovsdLoop.advances [inst : Bindings] (hstride : Prelude.UnitStringStride inst)
    (boundary : ReturnBoundary) (count : Nat) (s : RamState) (h : MovsdLoop s (count + 1))
    (hstart : s.RIP ≠ boundary.rip) (hend : BitVec.add s.RIP (BitVec.ofNat 64 2) ≠ boundary.rip) :
    Advances boundary (count + 1) s (nextStates (count + 1) s) := by
  induction count generalizing s with
  | zero =>
    have hs := h.step hstride (by omega)
    have hi : (repMovsAfter 32 2 s).RIP ≠ boundary.rip := by
      rw [repMovsAfter_rip 32 2 s h.ready.msr]
      split <;> assumption
    rw [nextStates_one, nextState_of_step hs]
    exact Advances.of_step hs (.inl hi)
  | succ k ih =>
    have hs := h.step hstride (by omega)
    have hsl := h.srcLow
    have hrip : (repMovsAfter 32 2 s).RIP = s.RIP := by
      rw [repMovsAfter_rip 32 2 s h.ready.msr, h.counter]
      simp only [ofNat_succ_sub_one, ofNat_ne_zero (c := k + 1) (by omega) (by omega), ↓reduceIte]
    have ha : Advances boundary 1 s (repMovsAfter 32 2 s) :=
      Advances.of_step hs (.inl (by rw [hrip]; exact hstart))
    have hb := ih (repMovsAfter 32 2 s) h.next (by rw [hrip]; exact hstart)
      (by rw [hrip]; exact hend)
    rw [nextStates_succ, nextState_of_step hs]
    simpa only [Nat.add_comm 1 (k + 1)] using ha.trans hb

end ChaCha20Poly1305.Proofs.Core.Setup

namespace ChaCha20Poly1305.Proofs.Core.Setup


open ChaCha20Poly1305.Spec.Program Standards.RFC.ChaCha20Poly1305 Prelude X86 X86.Machine
open X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CoreContract
open ChaCha20Poly1305.Proofs.MemoryRoutines.Machine

section AfterKey

variable [bindings : Machine.Bindings] {s : RamState} {key : Vector UInt8 32}
  {nonce : Vector UInt8 12} {associatedData plaintext : ByteArray} {inPtr outPtr : BitVec 64}

def W100 (s : RamState) (x : Nat) : Prop :=
  Win s 0xb0 0xd0 x ∨ Win s 0x48 0x4c x ∨ Win s 0x58 0x98 x ∨
    (frameBase s - 0x1a8 ≤ x ∧ x < frameBase s)

omit bindings in
theorem key_same (hS : Encrypt.StackFacts s) {v w : RamState}
    (hrdi : (rdi.read v).toNat = frameBase s + 0x18) (hspv : (stackPtr v).toNat = frameBase s - 8)
    (hag : AgreesExcept (Callee100a80.callChanges v (framePointer s + 176#64) zeros32.size) v w) :
    Encrypt.Same (W100 s) v w := by
  have := hS.room
  have := hS.top
  have hin : (framePointer s + 176#64).toNat = frameBase s + 0xb0 := fp_toNat' hS (by decide)
  have hsz := zeros32_size
  have h30 : (0x30 : BitVec 64).toNat = 0x30 := rfl
  have h40 : (0x40 : BitVec 64).toNat = 0x40 := rfl
  apply Encrypt.Same.of_agrees hag
  intro c hc
  simp only [Callee100a80.callChanges, Callee100a80.frameBytes, List.mem_cons,
    List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl
  any_goals exact fun x hx => absurd hx (Encrypt.nonmem_not_covers rfl x)
  all_goals rintro x ⟨j, hj, rfl⟩
  all_goals simp only [BitVec.toNat_add, BitVec.toNat_sub, BitVec.toNat_ofNat, hrdi, hspv,
    h30, h40, hin, hsz] at hj ⊢
  all_goals simp only [W100, Win]
  all_goals unfold frameBase frameBytes at *
  all_goals omega


theorem stack_vs_program (hPre : CorePre s key nonce associatedData plaintext inPtr outPtr) :
    (stackPtr s).toNat + 8 ≤ 0x100000 ∨ 0x100000 + 11759 ≤ (stackPtr s).toNat - 992 := by
  have hS := Encrypt.stack_facts hPre
  have := hS.room
  have := hS.top
  refine Classical.byContradiction fun hc => ?_
  have hx : max ((stackPtr s).toNat - 992) 0x100000 < 2 ^ 64 := by omega
  apply hS.outside (BitVec.ofNat 64 (max ((stackPtr s).toNat - 992) 0x100000))
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx]; omega
  · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx]; omega
  · apply Encrypt.inProgram_of_toNat <;> rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx] <;> omega

theorem frame_storePre (hPre : CorePre s key nonce associatedData plaintext inPtr outPtr)
    {u : RamState} (hgrow : ∀ x : BitVec 64, (s.external[x]?).isSome → (u.external[x]?).isSome)
    {p : BitVec 64} {codeLen n : Nat} (hrip : u.RIP = p)
    (hp : 0x100000 ≤ p.toNat ∧ p.toNat + codeLen ≤ 0x100000 + 11759)
    {addr : RamState → BitVec 64} {a : BitVec 64} (ha : addr u = a)
    (h₁ : (stackPtr s).toNat - 992 ≤ a.toNat) (h₂ : a.toNat + n ≤ (stackPtr s).toNat + 8) :
    StorePre p codeLen addr n u := by
  have hS := Encrypt.stack_facts hPre
  have := hS.top
  have htab := hS.tables
  have hsp := stack_vs_program hPre
  refine ⟨hrip, ha ▸ ⟨by omega, fun i hi => ?_, by simp only [PageTableEntriesApart]; omega⟩,
    ha ▸ RangeApart.of_toNat (by omega) (by omega) (by omega)⟩
  rw [show a + BitVec.ofNat 64 i = BitVec.ofNat 64 (a.toNat + i) by
    apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega]
  exact frame_some hPre hgrow _ (by omega) (by omega)

theorem stack_av (hPre : CorePre s key nonce associatedData plaintext inPtr outPtr)
    {a : BitVec 64} {n : Nat} (h₁ : (stackPtr s).toNat - 992 ≤ a.toNat)
    (h₂ : a.toNat + n ≤ (stackPtr s).toNat + 8) :
    ∀ x, (Component.mem a n).Covers x → ¬ InProgram x := by
  have hS := Encrypt.stack_facts hPre
  have := hS.top
  apply Encrypt.mem_av (by omega)
  intro x hx₁ hx₂
  exact hS.outside x (by omega) (by omega)

structure AtPoly (s v w : RamState) (key : Vector UInt8 32) (nonce : Vector UInt8 12) : Prop where
  rip : w.RIP = 0x101e40
  rsp : rg w 4 = framePointer s - BitVec.ofNat 64 8
  rdi : rg w 7 = framePointer s + BitVec.ofNat 64 0x150
  rsi : rg w 6 = framePointer s + BitVec.ofNat 64 0xb0
  rbx : rg w 3 = lengthLimit
  r15 : rg w 15 = framePointer s + BitVec.ofNat 64 0x150
  rbp : rg w 5 = rg v 5
  r12 : rg w 12 = rg v 12
  r13 : rg w 13 = rg v 13
  r14 : rg w 14 = rg v 14
  ret : ld w (framePointer s - BitVec.ofNat 64 8) 64 = 0x10080b
  same : Encrypt.Same (W100 s) v w
  otk : (⟨frameBase s + 0xb0, 32⟩ : MemoryRegion).HasBytes w.external
    (chacha20Encrypt key 0 nonce zeros32)
  grow : ∀ x : BitVec 64, (v.external[x]?).isSome → (w.external[x]?).isSome
  df : DirectionFlagUnset w
  sse : SupportedSSE bindings.processor w

omit bindings in
theorem slice_at {u : RamState} (hc : CodeIn Extracted.programImage u) (off cnt : Nat)
    {p : BitVec 64} {bytes : List UInt8} (h1 : off + cnt ≤ Extracted.textBytes.size)
    (hp : Extracted.textAddress + BitVec.ofNat 64 off = p)
    (hb : Extracted.textBytes.toListFrom off cnt = bytes) : CodeIn (codeRange p bytes) u :=
  slice_code hc off cnt h1 hp hb

set_option maxHeartbeats 4000000 in
theorem after_key (hPre : CorePre s key nonce associatedData plaintext inPtr outPtr)
    {boundary : ReturnBoundary} (hOut : ¬ InProgram boundary.rip) {v w0 : RamState}
    (L : Loads s v) (hdf : DirectionFlagUnset v) (hsse : SupportedSSE bindings.processor v)
    (hgrow : ∀ x : BitVec 64, (s.external[x]?).isSome → (v.external[x]?).isSome)
    (hR : Callee100a80.CallResult v w0 key 0 nonce (framePointer s + 176#64) zeros32) :
    ∃ fuel w, Advances boundary fuel w0 w ∧ ReadyToStep w ∧ CodeIn Extracted.programImage w ∧
      AtPoly s v w key nonce := by
  have hS := Encrypt.stack_facts hPre
  have hroom := hS.room
  have htop := hS.top
  have hFB : frameBase s = (stackPtr s).toNat - 0x1b8 := rfl
  have hspv : (stackPtr v).toNat = frameBase s - 8 := by
    rw [stackPtr_eq_read]; change (rg v 4).toNat = _; rw [L.rsp]
    exact Encrypt.framePointer_sub_toNat hS (by decide)
  have hrdi : (rdi.read v).toNat = frameBase s + 0x18 := by
    change (rg v 7).toNat = _; rw [L.rdi]; exact fp_toNat' hS (by decide)
  have hRet : (returnBoundary v).rip = 0x1007e1 := by
    simp only [returnBoundary]
    rw [Encrypt.mem_read_eq, stackPtr_eq_read]
    change ld v (rg v 4) 64 = _
    rw [L.rsp, L.ret]; rfl
  have hAcc : Callee100a80.Accepted 0 zeros32.size := by
    unfold Callee100a80.Accepted; rw [zeros32_size]; decide
  have hst := hR.status
  simp only [hAcc, ↓reduceIte] at hst
  obtain ⟨hal, hct⟩ := hst
  have hsp0 : rg w0 4 = framePointer s := by
    have := hR.rsp
    rw [stackPtr_eq_read, stackPtr_eq_read] at this
    change rg w0 4 = rg v 4 + 8 at this
    rw [this, L.rsp]; exact BitVec.sub_add_cancel _ _
  obtain ⟨w1, b1, r1, c1, g1⟩ := Encrypt.step_run (boundary := boundary)
    (test_r8_r8_effect_step 0x1007e1 0xc0 (by decide) (by decide) (by decide))
    hR.ready hR.code (slice_at hR.code 0x7e1 2 (by decide +kernel) (by decide) (by decide +kernel))
    (hR.rip.trans hRet) (Encrypt.ne_boundary hOut 0x1007e3 ⟨by decide, by decide⟩)
    (Encrypt.regs_av (by simp [Component.isMem]))
  change (testR8R8Effect 0x1007e1 2 0 0 w0).Holds w0 w1 at g1
  have hZF : (StatusFlags.ofRFLAGS w1.RFLAGS).ZF = true := by
    obtain ⟨-, -, -, hZ, -⟩ := g1.flags
    have h0 : (Operand.reg 0 : Operand 8).read w0 = 0 := hal
    simp only [testFlags, FlagAllows, h0] at hZ
    rw [hZ]; rfl
  have hj : (jccEffect 0x1007e3 6 5 ((0x22a : BitVec 32).signExtend 64) w1).rip = 0x1007e9 := by
    simp only [jccEffect, branchEffect, condHolds_5, hZF]; rfl
  obtain ⟨w2, b2, r2, c2, g2⟩ := Encrypt.step_run (boundary := boundary)
    (jcc_rel32_effect_step 0x1007e3 5 0x22a)
    r1 c1 (slice_at c1 0x7e3 6 (by decide +kernel) (by decide) (by decide +kernel))
    ⟨g1.rip, fun h => by rw [condHolds_5, hZF] at h; exact absurd h (by decide)⟩
    (by rw [hj]; exact Encrypt.ne_boundary hOut 0x1007e9 ⟨by decide, by decide⟩)
    (Encrypt.regs_av (by simp (config := { decide := true }) [Component.isMem, jccEffect]))
  have hsp1 : rg w1 4 = framePointer s :=
    (rg_keep g1.agrees (by simp (config := { decide := true }) [testR8R8Effect, Effect.components])).trans hsp0
  have hsp2 : rg w2 4 = framePointer s :=
    (rg_keep g2.agrees (by simp (config := { decide := true }) [jccEffect, branchEffect, Effect.components])).trans hsp1
  obtain ⟨w3, b3, r3, c3, g3⟩ := Encrypt.step_run (boundary := boundary)
    (mov_r64_imm64_effect_step 0x1007e9 0x48 0xbb (by unfold RexWPrefix; decide) (by decide)
      0x3fffffffbf)
    r2 c2 (slice_at c2 0x7e9 10 (by decide +kernel) (by decide) (by decide +kernel))
    (g2.rip.trans hj) (Encrypt.ne_boundary hOut 0x1007f3 ⟨by decide, by decide⟩)
    (Encrypt.regs_av (by simp (config := { decide := true }) [Component.isMem, movR64Imm64Effect, Effect.components]))
  have hsp3 : rg w3 4 = framePointer s :=
    (rg_keep g3.agrees (by simp (config := { decide := true }) [movR64Imm64Effect, Effect.components])).trans hsp2
  have hbx3 : rg w3 3 = lengthLimit := g3.writes
  obtain ⟨w4, b4, r4, c4, g4⟩ := Encrypt.step_run (boundary := boundary)
    (lea_r64_effect_step 0x1007f3 0x4c (by unfold RexWPrefix; decide) 7
      (.sib 4 none 0 (.d32 0x150)) (by decide) (by decide) (by decide))
    r3 c3 (slice_at c3 0x7f3 8 (by decide +kernel) (by decide) (by decide +kernel))
    g3.rip (Encrypt.ne_boundary hOut 0x1007fb ⟨by decide, by decide⟩)
    (Encrypt.regs_av (by simp (config := { decide := true }) [Component.isMem, leaR64Effect, Effect.components]))
  have hsp4 : rg w4 4 = framePointer s :=
    (rg_keep g4.agrees (by simp (config := { decide := true }) [leaR64Effect, Effect.components])).trans hsp3
  have h15 : rg w4 15 = framePointer s + BitVec.ofNat 64 0x150 := by
    have e : rg w4 15 = (AddrMode.sib 4 none 0 (.d32 0x150)).addr w3
      (0x1007f3 + BitVec.ofNat 64 (leaLen (.sib 4 none 0 (.d32 0x150)))) := g4.writes
    rw [e, Encrypt.sib_rsp_addr, stackPtr_eq_read]
    change rg w3 4 + _ = _
    rw [hsp3]; rfl
  obtain ⟨w5, b5, r5, c5, g5⟩ := Encrypt.step_run (boundary := boundary)
    (lea_r64_effect_step 0x1007fb 0x48 (by unfold RexWPrefix; decide) 6
      (.sib 4 none 0 (.d32 0xb0)) (by decide) (by decide) (by decide))
    r4 c4 (slice_at c4 0x7fb 8 (by decide +kernel) (by decide) (by decide +kernel))
    g4.rip (Encrypt.ne_boundary hOut 0x100803 ⟨by decide, by decide⟩)
    (Encrypt.regs_av (by simp (config := { decide := true }) [Component.isMem, leaR64Effect, Effect.components]))
  have hsp5 : rg w5 4 = framePointer s :=
    (rg_keep g5.agrees (by simp (config := { decide := true }) [leaR64Effect, Effect.components])).trans hsp4
  have h6 : rg w5 6 = framePointer s + BitVec.ofNat 64 0xb0 := by
    have e : rg w5 6 = (AddrMode.sib 4 none 0 (.d32 0xb0)).addr w4
      (0x1007fb + BitVec.ofNat 64 (leaLen (.sib 4 none 0 (.d32 0xb0)))) := g5.writes
    rw [e, Encrypt.sib_rsp_addr, stackPtr_eq_read]
    change rg w4 4 + _ = _
    rw [hsp4]; rfl
  obtain ⟨w6, b6, r6, c6, g6⟩ := Encrypt.step_run (boundary := boundary)
    (mov_r64_r64_effect_step 0x100803 0x4c 0xff (by unfold RexWPrefix; decide) (by decide))
    r5 c5 (slice_at c5 0x803 3 (by decide +kernel) (by decide) (by decide +kernel))
    g5.rip (Encrypt.ne_boundary hOut 0x100806 ⟨by decide, by decide⟩)
    (Encrypt.regs_av (by simp (config := { decide := true }) [Component.isMem, movR64R64Effect, Effect.components]))
  have hsp6 : rg w6 4 = framePointer s :=
    (rg_keep g6.agrees (by simp (config := { decide := true }) [movR64R64Effect, Effect.components])).trans hsp5
  have h7 : rg w6 7 = framePointer s + BitVec.ofNat 64 0x150 := by
    have e : rg w6 7 = rg w5 15 := g6.writes
    rw [e, rg_keep g5.agrees (r := 15) (by simp (config := { decide := true }) [leaR64Effect, Effect.components]), h15]
  have hagW := g1.agrees.trans (g2.agrees.trans (g3.agrees.trans (g4.agrees.trans
    (g5.agrees.trans g6.agrees))))
  have hgrow6 : ∀ x : BitVec 64, (s.external[x]?).isSome → (w6.external[x]?).isSome :=
    fun x hx => hagW.grow x (hR.agrees.grow x (hgrow x hx))
  have hfm8 : (framePointer s - BitVec.ofNat 64 8).toNat = frameBase s - 8 :=
    Encrypt.framePointer_sub_toNat hS (by decide)
  have hpa : pushAddr w6 = framePointer s - BitVec.ofNat 64 8 := by
    rw [pushAddr, stackPtr_eq_read]; change rg w6 4 - 8 = _; rw [hsp6]; rfl
  have hpre7 : PushPre 0x100806 5 w6 :=
    frame_storePre hPre hgrow6 (p := 0x100806) g6.rip ⟨by decide, by decide⟩ hpa
      (by rw [hfm8]; unfold frameBase frameBytes; omega)
      (by rw [hfm8]; unfold frameBase frameBytes; omega)
  obtain ⟨w7, b7, r7, c7, g7⟩ := Encrypt.step_run (boundary := boundary)
    (call_rel32_effect_step 0x100806 0x1635 (by decide))
    r6 c6 (slice_at c6 0x806 5 (by decide +kernel) (by decide) (by decide +kernel))
    hpre7 (Encrypt.ne_boundary hOut 0x101e40 ⟨by decide, by decide⟩) (by
      intro c hc
      simp only [callEffect, pushEffect_components, List.mem_cons, List.not_mem_nil,
        or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact fun x hx => absurd hx (Encrypt.nonmem_not_covers rfl x)
      · rw [hpa]
        exact stack_av hPre (by rw [hfm8]; unfold frameBase frameBytes; omega)
          (by rw [hfm8]; unfold frameBase frameBytes; omega)
      · exact fun x hx => absurd hx (Encrypt.nonmem_not_covers rfl x))
  obtain ⟨g7a, g7b⟩ := g7.writes
  have hall := hagW.trans g7.agrees
  have hkeep {cs : List Component} (hag : AgreesExcept cs w0 w7) (r : BitVec 5)
      (hr : Component.reg r ∉ Callee100a80.callChanges v (framePointer s + 176#64) zeros32.size)
      (hr' : Component.reg r ∉ cs) : rg w7 r = rg v r := by
    rw [rg_keep hag hr', rg_keep hR.agrees hr]
  have hsameV : Encrypt.Same (W100 s) v w0 := key_same hS hrdi hspv hR.agrees
  have hsame0 : Encrypt.Same (WinK s) w0 w7 := by
    refine (Encrypt.same_of_regs hagW (by
      simp (config := { decide := true }) [testR8R8Effect, jccEffect, branchEffect,
        movR64Imm64Effect, leaR64Effect, movR64R64Effect, Effect.components, Component.isMem])).trans ?_
    apply Encrypt.Same.of_agrees g7.agrees
    intro c hc
    simp only [callEffect, pushEffect_components, List.mem_cons, List.not_mem_nil,
      or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact fun x hx => absurd hx (Encrypt.nonmem_not_covers rfl x)
    · rw [hpa]
      refine Encrypt.mem_within (by rw [hfm8]; unfold frameBase frameBytes; omega) ?_
      intro j hj; rw [hfm8]; simp only [WinK]; omega
    · exact fun x hx => absurd hx (Encrypt.nonmem_not_covers rfl x)
  refine ⟨_, w7, b1.trans (b2.trans (b3.trans (b4.trans (b5.trans (b6.trans b7))))), r7, c7,
    ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, hsameV.trans (hsame0.mono fun x hx => by
      simp only [WinK] at hx; simp only [W100]; omega), ?_, ?_, ?_, ?_⟩⟩
  · rw [g7.rip]; rfl
  · rw [show rg w7 4 = pushAddr w6 from g7a, hpa]
  · rw [rg_keep g7.agrees (r := 7) (by simp [callEffect, pushEffect, Effect.components]), h7]
  · rw [rg_keep g7.agrees (r := 6) (by simp [callEffect, pushEffect, Effect.components]),
      rg_keep g6.agrees (r := 6) (by simp (config := { decide := true }) [movR64R64Effect, Effect.components]), h6]
  · rw [rg_keep g7.agrees (r := 3) (by simp [callEffect, pushEffect, Effect.components]),
      rg_keep g6.agrees (r := 3) (by simp (config := { decide := true }) [movR64R64Effect, Effect.components]),
      rg_keep g5.agrees (r := 3) (by simp (config := { decide := true }) [leaR64Effect, Effect.components]),
      rg_keep g4.agrees (r := 3) (by simp (config := { decide := true }) [leaR64Effect, Effect.components]), hbx3]
  · rw [rg_keep g7.agrees (r := 15) (by simp [callEffect, pushEffect, Effect.components]),
      rg_keep g6.agrees (r := 15) (by simp (config := { decide := true }) [movR64R64Effect, Effect.components]),
      rg_keep g5.agrees (r := 15) (by simp (config := { decide := true }) [leaR64Effect, Effect.components]), h15]
  · exact hkeep hall 5 (by simp [Callee100a80.callChanges]) (by
      simp (config := { decide := true }) [testR8R8Effect, jccEffect, branchEffect,
        movR64Imm64Effect, leaR64Effect, movR64R64Effect, callEffect, pushEffect, Effect.components])
  · exact hkeep hall 12 (by simp [Callee100a80.callChanges]) (by
      simp (config := { decide := true }) [testR8R8Effect, jccEffect, branchEffect,
        movR64Imm64Effect, leaR64Effect, movR64R64Effect, callEffect, pushEffect, Effect.components])
  · exact hkeep hall 13 (by simp [Callee100a80.callChanges]) (by
      simp (config := { decide := true }) [testR8R8Effect, jccEffect, branchEffect,
        movR64Imm64Effect, leaR64Effect, movR64R64Effect, callEffect, pushEffect, Effect.components])
  · exact hkeep hall 14 (by simp [Callee100a80.callChanges]) (by
      simp (config := { decide := true }) [testR8R8Effect, jccEffect, branchEffect,
        movR64Imm64Effect, leaR64Effect, movR64R64Effect, callEffect, pushEffect, Effect.components])
  · have e : ld w7 (pushAddr w6) 64 = 0x100806 + BitVec.ofNat 64 5 := g7b
    rw [hpa] at e; rw [e]; rfl
  · have hin : (framePointer s + 176#64).toNat = frameBase s + 0xb0 := fp_toNat' hS (by decide)
    have h := hct
    simp only [Callee100a80.outputRegion, hin, zeros32_size] at h
    exact hsame0.hasBytes h (by dsimp only; omega) (fun x h₁ h₂ => by
      dsimp only at h₁ h₂; simp only [WinK]; omega)
  · intro x hx
    exact hall.grow x (hR.agrees.grow x hx)
  · exact hall.directionFlagClear (by
      simp (config := { decide := true }) [testR8R8Effect, jccEffect, branchEffect,
        movR64Imm64Effect, leaR64Effect, movR64R64Effect, callEffect, pushEffect, Effect.components])
      (hR.agrees.directionFlagClear (by simp [Callee100a80.callChanges]) hdf)
  · exact SupportedSSE.of_agreesExcept hall (SupportedSSE.of_agreesExcept hR.agrees hsse)

end AfterKey

end ChaCha20Poly1305.Proofs.Core.Setup

namespace ChaCha20Poly1305.Proofs.Core.Setup


open ChaCha20Poly1305.Spec.Program Standards.RFC.ChaCha20Poly1305 Prelude X86 X86.Machine
open X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CoreContract
open ChaCha20Poly1305.Proofs.MemoryRoutines.Machine ChaCha20Poly1305.Proofs.Poly1305State

section PolyCall

variable [bindings : Machine.Bindings] {s : RamState} {key : Vector UInt8 32}
  {nonce : Vector UInt8 12} {associatedData plaintext : ByteArray} {inPtr outPtr : BitVec 64}

omit bindings in
theorem otk_byte {m : Ram} {start : Nat} (key : Vector UInt8 32) (nonce : Vector UInt8 12)
    (h : (⟨start, 32⟩ : MemoryRegion).HasBytes m (chacha20Encrypt key 0 nonce zeros32))
    (i : Fin 32) : m[BitVec.ofNat 64 (start + i.val)]? = some (otk key nonce)[i] := by
  rw [keygen] at h
  have := h.2 ⟨i.val, by simp [ByteArray.size]⟩
  rw [this]
  simp [otk, ByteArray.getElem_eq_getElem_data]

set_option maxHeartbeats 4000000 in
theorem polyPre (hPre : CorePre s key nonce associatedData plaintext inPtr outPtr)
    {v w : RamState} (A : AtPoly s v w key nonce)
    (hgrow : ∀ x : BitVec 64, (s.external[x]?).isSome → (v.external[x]?).isSome) :
    Poly1305.Callee101e40.Pre (otk key nonce) w := by
  have hS := Encrypt.stack_facts hPre
  have hroom := hS.room
  have htop := hS.top
  have hFB : frameBase s = (stackPtr s).toNat - 0x1b8 := rfl
  have htab := hS.tables
  have hsp := stack_vs_program hPre
  have hrdi : (rdi.read w).toNat = frameBase s + 0x150 := by
    change (rg w 7).toNat = _; rw [A.rdi]; exact fp_toNat' hS (by decide)
  have hrsi : (rsi.read w).toNat = frameBase s + 0xb0 := by
    change (rg w 6).toNat = _; rw [A.rsi]; exact fp_toNat' hS (by decide)
  have hspw : (stackPtr w).toNat = frameBase s - 8 := by
    rw [stackPtr_eq_read]; change (rg w 4).toNat = _; rw [A.rsp]
    exact Encrypt.framePointer_sub_toNat hS (by decide)
  have hgw : ∀ x : BitVec 64, (s.external[x]?).isSome → (w.external[x]?).isSome :=
    fun x hx => A.grow x (hgrow x hx)
  have hread {a : BitVec 64} {n : Nat} (ha₁ : frameBase s - 8 ≤ a.toNat)
      (ha₂ : a.toNat + n ≤ frameBase s + 0x1c0) : MemReadable w a n := by
    refine ⟨by omega, fun i hi => ?_⟩
    rw [show a + BitVec.ofNat 64 i = BitVec.ofNat 64 (a.toNat + i) by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega]
    exact frame_some hPre hgw _ (by omega) (by omega)
  refine ⟨A.rip, ⟨hread (by omega) (by unfold stateBytes; omega), fun i hi => ?_, fun i hi => ?_⟩,
    hread (by omega) (by omega), fun i => ?_, ?_, hread (by omega) (by omega), ?_, ?_, ?_⟩
  · rw [Common.inPageTables_iff, Encrypt.toNat_add_ofNat (by unfold stateBytes at hi; omega)]
    unfold stateBytes at hi; omega
  · apply hS.outside <;> rw [Encrypt.toNat_add_ofNat (by unfold stateBytes at hi; omega)] <;>
      unfold stateBytes at hi <;> omega
  · rw [show rsi.read w + BitVec.ofNat 64 i.val = BitVec.ofNat 64 (frameBase s + 0xb0 + i.val) by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_add, hrsi, BitVec.toNat_ofNat, BitVec.toNat_ofNat]; omega]
    exact otk_byte key nonce A.otk i
  · unfold stateBytes
    exact RangeApart.of_toNat (by omega) (by omega) (by rw [hrdi, hrsi]; omega)
  · unfold stateBytes
    exact RangeApart.of_toNat (by omega) (by omega) (by rw [hrdi, hspw]; omega)
  · simp only [returnBoundary]
    rw [Encrypt.mem_read_eq, stackPtr_eq_read]
    change (ld w (rg w 4) 64).toNat < _
    rw [A.rsp, A.ret]; decide
  · left
    simp only [returnBoundary]
    rw [Encrypt.mem_read_eq, stackPtr_eq_read]
    change (ld w (rg w 4) 64).toNat < _
    rw [A.rsp, A.ret]; decide

end PolyCall

section AfterPoly

variable [bindings : Machine.Bindings] {s : RamState} {key : Vector UInt8 32}
  {nonce : Vector UInt8 12} {associatedData plaintext : ByteArray} {inPtr outPtr : BitVec 64}

omit bindings in
theorem ldb_loop_isSome {memory : Machine.Ram} {address : BitVec 64}
    {remaining current shift accumulator : Nat} {value : BitVec 64}
    (h : Machine.loadBytes.loop memory address remaining current shift accumulator = .ok value) :
    ∀ i < remaining, (memory[address + BitVec.ofNat 64 (current + i)]?).isSome := by
  induction remaining generalizing current shift accumulator with
  | zero => intro i hi; omega
  | succ remaining ih =>
    cases hbyte : memory[Machine.addAddress address current]? with
    | none => simp only [Machine.loadBytes.loop, hbyte] at h; cases h
    | some byte =>
      simp only [Machine.loadBytes.loop, hbyte] at h
      intro i hi
      cases i with
      | zero =>
        change memory[address + BitVec.ofNat 64 current]? = some byte at hbyte
        simpa only [Nat.add_zero, hbyte] using (show (some byte).isSome = true from rfl)
      | succ i =>
        have hb := ih h i (by omega)
        simpa only [Nat.add_assoc, Nat.add_comm 1 i] using hb

omit bindings in
theorem ldb_isSome {memory : Machine.Ram} {address : BitVec 64} {count : Nat}
    {value : BitVec 64} (h : Machine.loadBytes memory address count = .ok value) :
    ∀ i < count, (memory[address + BitVec.ofNat 64 i]?).isSome := by
  simpa only [Nat.zero_add] using ldb_loop_isSome h

omit bindings in
theorem word64At_ld {region : MemoryRegion} {memory : Machine.Ram} {value : BitVec 64}
    (h : region.Word64At memory value) :
    memLoad memory (BitVec.ofNat 64 region.start) 64 = value := by
  have hb : Bytes memory (BitVec.ofNat 64 region.start) 8
      (storedByte (memLoad memory (BitVec.ofNat 64 region.start) 64)) :=
    Bytes.of_memLoad (n := 64) (ldb_isSome h.2)
  exact Except.ok.inj (hb.loadBytes64.symm.trans h.2)

def Wall (s : RamState) (x : Nat) : Prop := frameBase s - 0x1a8 ≤ x ∧ x < frameBase s + 0x1b8

def WP (s : RamState) (x : Nat) : Prop := frameBase s - 0x1a8 ≤ x ∧ x < frameBase s + 0x188

structure AtCut (s v z : RamState) (key : Vector UInt8 32) (nonce : Vector UInt8 12)
    (plaintext : ByteArray) : Prop where
  rip : z.RIP = 0x10083c
  rsp : rg z 4 = framePointer s
  rbp : rg z 5 = rg v 5
  r12 : rg z 12 = rg v 12
  r13 : rg z 13 = rg v 13
  r14 : rg z 14 = rg v 14
  r15 : rg z 15 = polyBase s
  rbx : rg z 3 = lengthLimit
  rcx : rg z 1 = BitVec.ofNat 64 plaintext.size
  same : Encrypt.Same (WP s) v z
  cipher : (⟨frameBase s + cipherOffset, 0x40⟩ : MemoryRegion).HasBytes z.external
    (cipherWords key nonce)
  position : (⟨frameBase s + cipherOffset + 0x40, 1⟩ : MemoryRegion).HasBytes z.external ⟨#[64]⟩
  poly : PolyState z (polyBase s) (otk key nonce) 0
  grow : ∀ x : BitVec 64, (v.external[x]?).isSome → (z.external[x]?).isSome
  df : DirectionFlagUnset z
  sse : SupportedSSE bindings.processor z

theorem cipher_bytes (hPre : CorePre s key nonce associatedData plaintext inPtr outPtr)
    {v u : RamState} (L : Loads s v)
    (hgrow : ∀ x : BitVec 64, (s.external[x]?).isSome → (v.external[x]?).isSome)
    (Wc : Encrypt.Same (fun y => W100 s y ∨ Win s 0x150 0x188 y ∨ Win s 0x48 0x4c y ∨
      Win s 0x58 0x59 y ∨ Win s 0 0 y) v u)
    (hgu : ∀ y : BitVec 64, (s.external[y]?).isSome → (u.external[y]?).isSome)
    (l12 : ld u (framePointer s + BitVec.ofNat 64 0x48) 32 = 1#32) :
    ∀ j (hj : j < 64), u.external[BitVec.ofNat 64 (frameBase s + 0x18 + j)]? =
      some ((cipherWords key nonce)[j]'(by
        simp only [cipherWords, ByteArray.size, Vector.size_toArray]; omega)) := by
  have hS := Encrypt.stack_facts hPre
  have hroom := hS.room
  have htop := hS.top
  have hFB : frameBase s = (stackPtr s).toNat - 0x1b8 := rfl
  have fp_addr (k i : Nat) (h : k + i ≤ 0x1c0) :
      BitVec.ofNat 64 (frameBase s + k + i) =
        framePointer s + BitVec.ofNat 64 k + BitVec.ofNat 64 i := by
    rw [addr_assoc, Encrypt.framePointer_add_eq hS h, Nat.add_assoc]
  have hwords := words_of_loads hPre L hgrow
  intro j hj
  by_cases hc : 48 ≤ j ∧ j < 52
  · obtain ⟨i, rfl⟩ : ∃ i, j = 48 + i := ⟨j - 48, by omega⟩
    apply some_of_memByte (frame_some hPre hgu _ (by omega) (by omega))
    rw [show frameBase s + 0x18 + (48 + i) = frameBase s + 0x48 + i by omega,
      fp_addr 0x48 i (by omega), ld_byte l12 i (by omega)]
    have hc' := Callee100a80.stateBytes_counter key 1 nonce i (by omega)
      (by simp only [Callee100a80.stateBytes, ByteArray.size, Vector.size_toArray]; omega)
    exact hc'.symm
  · have hx' : u.external[BitVec.ofNat 64 (frameBase s + 0x18 + j)]? =
        v.external[BitVec.ofNat 64 (frameBase s + 0x18 + j)]? := by
      apply Wc
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      simp only [W100, Win]; omega
    have hjs : j < (Callee100a80.stateBytes key 0 nonce).size := by
      simp only [Callee100a80.stateBytes, ByteArray.size, Vector.size_toArray]; omega
    have hw := hwords.2 ⟨j, hjs⟩
    rw [hx', hw]
    refine congrArg some ?_
    rw [stateBytes_get key 0 nonce j hj]
    change _ = (Callee100a80.stateBytes key 1 nonce)[j]'(by
      simp only [Callee100a80.stateBytes, ByteArray.size, Vector.size_toArray]; omega)
    rw [stateBytes_get key 1 nonce j hj]
    rcases (by omega : j < 16 ∨ (16 ≤ j ∧ j < 48) ∨ 52 ≤ j) with h | h | h
    · rw [serialize_const key 0 nonce j h, serialize_const key 1 nonce j h]
    · rw [serialize_key key 0 nonce j h.1 h.2, serialize_key key 1 nonce j h.1 h.2]
    · rw [serialize_nonce key 0 nonce j h (by omega), serialize_nonce key 1 nonce j h (by omega)]

set_option maxHeartbeats 8000000 in
theorem after_poly (hPre : CorePre s key nonce associatedData plaintext inPtr outPtr)
    {boundary : ReturnBoundary} (hOut : ¬ InProgram boundary.rip) {v w : RamState}
    (L : Loads s v) (hgrow : ∀ x : BitVec 64, (s.external[x]?).isSome → (v.external[x]?).isSome)
    (hsameS : Encrypt.Same (WinS s) s v)
    (A : AtPoly s v w key nonce) (hr : ReadyToStep w) (hc : CodeIn Extracted.programImage w) :
    ∃ fuel z, Advances boundary fuel w z ∧ ReadyToStep z ∧ CodeIn Extracted.programImage z ∧
      AtCut s v z key nonce plaintext := by
  have hS := Encrypt.stack_facts hPre
  have hroom := hS.room
  have htop := hS.top
  have hFB : frameBase s = (stackPtr s).toNat - 0x1b8 := rfl
  have hsp := stack_vs_program hPre
  have hgw : ∀ x : BitVec 64, (s.external[x]?).isSome → (w.external[x]?).isSome :=
    fun x hx => A.grow x (hgrow x hx)
  have hb : boundary.rip.toNat < Poly1305.Callee101e40.entry.toNat ∨
      Poly1305.Callee101e40.entry.toNat + Poly1305.Callee101e40.codeLength ≤ boundary.rip.toNat := by
    rw [Poly1305.Callee101e40.entry_toNat]
    refine Classical.byContradiction fun h => hOut (Encrypt.inProgram_of_toNat ?_ ?_) <;>
      simp only [Poly1305.Callee101e40.codeLength] at h <;> omega
  have hRet : (returnBoundary w).rip = 0x10080b := by
    simp only [returnBoundary]
    rw [Encrypt.mem_read_eq, stackPtr_eq_read]
    change ld w (rg w 4) 64 = _
    rw [A.rsp, A.ret]
  obtain ⟨f0, x, a0, hx⟩ := Poly1305.Callee101e40.advances (otk key nonce) boundary hb w hr hc
    (polyPre hPre A hgrow) (by rw [hRet]; exact Encrypt.ne_boundary hOut _ ⟨by decide, by decide⟩)
  have hrdiN : (rdi.read w).toNat = frameBase s + 0x150 := by
    change (rg w 7).toNat = _; rw [A.rdi]; exact fp_toNat' hS (by decide)
  have hspx : rg x 4 = framePointer s := by
    have := hx.rsp
    rw [stackPtr_eq_read, stackPtr_eq_read] at this
    change rg x 4 = rg w 4 + 8 at this
    rw [this, A.rsp]; exact BitVec.sub_add_cancel _ _
  have hcx : CodeIn Extracted.programImage x := by
    apply CodeIn.of_agreesExcept hx.agrees _ hc
    intro y hy c hcm hcov
    simp only [Poly1305.Callee101e40.changes, List.mem_cons, List.not_mem_nil, or_false] at hcm
    rcases hcm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hcov
    exact stack_av hPre (a := rdi.read w) (n := stateBytes) (by rw [hrdiN]; omega)
      (by rw [hrdiN]; unfold stateBytes; omega) y.1 hcov (inProgram_of_mem hy)
  have hsameX : Encrypt.Same (Win s 0x150 0x188) w x := by
    apply Encrypt.Same.of_agrees hx.agrees
    intro c hcm
    simp only [Poly1305.Callee101e40.changes, List.mem_cons, List.not_mem_nil, or_false] at hcm
    rcases hcm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact fun y hy => absurd hy (Encrypt.nonmem_not_covers rfl y)
    refine Encrypt.mem_within (by rw [hrdiN]; unfold stateBytes; omega) ?_
    intro j hj; rw [hrdiN]; unfold stateBytes at hj; simp only [Win]; omega
  have hpoly : PolyState x (polyBase s) (otk key nonce) 0 := by
    have hbase : rdi.read w = polyBase s := A.rdi
    have hz := hx.hZero
    rw [hbase] at hz
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [← hbase]; exact hx.pad
    · rw [← hbase]; exact hx.rClamped
    · rw [← hbase]; exact hx.rValue
    · simp only [BoundedLimbs, hz]; decide
    · simp only [limbValue, hz]; decide
  have hgx : ∀ y : BitVec 64, (s.external[y]?).isSome → (x.external[y]?).isSome :=
    fun y hy => hx.agrees.grow y (hgw y hy)
  have hsib (u : RamState) (hu : rg u 4 = framePointer s) (d : Disp) (k : Nat)
      (hd : d.value = BitVec.ofNat 64 k) (q : BitVec 64) :
      (AddrMode.sib 4 none 0 d).addr u q = framePointer s + BitVec.ofNat 64 k := by
    rw [Encrypt.sib_rsp_addr, stackPtr_eq_read]; change rg u 4 + _ = _; rw [hu, hd]
  have hpre8 := frame_storePre hPre hgx (p := 0x10080b) (codeLen := 6 + 2) (n := 4)
    (addr := fun u => (AddrMode.sib 4 none 0 (.d8 0x48)).addr u (0x10080b + BitVec.ofNat 64 (6 + 2))) (hx.rip.trans hRet)
    ⟨by decide, by decide⟩ (hsib x hspx (.d8 0x48) 0x48 rfl _)
    (by rw [fp_toNat' hS (k := 0x48) (by decide)]; omega)
    (by rw [fp_toNat' hS (k := 0x48) (by decide)]; omega)
  obtain ⟨x8, b8, r8, c8, g8⟩ := Encrypt.step_run (boundary := boundary)
    (mov_m32_imm32_effect_step 0x10080b (.sib 4 none 0 (.d8 0x48)) (by decide) (by decide)
      (by decide) 1)
    hx.ready hcx (slice_at hcx 0x80b 8 (by decide +kernel) (by decide) (by decide +kernel))
    hpre8 (Encrypt.ne_boundary hOut 0x100813 ⟨by decide, by decide⟩) (by
      intro c hc
      simp only [movM32Imm32Effect, storeEffect, Effect.components, List.map_cons, List.map_nil,
        Write.component_mem, List.cons_append, List.nil_append, List.append_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · rw [hsib x hspx (.d8 0x48) 0x48 rfl]
        exact stack_av hPre (by rw [fp_toNat' hS (by decide)]; omega)
          (by rw [fp_toNat' hS (by decide)]; omega)
      · exact fun y hy => absurd hy (Encrypt.nonmem_not_covers rfl y))
  have hsp8 : rg x8 4 = framePointer s :=
    (rg_keep g8.agrees (by simp [movM32Imm32Effect, storeEffect, Effect.components])).trans hspx
  have w48 : ld x8 (framePointer s + BitVec.ofNat 64 0x48) 32 = 1#32 := by
    have e : ld x8 ((AddrMode.sib 4 none 0 (.d8 0x48)).addr x (0x10080b + BitVec.ofNat 64 (6 + 2))) 32 = 1#32 :=
      g8.writes
    rw [hsib x hspx (.d8 0x48) 0x48 rfl] at e; exact e
  have s8 : Encrypt.Same (Win s 0x48 0x4c) x x8 := by
    have h := Encrypt.same_of_store g8.agrees (addr := framePointer s + BitVec.ofNat 64 0x48)
      (n := 4) (by
        simp only [movM32Imm32Effect, storeEffect, Effect.components, List.map_cons, List.map_nil, Write.component_mem, List.cons_append, List.nil_append, List.append_nil]
        rw [hsib x hspx (.d8 0x48) 0x48 rfl])
      (by rw [fp_toNat' hS (by decide)]; omega)
    refine h.mono fun y hy => ?_
    rw [fp_toNat' hS (by decide)] at hy; simp only [Win]; omega
  have hgx8 : ∀ y : BitVec 64, (s.external[y]?).isSome → (x8.external[y]?).isSome :=
    fun y hy => g8.agrees.grow y (hgx y hy)
  have hpre9 := frame_storePre hPre hgx8 (p := 0x100813) (codeLen := 3 + 2) (n := 1)
    (addr := storeAddrAt 0x100813 (.sib 4 none 0 (.d8 0x58)) (3 + 2)) g8.rip
    ⟨by decide, by decide⟩ (hsib x8 hsp8 (.d8 0x58) 0x58 rfl _)
    (by rw [fp_toNat' hS (k := 0x58) (by decide)]; omega)
    (by rw [fp_toNat' hS (k := 0x58) (by decide)]; omega)
  obtain ⟨x9, b9, r9, c9, g9⟩ := Encrypt.step_run (boundary := boundary)
    (mov_m8_imm8_effect_step 0x100813 (.sib 4 none 0 (.d8 0x58)) (by decide) (by decide)
      (by decide) 0x40)
    r8 c8 (slice_at c8 0x813 5 (by decide +kernel) (by decide) (by decide +kernel))
    hpre9 (Encrypt.ne_boundary hOut 0x100818 ⟨by decide, by decide⟩) (by
      intro c hc
      simp only [movM8Imm8Effect, storeEffect, Effect.components, List.map_cons, List.map_nil,
        Write.component_mem, List.cons_append, List.nil_append, List.append_nil, List.mem_cons,
        List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · rw [storeAddrAt, hsib x8 hsp8 (.d8 0x58) 0x58 rfl]
        exact stack_av hPre (by rw [fp_toNat' hS (by decide)]; omega)
          (by rw [fp_toNat' hS (by decide)]; omega)
      · exact fun y hy => absurd hy (Encrypt.nonmem_not_covers rfl y))
  have hsp9 : rg x9 4 = framePointer s :=
    (rg_keep g9.agrees (by simp [movM8Imm8Effect, storeEffect, Effect.components])).trans hsp8
  have w58 : ld x9 (framePointer s + BitVec.ofNat 64 0x58) 8 = 0x40#8 := by
    have e : ld x9 ((AddrMode.sib 4 none 0 (.d8 0x58)).addr x8 (0x100813 + BitVec.ofNat 64 (3 + 2))) 8 = 0x40#8 :=
      g9.writes
    rw [hsib x8 hsp8 (.d8 0x58) 0x58 rfl] at e; exact e
  have s9 : Encrypt.Same (Win s 0x58 0x59) x8 x9 := by
    have h := Encrypt.same_of_store g9.agrees (addr := framePointer s + BitVec.ofNat 64 0x58)
      (n := 1) (by
        simp only [movM8Imm8Effect, storeEffect, Effect.components, storeAddrAt, List.map_cons, List.map_nil, Write.component_mem, List.cons_append, List.nil_append, List.append_nil]
        rw [hsib x8 hsp8 (.d8 0x58) 0x58 rfl])
      (by rw [fp_toNat' hS (by decide)]; omega)
    refine h.mono fun y hy => ?_
    rw [fp_toNat' hS (by decide)] at hy; simp only [Win]; omega
  obtain ⟨x10, b10, r10, c10, g10⟩ := Encrypt.step_run (boundary := boundary)
    (lea_r64_effect_step 0x100818 0x48 (by unfold RexWPrefix; decide) 7
      (.sib 4 none 0 (.d32 0xd0)) (by decide) (by decide) (by decide))
    r9 c9 (slice_at c9 0x818 8 (by decide +kernel) (by decide) (by decide +kernel))
    g9.rip (Encrypt.ne_boundary hOut 0x100820 ⟨by decide, by decide⟩)
    (Encrypt.regs_av (by simp (config := { decide := true }) [Component.isMem, leaR64Effect, Effect.components]))
  have hsp10 : rg x10 4 = framePointer s :=
    (rg_keep g10.agrees (by simp (config := { decide := true }) [leaR64Effect, Effect.components])).trans hsp9
  have h7 : rg x10 7 = framePointer s + BitVec.ofNat 64 0xd0 := by
    have e : rg x10 7 = (AddrMode.sib 4 none 0 (.d32 0xd0)).addr x9
      (0x100818 + BitVec.ofNat 64 (leaLen (.sib 4 none 0 (.d32 0xd0)))) := g10.writes
    rw [e, hsib x9 hsp9 _ 0xd0 rfl]
  obtain ⟨x11, b11, r11, c11, g11⟩ := Encrypt.step_run (boundary := boundary)
    (lea_r64_effect_step 0x100820 0x48 (by unfold RexWPrefix; decide) 6
      (.sib 4 none 0 (.d8 0x18)) (by decide) (by decide) (by decide))
    r10 c10 (slice_at c10 0x820 5 (by decide +kernel) (by decide) (by decide +kernel))
    g10.rip (Encrypt.ne_boundary hOut 0x100825 ⟨by decide, by decide⟩)
    (Encrypt.regs_av (by simp (config := { decide := true }) [Component.isMem, leaR64Effect, Effect.components]))
  have hsp11 : rg x11 4 = framePointer s :=
    (rg_keep g11.agrees (by simp (config := { decide := true }) [leaR64Effect, Effect.components])).trans hsp10
  have h6 : rg x11 6 = framePointer s + BitVec.ofNat 64 0x18 := by
    have e : rg x11 6 = (AddrMode.sib 4 none 0 (.d8 0x18)).addr x10
      (0x100820 + BitVec.ofNat 64 (leaLen (.sib 4 none 0 (.d8 0x18)))) := g11.writes
    rw [e, hsib x10 hsp10 _ 0x18 rfl]
  have h7' : rg x11 7 = framePointer s + BitVec.ofNat 64 0xd0 := by
    rw [rg_keep g11.agrees (r := 7) (by simp (config := { decide := true }) [leaR64Effect, Effect.components]), h7]
  obtain ⟨x12, b12, r12, c12, g12⟩ := Encrypt.step_run (boundary := boundary)
    (mov_r32_imm32_effect_step 0x100825 0xb9 (by decide) 0x20)
    r11 c11 (slice_at c11 0x825 5 (by decide +kernel) (by decide) (by decide +kernel))
    g11.rip (Encrypt.ne_boundary hOut 0x10082a ⟨by decide, by decide⟩)
    (Encrypt.regs_av (by simp (config := { decide := true }) [Component.isMem, movR32Imm32Effect, Effect.components]))
  have hsp12 : rg x12 4 = framePointer s :=
    (rg_keep g12.agrees (by simp (config := { decide := true }) [movR32Imm32Effect, Effect.components])).trans hsp11
  have h1 : rg x12 1 = BitVec.ofNat 64 32 := g12.writes
  have h6' : rg x12 6 = framePointer s + BitVec.ofNat 64 0x18 := by
    rw [rg_keep g12.agrees (r := 6) (by simp (config := { decide := true }) [movR32Imm32Effect, Effect.components]), h6]
  have h7'' : rg x12 7 = framePointer s + BitVec.ofNat 64 0xd0 := by
    rw [rg_keep g12.agrees (r := 7) (by simp (config := { decide := true }) [movR32Imm32Effect, Effect.components]), h7']
  have hgx12 : ∀ y : BitVec 64, (s.external[y]?).isSome → (x12.external[y]?).isSome :=
    fun y hy => g12.agrees.grow y (g11.agrees.grow y (g10.agrees.grow y (g9.agrees.grow y
      (hgx8 y hy))))
  have hdf12 : DirectionFlagUnset x12 :=
    g12.agrees.directionFlagClear (by simp [movR32Imm32Effect, Effect.components]) <|
    g11.agrees.directionFlagClear (by simp [leaR64Effect, Effect.components]) <|
    g10.agrees.directionFlagClear (by simp [leaR64Effect, Effect.components]) <|
    g9.agrees.directionFlagClear (by simp [movM8Imm8Effect, storeEffect, Effect.components]) <|
    g8.agrees.directionFlagClear (by simp [movM32Imm32Effect, storeEffect, Effect.components]) <|
    hx.agrees.directionFlagClear (by simp [Poly1305.Callee101e40.changes]) A.df
  have hrip12 : x12.RIP = 0x10082a := g12.rip
  have hsiN : (rsi.read x12).toNat = frameBase s + 0x18 := by
    change (rg x12 6).toNat = _; rw [h6']; exact fp_toNat' hS (by decide)
  have hdiN : (rdi.read x12).toNat = frameBase s + 0xd0 := by
    change (rg x12 7).toNat = _; rw [h7'']; exact fp_toNat' hS (by decide)
  have hcxN : (rcx.read x12).toNat = 32 := by change (rg x12 1).toNat = _; rw [h1]; rfl
  have hal : (stackPtr s).toNat % 16 = 8 := hPre.stack.2.2.2
  have htab := hS.tables
  have hmem (a : BitVec 64) (k : Nat) (ha : a.toNat = frameBase s + k) (hk : k + 128 ≤ 0x1c0) :
      ∀ i < 4 * 32, (x12.external[a + BitVec.ofNat 64 i]?).isSome := by
    intro i hi
    rw [show a + BitVec.ofNat 64 i = BitVec.ofNat 64 (a.toNat + i) by
      apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, BitVec.toNat_ofNat]; omega]
    exact frame_some hPre hgx12 _ (by omega) (by omega)
  have HL : MovsdLoop x12 (31 + 1) := by
    have hcode := slice_at (p := 0x10082a) (bytes := [0xF3, 0xA5]) c12 0x82a 2
      (by decide +kernel) (by decide) (by decide +kernel)
    refine ⟨r12.midRep, hdf12.df, hrip12 ▸ hcode.bytesAt, by rw [hrip12]; decide, h1, ?_, ?_, ?_,
      hmem _ 0x18 hsiN (by decide), hmem _ 0xd0 hdiN (by decide), ?_, ?_, ?_⟩
    · rw [hsiN]; omega
    · rw [hdiN]; omega
    · rw [hdiN]; omega
    · rw [hsiN, hdiN]; omega
    · rw [hdiN]; omega
    · rw [hrip12]
      have h0 : (0x10082a : BitVec 64).toNat = 0x10082a := rfl
      exact RangeApart.of_toNat (by omega) (by decide) (by rw [hdiN, h0]; omega)
  have hstride : UnitStringStride bindings := hPre.environment.stringStride
  have hloop := MovsdLoop.advances hstride boundary 31 x12 HL
    (by rw [hrip12]; exact Encrypt.ne_boundary hOut _ ⟨by decide, by decide⟩)
    (by rw [hrip12]; exact Encrypt.ne_boundary hOut 0x10082c ⟨by decide, by decide⟩)
  have hdone := movsd_loop hstride 31 x12 HL
  have hagM := hdone.agrees
  rw [clearRep_eq r12.ready.repeatClear] at hagM
  have hcM : CodeIn Extracted.programImage (nextStates (31 + 1) x12) := by
    apply CodeIn.of_agreesExcept hagM _ c12
    intro y hy c hcm hcov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hcm
    rcases hcm with rfl | rfl | rfl | rfl | rfl
    all_goals try exact hcov
    exact stack_av hPre (a := rdi.read x12) (n := 4 * (31 + 1)) (by rw [hdiN]; omega)
      (by rw [hdiN]; omega) y.1 hcov (inProgram_of_mem hy)
  have hrip13 : (nextStates (31 + 1) x12).RIP = 0x10082c := by rw [hdone.rip, hrip12]; rfl
  have hr12 : rg (nextStates (31 + 1) x12) 12 = rg s 9 := by
    rw [rg_keep hagM (r := 12) (by simp),
      rg_keep g12.agrees (r := 12) (by simp (config := { decide := true }) [movR32Imm32Effect, Effect.components]),
      rg_keep g11.agrees (r := 12) (by simp (config := { decide := true }) [leaR64Effect, Effect.components]),
      rg_keep g10.agrees (r := 12) (by simp (config := { decide := true }) [leaR64Effect, Effect.components]),
      rg_keep g9.agrees (r := 12) (by simp [movM8Imm8Effect, storeEffect, Effect.components]),
      rg_keep g8.agrees (r := 12) (by simp [movM32Imm32Effect, storeEffect, Effect.components]),
      rg_keep hx.agrees (r := 12) (by simp [Poly1305.Callee101e40.changes]), A.r12, L.r12]
  have hdb : (descriptorRegion s).Bounded := hPre.descriptorBounded
  simp only [descriptorRegion, registerRegion, MemoryRegion.Bounded, userAddressLimit] at hdb
  replace hdb : (rg s 9).toNat + 24 < 2 ^ 32 := hdb
  have hds := hPre.separation.2.1 (Stack.region s coreStackBytes) (by simp [coreWritten])
    (descriptorRegion s) (by simp [coreRead])
  have hdsep : (rg s 9).toNat + 24 ≤ (stackPtr s).toNat - 992 ∨
      (stackPtr s).toNat + 8 ≤ (rg s 9).toNat := by
    have h := sep_of_overlap (a := (rg s 9).toNat) (n := 24) (b := (stackPtr s).toNat - 992)
      (m := 1000) fun y h₁ h₂ h₃ h₄ =>
        hds y (Encrypt.stack_contains.mpr ⟨h₃, by omega⟩) ⟨h₁, h₂⟩
    generalize (rg s 9).toNat = a at h ⊢
    generalize (stackPtr s).toNat = b at h hroom ⊢
    omega
  have hlen := hPre.messageLength
  have haddr : rg s 9 + BitVec.signExtend 64 (0x10 : BitVec 8) =
      BitVec.ofNat 64 ((descriptorWord s 2).start) := by
    apply BitVec.eq_of_toNat_eq
    simp only [descriptorWord]
    rw [BitVec.toNat_ofNat, show BitVec.signExtend 64 (0x10 : BitVec 8) = BitVec.ofNat 64 16 from rfl,
      Encrypt.toNat_add_ofNat (by omega)]
    change _ = ((rg s 9).toNat + 16) % _
    rw [Nat.mod_eq_of_lt (by omega)]
  have sRep : Encrypt.Same (Win s 0xd0 0x150) x12 (nextStates (31 + 1) x12) := by
    apply Encrypt.Same.of_agrees hagM
    intro c hcm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hcm
    rcases hcm with rfl | rfl | rfl | rfl | rfl
    all_goals try exact fun y hy => absurd hy (Encrypt.nonmem_not_covers rfl y)
    refine Encrypt.mem_within (by rw [hdiN]; omega) ?_
    intro j hj; rw [hdiN]; simp only [Win]; omega
  have sRegs : Encrypt.Same (Win s 0 0) x9 x12 :=
    Encrypt.same_of_regs (g10.agrees.trans (g11.agrees.trans g12.agrees)) (by
      simp (config := { decide := true }) [leaR64Effect, movR32Imm32Effect, Effect.components,
        Component.isMem])
  have mono {W : Nat → Prop} {a b : RamState} (h : Encrypt.Same W a b)
      (hw : ∀ y, W y → WP s y) : Encrypt.Same (WP s) a b := h.mono hw
  have hVZ : Encrypt.Same (WP s) v (nextStates (31 + 1) x12) := by
    refine (mono A.same ?_).trans <| (mono hsameX ?_).trans <| (mono s8 ?_).trans <|
      (mono s9 ?_).trans <| (mono sRegs ?_).trans (mono sRep ?_)
    all_goals intro y hy; simp only [W100, Win, WP] at hy ⊢; omega
  have hSZ : Encrypt.Same (Wall s) s (nextStates (31 + 1) x12) :=
    (hsameS.mono fun y hy => by simp only [WinS, Wall] at hy ⊢; omega).trans
      (hVZ.mono fun y hy => by simp only [WP, Wall] at hy ⊢; omega)
  have hval : ld (nextStates (31 + 1) x12) (BitVec.ofNat 64 (descriptorWord s 2).start) 64 =
      BitVec.ofNat 64 plaintext.size := by
    have hstart : (descriptorWord s 2).start = (rg s 9).toNat + 16 := rfl
    rw [show ld (nextStates (31 + 1) x12) _ 64 = ld s _ 64 from hSZ.load fun i hi => by
      simp only [Wall]
      rw [hstart, Encrypt.toNat_add_ofNat (by rw [BitVec.toNat_ofNat]; omega), BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega)]
      omega]
    exact word64At_ld hlen
  have hgx13 : ∀ y : BitVec 64, (s.external[y]?).isSome →
      ((nextStates (31 + 1) x12).external[y]?).isSome :=
    fun y hy => hagM.grow y (hgx12 y hy)
  have hsome16 : ∀ i < 8, (s.external[BitVec.ofNat 64 (descriptorWord s 2).start +
      BitVec.ofNat 64 i]?).isSome := ldb_isSome hlen.2
  have hamA : ∀ u : RamState, rg u 12 = rg s 9 → ∀ q,
      (AddrMode.sib 12 none 0 (.d8 0x10)).addr u q = BitVec.ofNat 64 (descriptorWord s 2).start := by
    intro u hu q
    rw [← haddr]
    simp only [AddrMode.addr, AddrMode.reg64, Disp.value]
    change rg u 12 + _ = _
    rw [hu]
  have hpre14 : LoadPre 0x10082c (fun u => (AddrMode.sib 12 none 0 (.d8 0x10)).addr u
      (0x10082c + BitVec.ofNat 64 (movLoadLen (.sib 12 none 0 (.d8 0x10))))) 8
      (nextStates (31 + 1) x12) := by
    refine ⟨hrip13, ?_⟩
    rw [hamA _ hr12]
    refine ⟨by rw [BitVec.toNat_ofNat]; change ((rg s 9).toNat + 16) % _ + 8 ≤ _
               rw [Nat.mod_eq_of_lt (by omega)]; omega, fun i hi => hgx13 _ (hsome16 i hi)⟩
  obtain ⟨x14, b14, r14, c14, g14⟩ := Encrypt.step_run (boundary := boundary)
    (mov_r64_m64_effect_step 0x10082c 0x49 (by unfold RexWPrefix; decide) 1
      (.sib 12 none 0 (.d8 0x10)) (by decide) (by decide) (by decide))
    hdone.ready hcM (slice_at hcM 0x82c 5 (by decide +kernel) (by decide) (by decide +kernel))
    hpre14 (Encrypt.ne_boundary hOut 0x100831 ⟨by decide, by decide⟩)
    (Encrypt.regs_av (by simp (config := { decide := true }) [Component.isMem, movR64M64Effect, Effect.components]))
  have hcx14 : rg x14 1 = BitVec.ofNat 64 plaintext.size := by
    have e : rg x14 1 = ld (nextStates (31 + 1) x12)
      ((AddrMode.sib 12 none 0 (.d8 0x10)).addr (nextStates (31 + 1) x12)
        (0x10082c + BitVec.ofNat 64 (movLoadLen (.sib 12 none 0 (.d8 0x10))))) 64 := g14.writes
    rw [e, hamA _ hr12, hval]
  obtain ⟨x15, b15, r15, c15, g15⟩ := Encrypt.step_run (boundary := boundary)
    (mov_r8_imm8_effect_step 0x100831 0xb0 (by decide) 1)
    r14 c14 (slice_at c14 0x831 2 (by decide +kernel) (by decide) (by decide +kernel))
    g14.rip (Encrypt.ne_boundary hOut 0x100833 ⟨by decide, by decide⟩)
    (Encrypt.regs_av (by simp (config := { decide := true }) [Component.isMem, movR8Imm8Effect, Effect.components]))
  obtain ⟨x16, b16, r16, c16, g16⟩ := Encrypt.step_run (boundary := boundary)
    (cmp_r64_r64_effect_step 0x100833 0x48 0xd9 (by unfold RexWPrefix; decide) (by decide))
    r15 c15 (slice_at c15 0x833 3 (by decide +kernel) (by decide) (by decide +kernel))
    g15.rip (Encrypt.ne_boundary hOut 0x100836 ⟨by decide, by decide⟩)
    (Encrypt.regs_av (by simp (config := { decide := true }) [Component.isMem, cmpR64R64Effect, Effect.components]))
  have hx13 : rg (nextStates (31 + 1) x12) 3 = lengthLimit := by
    rw [rg_keep hagM (r := 3) (by simp),
      rg_keep g12.agrees (r := 3) (by simp (config := { decide := true }) [movR32Imm32Effect, Effect.components]),
      rg_keep g11.agrees (r := 3) (by simp (config := { decide := true }) [leaR64Effect, Effect.components]),
      rg_keep g10.agrees (r := 3) (by simp (config := { decide := true }) [leaR64Effect, Effect.components]),
      rg_keep g9.agrees (r := 3) (by simp [movM8Imm8Effect, storeEffect, Effect.components]),
      rg_keep g8.agrees (r := 3) (by simp [movM32Imm32Effect, storeEffect, Effect.components]),
      rg_keep hx.agrees (r := 3) (by simp [Poly1305.Callee101e40.changes]), A.rbx]
  have hbx15 : rg x15 3 = lengthLimit := by
    rw [rg_keep g15.agrees (r := 3) (by simp (config := { decide := true }) [movR8Imm8Effect, Effect.components]),
      rg_keep g14.agrees (r := 3) (by simp (config := { decide := true }) [movR64M64Effect, Effect.components]), hx13]
  have hcx15 : rg x15 1 = BitVec.ofNat 64 plaintext.size := by
    rw [rg_keep g15.agrees (r := 1) (by simp (config := { decide := true }) [movR8Imm8Effect, Effect.components]), hcx14]
  have hInB : inPtr.toNat + plaintext.size < 2 ^ 32 := hPre.messageInMemory.1
  have hc16 : condHolds 7 (StatusFlags.ofRFLAGS x16.RFLAGS) = false := by
    have hf := g16.flags
    simp only [Effect.FlagsHold, cmpR64R64Effect] at hf
    obtain ⟨hCF, -, -, hZF, -⟩ := hf
    change (StatusFlags.ofRFLAGS x16.RFLAGS).CF = (cmpSpec _ _).CF at hCF
    change (StatusFlags.ofRFLAGS x16.RFLAGS).ZF = (cmpSpec _ _).ZF at hZF
    rw [condHolds_7, hCF, hZF, cmpSpec_ZF]
    change (!(decide ((rg x15 1).toNat < (rg x15 3).toNat) || (rg x15 1 == rg x15 3))) = _
    rw [hcx15, hbx15]
    have hlt : (BitVec.ofNat 64 plaintext.size).toNat < (lengthLimit).toNat := by
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      show plaintext.size < 0x3fffffffbf
      omega
    simp only [decide_eq_true hlt, Bool.true_or, Bool.not_true]
  obtain ⟨x17, b17, r17, c17, g17⟩ := Encrypt.step_run (boundary := boundary)
    (jcc_rel32_effect_step 0x100836 7 0x1c2)
    r16 c16 (slice_at c16 0x836 6 (by decide +kernel) (by decide) (by decide +kernel))
    ⟨g16.rip, fun h => by rw [hc16] at h; exact absurd h (by decide)⟩
    (by
      change (jccEffect 0x100836 6 7 _ x16).rip ≠ _
      simp only [jccEffect, branchEffect, hc16]
      exact Encrypt.ne_boundary hOut 0x10083c ⟨by decide, by decide⟩)
    (Encrypt.regs_av (by simp [Component.isMem, jccEffect]))
  have hag14 := g14.agrees.trans (g15.agrees.trans (g16.agrees.trans g17.agrees))
  have hext : x17.external = (nextStates (31 + 1) x12).external :=
    Encrypt.ext_of_regs hag14 (by
      simp (config := { decide := true }) [movR64M64Effect, movR8Imm8Effect, cmpR64R64Effect,
        jccEffect, branchEffect, Effect.components, Component.isMem])
  have hkeepX (r : BitVec 5) (hr0 : r ≠ 0) (hr1 : r ≠ 1) (hr6 : r ≠ 6) (hr7 : r ≠ 7) :
      rg x17 r = rg x r := by
    rw [rg_keep g17.agrees (r := r) (by simp [jccEffect, branchEffect, Effect.components]),
      rg_keep g16.agrees (r := r) (by simp [cmpR64R64Effect, Effect.components]),
      rg_keep g15.agrees (r := r) (by
        simp (config := { decide := true }) [movR8Imm8Effect, Effect.components]; exact hr0),
      rg_keep g14.agrees (r := r) (by
        simp (config := { decide := true }) [movR64M64Effect, Effect.components]; exact hr1),
      rg_keep hagM (r := r) (by simp; exact ⟨hr1, hr6, hr7⟩),
      rg_keep g12.agrees (r := r) (by
        simp (config := { decide := true }) [movR32Imm32Effect, Effect.components]; exact hr1),
      rg_keep g11.agrees (r := r) (by
        simp (config := { decide := true }) [leaR64Effect, Effect.components]; exact hr6),
      rg_keep g10.agrees (r := r) (by
        simp (config := { decide := true }) [leaR64Effect, Effect.components]; exact hr7),
      rg_keep g9.agrees (r := r) (by simp [movM8Imm8Effect, storeEffect, Effect.components]),
      rg_keep g8.agrees (r := r) (by simp [movM32Imm32Effect, storeEffect, Effect.components])]
  have hkeepW (r : BitVec 5) (hr : Component.reg r ∉ Poly1305.Callee101e40.changes w)
      (hr0 : r ≠ 0) (hr1 : r ≠ 1) (hr6 : r ≠ 6) (hr7 : r ≠ 7) : rg x17 r = rg w r := by
    rw [hkeepX r hr0 hr1 hr6 hr7, rg_keep hx.agrees hr]
  have fp_addr (k i : Nat) (h : k + i ≤ 0x1c0) :
      BitVec.ofNat 64 (frameBase s + k + i) =
        framePointer s + BitVec.ofNat 64 k + BitVec.ofNat 64 i := by
    rw [addr_assoc, Encrypt.framePointer_add_eq hS h, Nat.add_assoc]
  have Wc : Encrypt.Same (fun y => W100 s y ∨ Win s 0x150 0x188 y ∨ Win s 0x48 0x4c y ∨
      Win s 0x58 0x59 y ∨ Win s 0 0 y) v x12 :=
    ((((A.same.mono fun y hy => .inl hy).trans (hsameX.mono fun y hy => .inr (.inl hy))).trans
      (s8.mono fun y hy => .inr (.inr (.inl hy)))).trans
      (s9.mono fun y hy => .inr (.inr (.inr (.inl hy))))).trans
      (sRegs.mono fun y hy => .inr (.inr (.inr (.inr hy))))
  have bytes12 := cipher_bytes hPre L hgrow Wc hgx12 (by
    rw [keep_load sRegs hS (by decide) (by intro i hi; simp only [Win]; omega),
      keep_load s9 hS (by decide) (by intro i hi; simp only [Win]; omega)]
    exact w48)
  have hpos12 : x12.external[BitVec.ofNat 64 (frameBase s + 0x18 + 0x40)]? = some 64 := by
    have l12 : ld x12 (framePointer s + BitVec.ofNat 64 0x58) 8 = 0x40#8 := by
      rw [keep_load sRegs hS (by decide) (by intro i hi; simp only [Win]; omega)]
      exact w58
    apply some_of_memByte (frame_some hPre hgx12 _ (by omega) (by omega))
    rw [show frameBase s + 0x18 + 0x40 = frameBase s + 0x58 + 0 by omega,
      fp_addr 0x58 0 (by omega), ld_byte l12 0 (by decide)]
    rfl
  have hcopy (i : Nat) (hi : i < 0x41) :
      x17.external[BitVec.ofNat 64 (frameBase s + 0xd0 + i)]? =
        x12.external[BitVec.ofNat 64 (frameBase s + 0x18 + i)]? := by
    rw [hext]
    have hd : BitVec.ofNat 64 (frameBase s + 0xd0 + i) = rdi.read x12 + BitVec.ofNat 64 i := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Encrypt.toNat_add_ofNat (by omega), hdiN]
    have hs' : BitVec.ofNat 64 (frameBase s + 0x18 + i) = rsi.read x12 + BitVec.ofNat 64 i := by
      apply BitVec.eq_of_toNat_eq
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Encrypt.toNat_add_ofNat (by omega), hsiN]
    rw [hd, hs']
    exact hdone.copy i (by omega)
  have hXZ : Encrypt.Same (fun y => Win s 0x48 0x4c y ∨ Win s 0x58 0x59 y ∨ Win s 0 0 y ∨
      Win s 0xd0 0x150 y) x x17 :=
    (((s8.mono fun y hy => .inl hy).trans (s9.mono fun y hy => .inr (.inl hy))).trans
      (sRegs.mono fun y hy => .inr (.inr (.inl hy)))).trans
      ((sRep.mono fun y hy => .inr (.inr (.inr hy))).trans fun y _ => by rw [hext])
  have hag17 := hx.agrees.trans (g8.agrees.trans (g9.agrees.trans (g10.agrees.trans
    (g11.agrees.trans g12.agrees))))
  refine ⟨_, x17, a0.trans (b8.trans (b9.trans (b10.trans (b11.trans (b12.trans (hloop.trans
    (b14.trans (b15.trans (b16.trans b17))))))))), r17, c17, ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [g17.rip]; simp only [jccEffect, branchEffect, hc16]; rfl
  · rw [hkeepX 4 (by decide) (by decide) (by decide) (by decide), hspx]
  · rw [hkeepW 5 (by simp [Poly1305.Callee101e40.changes]) (by decide) (by decide) (by decide)
      (by decide), A.rbp]
  · rw [hkeepW 12 (by simp [Poly1305.Callee101e40.changes]) (by decide) (by decide) (by decide)
      (by decide), A.r12]
  · rw [hkeepW 13 (by simp [Poly1305.Callee101e40.changes]) (by decide) (by decide) (by decide)
      (by decide), A.r13]
  · rw [hkeepW 14 (by simp [Poly1305.Callee101e40.changes]) (by decide) (by decide) (by decide)
      (by decide), A.r14]
  · rw [hkeepW 15 (by simp [Poly1305.Callee101e40.changes]) (by decide) (by decide) (by decide)
      (by decide), A.r15]; rfl
  · rw [hkeepW 3 (by simp [Poly1305.Callee101e40.changes]) (by decide) (by decide) (by decide)
      (by decide), A.rbx]
  · rw [rg_keep g17.agrees (r := 1) (by simp [jccEffect, branchEffect, Effect.components]),
      rg_keep g16.agrees (r := 1) (by simp [cmpR64R64Effect, Effect.components]), hcx15]
  · exact hVZ.trans fun y _ => by rw [hext]
  · refine hasBytes_of_memByte (by simp only [cipherWords, ByteArray.size, Vector.size_toArray]) ?_ ?_
    · intro i hi
      exact frame_some hPre (fun y hy => by rw [hext]; exact hagM.grow y (hgx12 y hy)) _
        (by unfold cipherOffset; omega) (by unfold cipherOffset; omega)
    · intro i hi
      apply memByte_of_some
      unfold cipherOffset
      rw [hcopy i (by omega), bytes12 i hi]
  · refine hasBytes_of_memByte (n := 1) rfl ?_ ?_
    · intro i hi
      exact frame_some hPre (fun y hy => by rw [hext]; exact hagM.grow y (hgx12 y hy)) _
        (by unfold cipherOffset; omega) (by unfold cipherOffset; omega)
    · intro i hi
      obtain rfl : i = 0 := by omega
      apply memByte_of_some
      unfold cipherOffset
      rw [show frameBase s + 0xd0 + 0x40 + 0 = frameBase s + 0xd0 + 0x40 by rfl,
        hcopy 0x40 (by decide), hpos12]
      rfl
  · have hpb : (polyBase s).toNat = frameBase s + 0x150 :=
      Encrypt.framePointer_add_toNat hS (k := polyOffset) (by decide)
    exact Encrypt.polyState_same hXZ (by omega) (fun k hk => by
      rw [hpb]; simp only [Win]; omega) hpoly
  · intro y hy
    rw [hext]
    exact hagM.grow y (hag17.grow y (A.grow y hy))
  · rw [show DirectionFlagUnset x17 = DirectionFlagUnset x17 from rfl]
    exact hag14.directionFlagClear (by
      simp (config := { decide := true }) [movR64M64Effect, movR8Imm8Effect, cmpR64R64Effect,
        jccEffect, branchEffect, Effect.components])
      (hagM.directionFlagClear (by simp) hdf12)
  · exact SupportedSSE.of_agreesExcept hag14 (SupportedSSE.of_agreesExcept hagM
      (SupportedSSE.of_agreesExcept hag17 A.sse))

end AfterPoly

end ChaCha20Poly1305.Proofs.Core.Setup

namespace ChaCha20Poly1305.Proofs.Core.Setup


open ChaCha20Poly1305.Spec.Program Standards.RFC.ChaCha20Poly1305 Prelude X86 X86.Machine
open X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CoreContract
open ChaCha20Poly1305.Proofs.MemoryRoutines.Machine ChaCha20Poly1305.Proofs.Poly1305State

section Setup

variable [bindings : Machine.Bindings] {s : RamState} {key : Vector UInt8 32}
  {nonce : Vector UInt8 12} {associatedData plaintext : ByteArray} {inPtr outPtr : BitVec 64}

set_option maxHeartbeats 8000000 in
theorem setup (boundary : ReturnBoundary)
    (hPre : CorePre s key nonce associatedData plaintext inPtr outPtr)
    (hBoundaryOutside : ¬ InProgram boundary.rip)
    (_hBoundaryDifferent : boundary.rip ≠ (returnBoundary s).rip) :
    ∃ fuel t, Advances boundary fuel s t ∧
      Cut1 s t key nonce associatedData plaintext inPtr outPtr := by
  have hS := Encrypt.stack_facts hPre
  have hroom := hS.room
  have htop := hS.top
  have hFB : frameBase s = (stackPtr s).toNat - 0x1b8 := rfl
  have hOut := hBoundaryOutside
  obtain ⟨t1, t2, t3, t4, t5, t6, t7, t8, t9, t10, t11, f1, a1, r11, c11, h1, h2, h3, h4, h5, h6,
    h7, h8, h9, h10, h11, -⟩ := prefix_states boundary (away_of hOut) (ready_of_core hPre)
      hPre.code (segPre_of_core hPre)
  have L := prefix_loads hS (segPre_of_core hPre) h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
  obtain ⟨hsame, hgrow, hdf, hsse⟩ := prefix_misc hS h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11
    hPre.directionFlagUnset hPre.machine.sse
  have hCP := keyCallPre hPre r11 c11 h11.rip L hgrow hdf
  have hRet : (returnBoundary t11).rip = 0x1007e1 := by
    simp only [returnBoundary]
    rw [Encrypt.mem_read_eq, stackPtr_eq_read]
    change ld t11 (rg t11 4) 64 = _
    rw [L.rsp, L.ret]; rfl
  have hb : boundary.rip.toNat < Callee100a80.entry.toNat ∨
      Callee100a80.codeEnd ≤ boundary.rip.toNat := by
    have he : Callee100a80.entry.toNat = 0x100a80 := rfl
    rw [he]
    refine Classical.byContradiction fun h => hOut (Encrypt.inProgram_of_toNat ?_ ?_) <;>
      simp only [Callee100a80.codeEnd] at h <;> omega
  obtain ⟨f2, w0, a2, hR⟩ := Encrypt.calleeAdvances boundary hb hCP
    (by rw [hRet]; exact Encrypt.ne_boundary hOut _ ⟨by decide, by decide⟩)
  obtain ⟨f3, w, a3, rw, cw, A⟩ := after_key hPre hOut L hdf hsse hgrow hR
  obtain ⟨f4, z, a4, rz, cz, C⟩ := after_poly hPre hOut L hgrow hsame A rw cw
  have hSZ : Encrypt.Same (Wall s) s z :=
    (hsame.mono fun y hy => by simp only [WinS, Wall] at hy ⊢; omega).trans
      (C.same.mono fun y hy => by simp only [WP, Wall] at hy ⊢; omega)
  have hgz : ∀ y : BitVec 64, (s.external[y]?).isSome → (z.external[y]?).isSome :=
    fun y hy => C.grow y (hgrow y hy)
  have hstk (y : Nat) (hy : Wall s y) : (Stack.region s coreStackBytes).Contains y := by
    rw [Encrypt.stack_contains]; simp only [Wall] at hy; omega
  refine ⟨_, z, a1.trans (a2.trans (a3.trans a4)), ⟨⟨Encrypt.machineRamUnitStrideDecodable_of_ready rz
      hPre.environment.stringStride, ⟨rz.cpu, C.sse, rz.memory, rz.ready⟩, cz, C.df, ?rsp,
      ?frame, ?allocated, ?saved, ?returnAddress⟩, C.rip, ?rbp, ?r12, ?r13, ?r14, C.r15, C.rbx,
      C.rcx, ?message, C.cipher, C.position, C.poly⟩⟩
  case rsp => rw [stackPtr_eq_read]; exact C.rsp
  case rbp => exact C.rbp.trans L.rbp
  case r12 => exact C.r12.trans L.r12
  case r13 => exact C.r13.trans L.r13
  case r14 => exact C.r14.trans L.r14
  case frame =>
    intro y hy
    apply hSZ y
    intro hw
    exact hy (Stack.region s coreStackBytes) (by simp) (hstk _ hw)
  case allocated =>
    intro region hr y hy
    have hs : (s.external[y]?).isSome := by
      simp only [coreWritten, List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · obtain ⟨b, hb⟩ := hPre.resultInMemory.2 y hy; simp [hb]
      · obtain ⟨b, hb⟩ := hPre.outputInMemory.2 y hy; simp [hb]
      · obtain ⟨b, hb⟩ := hPre.stack.2.1 y hy; simp [hb]
    exact Option.isSome_iff_exists.mp (hgz y hs)
  case message =>
    have hIS := Encrypt.in_stack hPre
    exact hSZ.hasBytes hPre.messageInMemory.2 (by
      have := hPre.messageInMemory.1; simp only [messageRegion, MemoryRegion.Bounded,
        userAddressLimit] at this ⊢; omega)
      (fun y h₁ h₂ hw => hIS y ⟨h₁, h₂⟩ (hstk y hw))
  case returnAddress =>
    have hsp : s.regValue .rsp = stackPtr s := rfl
    have h0 : (Stack.returnSlot s).Word64At s.external (returnBoundary s).rip := by
      apply Encrypt.word64At_of_load rfl
      · simp only [Stack.returnSlot, hsp, BitVec.ofNat_toNat, BitVec.setWidth_eq]
        rfl
      · intro i hi
        simp only [Stack.returnSlot, hsp]
        rw [← BitVec.ofNat_add]
        obtain ⟨b, hb⟩ := hPre.stack.2.1 (BitVec.ofNat 64 ((stackPtr s).toNat + i))
          (Encrypt.stack_contains.mpr (by
          rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]; omega))
        simp [hb]
    exact hSZ.word64At h0 (by simp only [Stack.returnSlot, hsp]; omega) (fun y h₁ h₂ => by
      simp only [Stack.returnSlot, hsp] at h₁ h₂; simp only [Wall]; omega)
  case saved =>
    intro e he
    have hv (k : Nat) (hk : 0x188 ≤ k ∧ k ≤ 0x1b0) (val : BitVec 64)
        (h : ld t11 (framePointer s + BitVec.ofNat 64 k) 64 = val) :
        (slot s k).Word64At z.external val := by
      have hv0 : (slot s k).Word64At t11.external val := by
        apply Encrypt.word64At_of_load rfl
        · simp only [slot]; rw [← Encrypt.framePointer_add_eq hS (by omega)]; exact h
        · intro i hi
          simp only [slot]; rw [← BitVec.ofNat_add]
          exact frame_some hPre hgrow (frameBase s + k + i) (by omega) (by omega)
      exact (C.same).word64At hv0 (by simp only [slot]; omega) (fun y h₁ h₂ => by
        simp only [slot] at h₁ h₂; simp only [WP]; omega)
    simp only [savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at he
    rcases he with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hv 0x188 (by decide) _ L.s188
    · exact hv 0x190 (by decide) _ L.s190
    · exact hv 0x198 (by decide) _ L.s198
    · exact hv 0x1a0 (by decide) _ L.s1a0
    · exact hv 0x1a8 (by decide) _ L.s1a8
    · exact hv 0x1b0 (by decide) _ L.s1b0

end Setup

end ChaCha20Poly1305.Proofs.Core.Setup
