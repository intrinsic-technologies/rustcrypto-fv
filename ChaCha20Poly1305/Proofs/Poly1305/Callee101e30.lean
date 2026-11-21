import ChaCha20Poly1305.Proofs.Poly1305.Callee101e30.Seg0
import ChaCha20Poly1305.Proofs.Poly1305.Callee101e30.Seg11
import ChaCha20Poly1305.Proofs.Poly1305.Callee101e30.Seg24
import ChaCha20Poly1305.Proofs.Poly1305.Callee101e30.Seg41
import ChaCha20Poly1305.Proofs.Poly1305.Callee101e30.Seg56
import ChaCha20Poly1305.Proofs.Poly1305.Callee101e30.Seg73
import ChaCha20Poly1305.Proofs.Poly1305.Callee101e30.Seg89
import ChaCha20Poly1305.Proofs.Poly1305.Callee101e30.Seg103
import ChaCha20Poly1305.Proofs.Poly1305.Callee101e30.Seg112
import ChaCha20Poly1305.Proofs.Poly1305.Callee101e30.Seg124
import ChaCha20Poly1305.Proofs.Poly1305.Callee101e30.Seg138
import ChaCha20Poly1305.Proofs.Poly1305.Callee101e40

namespace ChaCha20Poly1305.Proofs.Poly1305.Callee101e30

set_option linter.unusedSimpArgs false

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Standards.RFC.ChaCha20Poly1305
open ChaCha20Poly1305.Spec.Program ChaCha20Poly1305.Proofs.Poly1305State
  ChaCha20Poly1305.Proofs.Common

section Call

open ChaCha20Poly1305.Proofs.MemoryRoutines.Machine ChaCha20Poly1305.Proofs.Poly1305.BlockArith
open ChaCha20Poly1305.Proofs.Poly1305.Callee101e40 (leNat leNat_split leNat_lt leNat_congr
  leNat_window memLoad_of_bytes foldr_leNat)

theorem entry_run [Bindings] (boundary : ReturnBoundary)
    (h1 : (0x101e32 : BitVec 64) ≠ boundary.rip) (h2 : (0x101ab0 : BitVec 64) ≠ boundary.rip)
    (s : RamState) (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s)
    (hip : s.RIP = 0x101e30) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      t.RIP = 0x101ab0 ∧ (Operand.reg 2 : Operand 64).read t = 0 ∧
      AgreesExcept [.reg 2, .flags, .rip] s t := by
  have hcx : CodeIn (codeRange 0x101e30 [0x31, 0xd2]) s :=
    program_text_slice hc 0x1e30 2 (by decide +kernel)
  obtain ⟨u, hau, hru, heu⟩ := (xor_r32_r32_effect_step 0x101e30 0xd2 (by decide)).advances hr
    hcx hip h1
  have hcu : CodeIn Extracted.programImage u :=
    heu.codeIn (Effect.Avoids.of_noMem (by
      intro c hc x; simp only [xorR32R32Effect_components, List.mem_cons, List.not_mem_nil,
        or_false] at hc; rcases hc with rfl | rfl | rfl <;> exact id) _) hc
  have hcj : CodeIn (codeRange 0x101e32 (0xE9 :: immBytes 32 0xfffffc79)) u :=
    program_text_slice hcu 0x1e32 5 (by decide +kernel)
  obtain ⟨v, hav, hrv, hev⟩ := (jmp_rel32_effect_step 0x101e32 0xfffffc79
    (by decide)).advances hru hcj heu.rip h2
  refine ⟨1 + 1, v, hau.trans hav, hrv, ?_, hev.rip, ?_, ?_⟩
  · exact hev.codeIn (fun x _ c hc' hcov ↦ by
      simp only [jmpEffect, Effect.components, List.map_nil, List.nil_append, List.mem_singleton]
        at hc'
      subst hc'
      exact hcov) hcu
  · have hw := heu.writes
    have hv : (Operand.reg 2 : Operand 64).read v = (Operand.reg 2 : Operand 64).read u :=
      hev.agrees.read (by simp [jmpEffect, Effect.components])
    change (Operand.reg 2 : Operand 64).read u = _ at hw
    rw [hv, hw]
    show BitVec.setWidth 64 ((Operand.reg 2 : Operand 32).read s ^^^
      (Operand.reg 2 : Operand 32).read s) = 0
    simp
  · apply (heu.agrees.trans hev.agrees).mono
    intro c hc
    rw [List.mem_append, xorR32R32Effect_components] at hc
    have hj : (jmpEffect 0x101e32 5 (BitVec.signExtend 64 (0xfffffc79 : BitVec 32))).components =
        [.rip] := rfl
    rw [hj] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with (rfl | rfl | rfl) | rfl
    · left; rfl
    · right; left; rfl
    · right; right; rfl
    · right; right; rfl

def envOf (s : RamState) : Env where
  sp := stackPtr s
  st := rdi.read s
  bp := rsi.read s
  rbx := (Operand.reg 3 : Operand 64).read s
  rbp := (Operand.reg 5 : Operand 64).read s
  r12 := (Operand.reg 12 : Operand 64).read s
  r13 := (Operand.reg 13 : Operand 64).read s
  r14 := (Operand.reg 14 : Operand 64).read s
  r15 := (Operand.reg 15 : Operand 64).read s
  r0 := (Operand.mem (rdi.read s + 0x10) : Operand 32).read s
  r1 := (Operand.mem (rdi.read s + 0x14) : Operand 32).read s
  r2 := (Operand.mem (rdi.read s + 0x18) : Operand 32).read s
  r3 := (Operand.mem (rdi.read s + 0x1c) : Operand 32).read s
  r4 := (Operand.mem (rdi.read s + 0x20) : Operand 32).read s
  h0 := (Operand.mem (rdi.read s + 0x24) : Operand 32).read s
  h1 := (Operand.mem (rdi.read s + 0x28) : Operand 32).read s
  h2 := (Operand.mem (rdi.read s + 0x2c) : Operand 32).read s
  h3 := (Operand.mem (rdi.read s + 0x30) : Operand 32).read s
  h4 := (Operand.mem (rdi.read s + 0x34) : Operand 32).read s
  w0 := (Operand.mem (rsi.read s) : Operand 32).read s
  w1 := (Operand.mem (rsi.read s + 0x3) : Operand 32).read s
  w2 := (Operand.mem (rsi.read s + 0x6) : Operand 32).read s
  w3 := (Operand.mem (rsi.read s + 0x9) : Operand 32).read s
  w4 := (Operand.mem (rsi.read s + 0xc) : Operand 32).read s

theorem RangeApart.toNat_disjoint {a b : BitVec 64} {n m : Nat} (h : RangeApart a n b m)
    (hn : 0 < n) (hm : 0 < m) (ha : a.toNat + n ≤ 2 ^ 64) (hb : b.toNat + m ≤ 2 ^ 64) :
    a.toNat + n ≤ b.toNat ∨ b.toNat + m ≤ a.toNat := by
  refine Decidable.byContradiction fun hc ↦ ?_
  rcases Nat.lt_or_ge a.toNat b.toNat with hab | hab
  · apply h (b.toNat - a.toNat) (by omega) 0 hm
    apply BitVec.eq_of_toNat_eq
    rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)]
    omega
  · apply h 0 hn (a.toNat - b.toNat) (by omega)
    apply BitVec.eq_of_toNat_eq
    rw [toNat_add_ofNat _ _ (by omega), toNat_add_ofNat _ _ (by omega)]
    omega

theorem stackBase_eq (s : RamState) : stackBase s = (envOf s).sp - 88 := rfl

theorem frame_of_pre {s : RamState} (hPre : CallPre s) : Frame (envOf s) s := by
  have hsl := hPre.stackLow
  have hrl := hPre.returnSlot.low
  have hra := hPre.rLimbsReadable.low
  have hha := hPre.hLimbsWritable.readable.low
  have hbl := hPre.blockReadable.low
  have hstk := hPre.stack.readable.low
  have hra' : (rAddress s).toNat + 20 ≤ 2 ^ 32 := by
    simpa [rAddress, rOffset] using hra
  have hha' : (hAddress s).toNat + 20 ≤ 2 ^ 32 := by
    simpa [hAddress, hOffset] using hha
  have hbl' : (rsi.read s).toNat + 16 ≤ 2 ^ 32 := by exact hbl
  simp only [rAddress, hAddress, rOffset, hOffset, stackBytes] at hra hha hsl
  have hbase : (stackBase s).toNat = (stackPtr s).toNat - 88 := by
    rw [stackBase_eq]; exact sp88_toNat hsl
  have d1 := RangeApart.toNat_disjoint hPre.rApart (by decide) (by decide)
    (by omega) (by simp only [stackBytes] at hstk ⊢; omega)
  have d2 := RangeApart.toNat_disjoint hPre.hApart (by decide) (by decide)
    (by omega) (by simp only [stackBytes] at hstk ⊢; omega)
  have d3 := RangeApart.toNat_disjoint hPre.blockApart (by decide) (by decide)
    (by omega) (by simp only [stackBytes] at hstk ⊢; omega)
  simp only [rAddress, hAddress, rOffset, hOffset, stackBytes, hbase] at d1 d2 d3
  have hrh : (rdi.read s + 0x24).toNat = (rdi.read s + 0x10).toNat + 20 := by bv_omega
  refine ⟨⟨hsl, hrl⟩, by simp only [envOf]; omega, hbl, ?_, ?_, hPre.stack, hPre.returnSlot,
    hPre.rLimbsReadable, hPre.hLimbsWritable, hPre.blockReadable,
    rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · simp only [envOf]; omega
  · simp only [envOf]; omega

theorem cut0_of_entry {s t : RamState} (ht : (Operand.reg 2 : Operand 64).read t = 0)
    (ha : AgreesExcept [.reg 2, .flags, .rip] s t) : Write.AllHold t (cut0 (envOf s)) := by
  have hr : ∀ r : BitVec 5, r ≠ 2 → (Operand.reg r : Operand 64).read t =
      (Operand.reg r : Operand 64).read s := by
    intro r hr
    have hr' : r ≠ (2 : BitVec 5) := by
      intro he
      apply hr
      exact BitVec.eq_of_toNat_eq (by simpa using congrArg BitVec.toNat he)
    apply ha.read
    simp only [List.mem_cons, List.not_mem_nil, or_false]
    simpa using hr' 
  simp only [cut0, Write.AllHold, envOf]
  refine ⟨?_, ?_, ?_, ht, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [stackPtr_eq_read]; exact hr 4 (by decide)
  · exact hr 7 (by decide)
  · exact hr 6 (by decide)
  · exact hr 3 (by decide)
  · exact hr 5 (by decide)
  · exact hr 12 (by decide)
  · exact hr 13 (by decide)
  · exact hr 14 (by decide)
  · exact hr 15 (by decide)

def blockByte (s : RamState) (j : Nat) : Nat :=
  if j < 16 then ((s.external[rsi.read s + BitVec.ofNat 64 j]?).getD 0).toNat else 0

theorem blockByte_lt (s : RamState) (j : Nat) : blockByte s j < 256 := by
  unfold blockByte
  split
  · exact UInt8.toNat_lt _
  · decide

def blockNum (s : RamState) : Nat := leNat (blockByte s) 16

theorem block_word (s : RamState) (d : Nat) (hd : d + 4 ≤ 16) :
    ((Operand.mem (rsi.read s + BitVec.ofNat 64 d) : Operand 32).read s).toNat =
      blockNum s / 2 ^ (8 * d) % 2 ^ 32 := by
  change (memLoad s.external (rsi.read s + BitVec.ofNat 64 d) (8 * 4)).toNat = _
  rw [memLoad_of_bytes (f := fun j ↦ blockByte s (d + j)) (fun j ↦ blockByte_lt s _)
    (fun i hi ↦ by
      rw [add_ofNat_add_ofNat]
      simp only [blockByte, show d + i < 16 by omega, ↓reduceIte, memByte,
        PhysicalMemory.read, UInt8.ofNat_toNat])]
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by
    have := leNat_lt (fun j ↦ blockByte_lt s (d + j)) 4
    simpa using this)]
  have hw := leNat_window (blockByte_lt s) d 4 (12 - d)
  rw [show d + (4 + (12 - d)) = 16 by omega] at hw
  rw [blockNum, Nat.pow_mul, ← hw]

theorem blockNum_lt (s : RamState) : blockNum s < 2 ^ 128 := by
  have := leNat_lt (blockByte_lt s) 16
  unfold blockNum
  simpa using this

theorem block_append_one (s : RamState) :
    leBytesToNum (block s ++ ⟨#[0x01]⟩) = blockNum s + 2 ^ 128 := by
  unfold leBytesToNum
  rw [← Array.foldr_toList, foldr_leNat]
  have hsize : (block s).data.toList.length = 16 := by simp [block]
  have hlen : (block s ++ ⟨#[0x01]⟩).data.toList.length = 16 + 1 := by
    rw [ByteArray.data_append, Array.toList_append, List.length_append, hsize]
    rfl
  have hl : ∀ j < 16, (block s ++ ⟨#[0x01]⟩).data.toList.getD j 0 =
      (s.external[rsi.read s + BitVec.ofNat 64 j]?).getD 0 := by
    intro j hj
    rw [List.getD_eq_getElem?_getD, ByteArray.data_append, Array.toList_append,
      List.getElem?_append_left (by rw [hsize]; omega)]
    simp only [block, Array.toList_ofFn, List.getElem?_ofFn, hj, ↓reduceDIte, Option.getD_some]
  have hl16 : (block s ++ ⟨#[0x01]⟩).data.toList.getD 16 0 = 1 := by
    rw [List.getD_eq_getElem?_getD, ByteArray.data_append, Array.toList_append,
      List.getElem?_append_right (by simp [hsize]), hsize]
    rfl
  rw [hlen, leNat_split]
  have h1 : leNat (fun j ↦ ((block s ++ ⟨#[0x01]⟩).data.toList.getD j 0).toNat) 16 =
      blockNum s := by
    apply leNat_congr
    intro j hj
    rw [hl j hj]
    simp [blockByte, hj]
  have h2 : leNat (fun j ↦ ((block s ++ ⟨#[0x01]⟩).data.toList.getD (16 + j) 0).toNat) 1 = 1 := by
    simp only [leNat, Nat.add_zero, hl16]
    rfl
  rw [h1, h2]

theorem msg_value (s : RamState) :
    let e := envOf s
    limbValue (msgLimbs (limbs5 e.w0 e.w1 e.w2 e.w3 e.w4)) = blockNum s := by
  intro e
  have w0 := block_word s 0 (by decide)
  have w1 := block_word s 3 (by decide)
  have w2 := block_word s 6 (by decide)
  have w3 := block_word s 9 (by decide)
  have w4 := block_word s 12 (by decide)
  have hN := blockNum_lt s
  rw [show rsi.read s + BitVec.ofNat 64 0 = rsi.read s from BitVec.add_zero _] at w0
  simp only [limbValue, msgLimbs, limbs5_0, limbs5_1, limbs5_2, limbs5_3, limbs5_4, mask26_toNat,
    BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  change (e.w0).toNat = _ at w0
  change (e.w1).toNat = _ at w1
  change (e.w2).toNat = _ at w2
  change (e.w3).toNat = _ at w3
  change (e.w4).toNat = _ at w4
  rw [w0, w1, w2, w3, w4]
  generalize blockNum s = N at *
  omega

theorem limbs_eq {s : RamState} {state : BitVec 64} {l : Fin 5 → BitVec 32}
    (hbase : BitVec 64) (h0 : word32 s (state + hbase) = l 0)
    (h1 : word32 s (state + hbase + 4) = l 1) (h2 : word32 s (state + hbase + 8) = l 2)
    (h3 : word32 s (state + hbase + 12) = l 3) (h4 : word32 s (state + hbase + 16) = l 4) :
    limbsAt s (state + hbase) = l := by
  funext i
  match i with
  | ⟨0, _⟩ => simpa [limbsAt] using h0
  | ⟨1, _⟩ => simpa [limbsAt] using h1
  | ⟨2, _⟩ => simpa [limbsAt] using h2
  | ⟨3, _⟩ => simpa [limbsAt] using h3
  | ⟨4, _⟩ => simpa [limbsAt] using h4

theorem clamp_lt (key : Nat) : clamp key < 2 ^ 124 := by
  unfold clamp
  exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)

end Call

section CallProof

open ChaCha20Poly1305.Proofs.MemoryRoutines.Machine ChaCha20Poly1305.Proofs.Poly1305.BlockArith

theorem incode_body {pc : BitVec 64} (h1 : 0x101ab0 ≤ pc.toNat) (h2 : pc.toNat < 0x101cd2) :
    InCode pc := .inr ⟨by simpa [bodyEntry] using h1, h2⟩

theorem limbs5_ext {l : Fin 5 → BitVec 32} :
    limbs5 (l 0) (l 1) (l 2) (l 3) (l 4) = l := by
  funext i
  match i with
  | ⟨0, _⟩ => rfl
  | ⟨1, _⟩ => rfl
  | ⟨2, _⟩ => rfl
  | ⟨3, _⟩ => rfl
  | ⟨4, _⟩ => rfl

theorem limbsAt_eq (s : RamState) (base : BitVec 64) :
    limbsAt s base = limbs5 (word32 s base) (word32 s (base + 4)) (word32 s (base + 8))
      (word32 s (base + 12)) (word32 s (base + 16)) := by
  funext i
  match i with
  | ⟨0, _⟩ => simp [limbsAt, limbs5]
  | ⟨1, _⟩ => simp [limbsAt, limbs5]
  | ⟨2, _⟩ => simp [limbsAt, limbs5]
  | ⟨3, _⟩ => simp [limbsAt, limbs5]
  | ⟨4, _⟩ => simp [limbsAt, limbs5]

theorem call_value (s : RamState) (hPre : CallPre s) {v : RamState}
    (hv : hLimbs v (rdi.read s) = limbs5 (fin_h0 (envOf s)) (fin_h1 (envOf s)) (fin_h2 (envOf s))
      (fin_h3 (envOf s)) (fin_h4 (envOf s))) :
    BoundedLimbs (hLimbs v (rdi.read s)) ∧
    limbValue (hLimbs v (rdi.read s)) % prime =
      ((limbValue (hLimbs s (rdi.read s)) + leBytesToNum (block s ++ ⟨#[0x01]⟩)) *
        limbValue (rLimbs s (rdi.read s))) % prime := by
  have hR : rLimbs s (rdi.read s) = limbs5 (envOf s).r0 (envOf s).r1 (envOf s).r2 (envOf s).r3 (envOf s).r4 := by
    rw [rLimbs, limbsAt_eq]
    simp only [rOffset, word32, BitVec.add_assoc, BitVec.reduceAdd]
    rfl
  have hH : hLimbs s (rdi.read s) = limbs5 (envOf s).h0 (envOf s).h1 (envOf s).h2 (envOf s).h3 (envOf s).h4 := by
    rw [hLimbs, limbsAt_eq]
    simp only [hOffset, word32, BitVec.add_assoc, BitVec.reduceAdd]
    rfl
  have hB : limbs5 (fin_h0 (envOf s)) (fin_h1 (envOf s)) (fin_h2 (envOf s)) (fin_h3 (envOf s)) (fin_h4 (envOf s)) =
      blockStep (limbs5 (envOf s).r0 (envOf s).r1 (envOf s).r2 (envOf s).r3 (envOf s).r4) (limbs5 (envOf s).h0 (envOf s).h1 (envOf s).h2 (envOf s).h3 (envOf s).h4)
        (limbs5 (envOf s).w0 (envOf s).w1 (envOf s).w2 (envOf s).w3 (envOf s).w4) 0x1000000 := by
    rw [fin_eq0, fin_eq1, fin_eq2, fin_eq3, fin_eq4, limbs5_ext]
  obtain ⟨key, hkey⟩ := hR ▸ hPre.rClamped
  have hb := hH ▸ hPre.hBounded
  have hc := clamp_lt key
  have k0 := hkey 0
  have k1 := hkey 1
  have k2 := hkey 2
  have k3 := hkey 3
  have k4 := hkey 4
  simp only [limbs5_0, limbs5_1, limbs5_2, limbs5_3, limbs5_4] at k0 k1 k2 k3 k4
  obtain ⟨b0, b1, b2, b3, b4⟩ := hb
  simp only [limbs5_0, limbs5_1, limbs5_2, limbs5_3, limbs5_4] at b0 b1 b2 b3 b4
  have hspec := blockStep_spec (limbs5 (envOf s).r0 (envOf s).r1 (envOf s).r2 (envOf s).r3 (envOf s).r4)
    (limbs5 (envOf s).h0 (envOf s).h1 (envOf s).h2 (envOf s).h3 (envOf s).h4) (limbs5 (envOf s).w0 (envOf s).w1 (envOf s).w2 (envOf s).w3 (envOf s).w4) 0x1000000
    (by simp only [limbs5_0]; rw [k0]; omega) (by simp only [limbs5_1]; rw [k1]; omega)
    (by simp only [limbs5_2]; rw [k2]; omega) (by simp only [limbs5_3]; rw [k3]; omega)
    (by simp only [limbs5_4]; rw [k4]; change clamp key / 2 ^ 104 % 2 ^ 26 < 2 ^ 20; omega)
    b0 b1 b2 b3 b4 (by decide)
  rw [hv, hB, hH, hR, block_append_one, ← msg_value s]
  refine ⟨hspec.1, ?_⟩
  rw [hspec.2]
  have hx : (0x1000000 : BitVec 32).toNat = 2 ^ 24 := rfl
  rw [hx, show 2 ^ 104 * 2 ^ 24 = 2 ^ 128 from rfl, Nat.add_assoc]

end CallProof

section CallMain

open ChaCha20Poly1305.Proofs.MemoryRoutines.Machine ChaCha20Poly1305.Proofs.Poly1305.BlockArith

set_option maxHeartbeats 2000000 in
theorem call [bindings : Bindings] (boundary : ReturnBoundary) {s : RamState}
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s) (hPre : CallPre s)
    (hBoundaryOutside : ¬ InCode boundary.rip)
    (hBoundaryReturn : boundary.rip ≠ (returnBoundary s).rip) :
    ∃ fuel t, Advances boundary fuel s t ∧ CallResult s t := by
  have hneB : ∀ pc : BitVec 64, 0x101ab0 ≤ pc.toNat → pc.toNat < 0x101cd2 →
      pc ≠ boundary.rip := by
    intro pc h1 h2 he
    exact hBoundaryOutside (he ▸ incode_body h1 h2)
  have hE1 : (0x101e32 : BitVec 64) ≠ boundary.rip := by
    intro he
    exact hBoundaryOutside (he ▸ .inl ⟨by decide, by decide⟩)
  have hE2 : (0x101ab0 : BitVec 64) ≠ boundary.rip := hneB _ (by decide) (by decide)
  obtain ⟨n1, t1, ha1, hr1, hc1, hip1, hdx, hag1⟩ :=
    entry_run boundary hE1 hE2 s hReady hCode hPre.rip
  have hF0 := frame_of_pre hPre
  have hF1 : Frame (envOf s) t1 := hF0.of_agrees (hag1.mono (by simp [bodyChanges]))
  have hW1 : Write.AllHold t1 (cut0 (envOf s)) := cut0_of_entry hdx hag1
  have hseg := (((((((((((seg0 boundary (envOf s) hneB).seq (seg11 boundary (envOf s) hneB)).seq
    (seg24 boundary (envOf s) hneB)).seq (seg41 boundary (envOf s) hneB)).seq
    (seg56 boundary (envOf s) hneB)).seq (seg73 boundary (envOf s) hneB)).seq
    (seg89 boundary (envOf s) hneB)).seq (seg103 boundary (envOf s) hneB)).seq
    (seg112 boundary (envOf s) hneB)).seq (seg124 boundary (envOf s) hneB)).seqF
    (seg138 boundary (envOf s) hneB))
  obtain ⟨n2, u, ha2, hr2, hc2, hip2, hW2, hag2⟩ := hseg t1 hr1 hc1 hip1 hF1 hW1
  simp only [cut153, Write.AllHold] at hW2
  obtain ⟨u4, u3, u5, u12, u13, u14, u15, m0, m1, m2, m3, m4⟩ := hW2
  have hag := hag1.trans hag2
  have hsl := hPre.stackLow
  have hrl := hPre.returnSlot.low
  have hha := hPre.hLimbsWritable.readable.low
  have hha' : (hAddress s).toNat + 20 ≤ 2 ^ 32 := by
    simpa [hAddress, hOffset] using hha
  have hstk := hPre.stack.readable.low
  simp only [hAddress, hOffset, stackBytes] at hha hsl hstk
  have hbase : (stackBase s).toNat = (stackPtr s).toNat - 88 := by
    rw [stackBase_eq]; exact sp88_toNat hsl
  have d2 := RangeApart.toNat_disjoint hPre.hApart (by decide) (by decide)
    (by omega) (by simp only [stackBytes] at hstk ⊢; omega)
  simp only [hAddress, hOffset, stackBytes, hbase] at d2
  have hbound : ((envOf s).st + 0x24).toNat + 20 ≤ 2 ^ 32 := by
    simpa [envOf, hAddress, hOffset] using hha'
  have hslot : ∀ i < 8, u.external[stackPtr s + BitVec.ofNat 64 i]? =
      s.external[stackPtr s + BitVec.ofNat 64 i]? := by
    intro i hi
    have hx : (stackPtr s + BitVec.ofNat 64 i).toNat = (stackPtr s).toNat + i :=
      toNat_add_ofNat _ _ (by omega)
    apply hag.byte
    intro c hc hcov
    simp only [finalChanges, bodyChanges, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false, List.mem_append] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hmem
    all_goals first
      | exact hcov
      | (simp only [Component.Covers] at hcov; contradiction)
      | skip
    · simp only [Component.Covers] at hcov
      obtain ⟨j, hj, he⟩ := hcov
      have := congrArg BitVec.toNat he
      rw [hx, toNat_add_ofNat _ _ (by rw [sp88_toNat hsl]; omega), sp88_toNat hsl] at this
      simp only [envOf] at this
      omega
    · rcases hmem with hmem | hmem
      all_goals
        simp only [Component.Covers] at hcov
        obtain ⟨j, hj, he⟩ := hcov
        have hh := congrArg BitVec.toNat he
        first
        | have hjaddr : ((envOf s).st + 0x24).toNat + j < 2 ^ 64 := by omega
          rw [hx, toNat_add_ofNat _ _ hjaddr] at hh
          simp only [envOf] at hh
          omega
        | rw [hx, toNat_add_ofNat _ _ (by rw [sp88_toNat hsl]; omega), sp88_toNat hsl] at hh
          simp only [envOf] at hh
          omega
  have hsp : stackPtr u = stackPtr s := by rw [stackPtr_eq_read, u4]; rfl
  have htop : stackTop u = (returnBoundary s).rip := by
    change memLoad u.external (stackPtr u) 64 = memLoad s.external (stackPtr s) 64
    rw [hsp]
    apply memLoad_congr
    intro i hi
    exact congrArg (fun b : Option UInt8 ↦ b.getD 0) (hslot i hi)
  have hread : MemReadable u (stackPtr u) 8 := by
    rw [hsp]
    exact ⟨hPre.returnSlot.low, fun i hi ↦ hag.grow _ (hPre.returnSlot.mem i hi)⟩
  have hcr : CodeIn (codeRange 0x101cd1 [0xc3]) u :=
    program_text_slice hc2 0x1cd1 1 (by decide +kernel)
  obtain ⟨v, hstep, hrv, hev⟩ := ret_effect_step 0x101cd1 u hr2 hcr
    ⟨⟨hip2, hread⟩, by rw [htop]; exact hPre.returnLow⟩
  have hext : v.external = u.external := hev.agrees.external (by simp [Component.Covers])
  have hregv : ∀ r : BitVec 5, r ≠ 4 → (Operand.reg r : Operand 64).read v =
      (Operand.reg r : Operand 64).read u := by
    intro r hr
    have hr' : r ≠ (4 : BitVec 5) := by
      intro he
      apply hr
      exact BitVec.eq_of_toNat_eq (by simpa using congrArg BitVec.toNat he)
    apply hev.agrees.read
    intro hm
    have hm' : r = (4 : BitVec 5) ∨ Component.reg r = Component.rip := by
      simpa [retEffect_components] using hm
    rcases hm' with hm' | hm'
    · exact hr' (by exact BitVec.eq_of_toNat_eq (by simpa using congrArg BitVec.toNat hm'))
    · cases hm'
  have hsaved : ∀ r : BitVec 5, (r = 3 ∨ r = 5 ∨ r = 12 ∨ r = 13 ∨ r = 14 ∨ r = 15) →
      (Operand.reg r : Operand 64).read v = (Operand.reg r : Operand 64).read s := by
    intro r hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · rw [hregv 3 (by decide), u3]; rfl
    · rw [hregv 5 (by decide), u5]; rfl
    · rw [hregv 12 (by decide), u12]; rfl
    · rw [hregv 13 (by decide), u13]; rfl
    · rw [hregv 14 (by decide), u14]; rfl
    · rw [hregv 15 (by decide), u15]; rfl
  have hv : hLimbs v (rdi.read s) = limbs5 (fin_h0 (envOf s)) (fin_h1 (envOf s))
      (fin_h2 (envOf s)) (fin_h3 (envOf s)) (fin_h4 (envOf s)) := by
    have hr : ∀ a : BitVec 64, word32 v a = (Operand.mem a : Operand 32).read u := fun a ↦ by
      change memLoad v.external a 32 = memLoad u.external a 32
      rw [hext]
    rw [hLimbs, limbsAt_eq]
    simp [hOffset, hr, BitVec.add_assoc, BitVec.reduceAdd]
    have m0' : (Operand.mem (rdi.read s + 0x24) : Operand 32).read u = fin_h0 (envOf s) := by simpa [envOf] using m0
    have m1' : (Operand.mem (rdi.read s + 0x28) : Operand 32).read u = fin_h1 (envOf s) := by simpa [envOf] using m1
    have m2' : (Operand.mem (rdi.read s + 0x2c) : Operand 32).read u = fin_h2 (envOf s) := by simpa [envOf] using m2
    have m3' : (Operand.mem (rdi.read s + 0x30) : Operand 32).read u = fin_h3 (envOf s) := by simpa [envOf] using m3
    have m4' : (Operand.mem (rdi.read s + 0x34) : Operand 32).read u = fin_h4 (envOf s) := by simpa [envOf] using m4
    change limbs5
      ((Operand.mem (rdi.read s + 0x24) : Operand 32).read u)
      ((Operand.mem (rdi.read s + 0x28) : Operand 32).read u)
      ((Operand.mem (rdi.read s + 0x2c) : Operand 32).read u)
      ((Operand.mem (rdi.read s + 0x30) : Operand 32).read u)
      ((Operand.mem (rdi.read s + 0x34) : Operand 32).read u) = _
    simp only [m0', m1', m2', m3', m4']
  obtain ⟨hbd, hval⟩ := call_value s hPre hv
  refine ⟨n1 + n2 + 1, v, (ha1.trans ha2).trans (Advances.of_step hstep (.inl ?_)), ?_⟩
  · rw [hev.rip]
    dsimp [retEffect]
    rw [htop]
    exact Ne.symm hBoundaryReturn
  refine ⟨hrv, hev.codeIn (Effect.avoids_of_components_reg_rip (retEffect_components u) _) hc2,
    hev.rip.trans htop, ?_, ?_, ?_, hbd, hval⟩
  · have hw := hev.writes
    change (Operand.reg 4 : Operand 64).read v = stackPtr u + 8 at hw
    rw [stackPtr_eq_read, hw, hsp]
  · refine ((hag.trans hev.agrees).narrow fun c hc hn ↦ ?_)
    simp only [finalChanges, bodyChanges, List.cons_append, List.nil_append, List.mem_cons,
      List.not_mem_nil, or_false, List.mem_append, retEffect_components] at hc
    simp only [callChanges, stackBase, hAddress, hOffset, stackBytes, envOf, List.mem_cons,
      List.not_mem_nil, or_false] at hn
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | (exfalso; apply hn; simp [callChanges, stackBase, hAddress, hOffset, stackBytes, envOf]; done)
      | (simp [Component.Agrees, callChanges, stackBase, hAddress, hOffset, stackBytes, envOf] at *)
      | (show v.GPR[gprIndex _] = s.GPR[gprIndex _]
         rw [← Operand.read_reg64, ← Operand.read_reg64]
         exact hsaved _ (by decide))
    all_goals first
      | exact hsaved.left
      | exact hsaved.right.left
      | exact hsaved.right.right.left
      | exact hsaved.right.right.right.left
      | exact hsaved.right.right.right.right.left
      | exact hsaved.right.right.right.right.right

  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact hsaved 3 (by decide)
    · exact hsaved 5 (by decide)
    · exact hsaved 12 (by decide)
    · exact hsaved 13 (by decide)
    · exact hsaved 14 (by decide)
    · exact hsaved 15 (by decide)

end CallMain

end ChaCha20Poly1305.Proofs.Poly1305.Callee101e30
