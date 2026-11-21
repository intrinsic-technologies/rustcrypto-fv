import K256.Proofs.Sec1.Parser.Affine
import K256.Proofs.Sec1.LIR.Program
import K256.Proofs.Sec1.LIR.Generated.Values
import K256.Proofs.ParseSignature.BlackBox

namespace K256.Proofs.Sec1.Affine

open Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine
open K256.Proofs.Sec1.LIR

def storeLimbs (mem : Ram) (dst : BitVec 64) (word : Nat → BitVec 64) : Nat → Ram
  | 0 => mem
  | i + 1 => memStore (storeLimbs mem dst word i) (wordAddr dst 64 i) (word i)

def selectedPoint (mem : Ram) (sp dst : BitVec 64) : Ram :=
  let valid := memLoad mem (sp + 88) 8
  let identity := memLoad mem (sp + 80) 8
  let mask := -(valid.setWidth 64)
  let word i := memLoad mem (wordAddr sp 64 i) 64 &&& mask
  let limbs := storeLimbs mem dst word 10
  let flag := ((identity ^^^ 1) &&& (-valid)) ^^^ 1
  memStore (memStore limbs (dst + 80) flag) (dst + 88) valid

set_option maxHeartbeats 650000 in
set_option maxRecDepth 4096 in
theorem selectBlock {code : CodeMap} (hcode : ∀ x ∈ fnCode, x ∈ code)
    (args : Values Value Reg.count) (mem : Ram) (sp dst : BitVec 64)
    (rsp : args[4].get 64 = sp) (outPtr : args[3].get 64 = dst)
    (stack : Readable mem sp 89) (writable : Writable code mem dst 89) :
    ∃ next : Values Value Reg.count,
      program.runBlock (dialect code) ⟨.l121502, args, mem⟩ =
        .jump ⟨.l121599, next, selectedPoint mem sp dst⟩ ∧
      ∀ i : Fin Reg.count, i.val ∈ [3, 4, 13, 22, 39, 50, 51] → next[i] = args[i] := by
  have readGuard {k : BitVec 64} {n : Nat} (bound : k.toNat + n ≤ 89) : LoadOk mem (sp + k) n :=
    LoadOk.of_region stack (by have := stack.low; bv_omega) (by have := stack.low; bv_omega)
  have readFirst : LoadOk mem sp 8 := LoadOk.of_region stack (Nat.le_refl _) (by omega)
  have writeGuard {m : Ram} {a k pc : BitVec 64} {n len : Nat}
      (ha : a = dst + k) (win : Writable code m dst 89) (bound : k.toNat + n ≤ 89)
      (hit : (pc - 0x121502).toNat + len ≤ bytes_l121502.length) : StoreOk code m a n pc len := by
    have slot : Writable code m a n := by
      rw [ha]
      exact win.sub (by have := win.readable.low; bv_omega) (by have := win.readable.low; bv_omega)
    have guard := ParseSignature.storeOk_of_codeRange slot (fun x hx => hcode x (code_l121502 x hx)) hit
    have pcEq : 0x121502 + BitVec.ofNat 64 (pc - 0x121502).toNat = pc := by
      rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
      bv_omega
    rwa [pcEq] at guard
  refine ⟨?_, ?exec, ?preserved⟩
  case exec =>
    cfg_eval
    simp only [rsp, outPtr, readFirst, ↓reduceIte]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_
             first
             | exact readGuard (by decide)
             | refine writeGuard rfl ?_ (by decide) (by decide +kernel)
               repeat' apply Writable.memStore
               exact writable
             | refine writeGuard (k := 0) (BitVec.add_zero dst).symm ?_ (by decide) (by decide +kernel)
               exact writable)
    simp only [setWidth_mergeGPR8, selectedPoint, storeLimbs, wordAddr, Nat.reduceDiv, Nat.reduceMul,
      BitVec.add_zero, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32),
      BitVec.setWidth_eq, BitVec.and_comm (-(memLoad mem (sp + 88) 8).setWidth 64) (memLoad mem (sp + 72) 64)]
    rfl
  case preserved =>
    rintro ⟨i, hi⟩ h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem storeLimbs_read {mem : Ram} {dst : BitVec 64} {word : Nat → BitVec 64}
    (low : dst.toNat + 89 ≤ 2^32) (n : Nat) (bound : n ≤ 10) (i : Nat) (inside : i < n) :
    memLoad (storeLimbs mem dst word n) (wordAddr dst 64 i) 64 = word i := by
  have addr (j : Nat) (hj : j < 10) : (wordAddr dst 64 j).toNat = dst.toNat + 8*j := by
    change (dst + BitVec.ofNat 64 (8*j)).toNat = _
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 8*j) (by omega),
      Nat.mod_eq_of_lt (by omega)]
  induction n with
  | zero => omega
  | succ n ih =>
    rw [storeLimbs]
    by_cases eq : i = n
    · subst i
      exact memLoad_memStore_same _ _ _ (by decide) (by decide)
    · rw [memLoad_memStore_of_rangeApart]
      · exact ih (by omega) (by omega)
      · apply RangeApart.of_toNat <;> (try rw [addr n (by omega)]) <;> try rw [addr i (by omega)]
        all_goals omega

theorem selected_valid (mem : Ram) (sp dst : BitVec 64) :
    memLoad (selectedPoint mem sp dst) (dst + 88) 8 = memLoad mem (sp + 88) 8 :=
  memLoad_memStore_same _ _ _ (by decide) (by decide)

theorem selected_publicKey {mem : Ram} {sp dst : BitVec 64} {point : Standards.SECG.ECC.Curve.Point}
    (low : dst.toNat + 89 ≤ 2^32) (valid : memLoad mem (sp + 88) 8 = 1)
    (key : Parser.PublicKeyAt mem sp point) : Parser.PublicKeyAt (selectedPoint mem sp dst) dst point := by
  obtain ⟨x, y, hp, xl, yl, wx, wy, ident, rx, ry⟩ := key
  let limbs := storeLimbs mem dst (fun i => memLoad mem (wordAddr sp 64 i) 64) 10
  have after : selectedPoint mem sp dst = memStore (memStore limbs (dst + 80) (0 : BitVec 8))
      (dst + 88) (1 : BitVec 8) := by
    unfold selectedPoint
    rw [valid, ident]
    change memStore (memStore (storeLimbs mem dst _ 10) (dst + 80) (0 : BitVec 8)) (dst + 88) (1 : BitVec 8) = _
    have mask (w : BitVec 64) : w &&& (-(1#8).setWidth 64) = w := BitVec.and_allOnes
    exact congrArg (fun word => memStore (memStore (storeLimbs mem dst word 10) (dst + 80)
      (0 : BitVec 8)) (dst + 88) (1 : BitVec 8))
      (funext fun i => mask (memLoad mem (wordAddr sp 64 i) 64))
  have coord (i : Nat) (hi : i < 10) :
      memLoad (selectedPoint mem sp dst) (wordAddr dst 64 i) 64 = memLoad mem (wordAddr sp 64 i) 64 := by
    rw [after, memLoad_memStore_of_rangeApart, memLoad_memStore_of_rangeApart]
    · exact storeLimbs_read low 10 (by decide) i hi
    all_goals apply RangeApart.right_sub (m := 80) (off := 8*i) _ (by omega)
    · exact RangeApart.of_offsets (x := dst) (c := 80) (d := 0) rfl (BitVec.add_zero _).symm (by decide)
    · exact RangeApart.of_offsets (x := dst) (c := 88) (d := 0) rfl (BitVec.add_zero _).symm (by decide)
  refine ⟨x, y, hp, xl, yl, ?_, ?_, ?_, rx, ry⟩
  · intro i hi
    exact (coord i (by omega)).trans (wx i hi)
  · intro i hi
    have step (base : BitVec 64) : wordAddr (base + 40) 64 i = wordAddr base 64 (5 + i) := by
      simp only [wordAddr, Nat.mul_add, BitVec.ofNat_add, BitVec.add_assoc]
      rfl
    rw [step, coord (5+i) (by omega), ← step]
    exact wy i hi
  · rw [after, memLoad_memStore_of_rangeApart]
    · exact memLoad_memStore_same _ _ _ (by decide) (by decide)
    · exact RangeApart.of_offsets (x := dst) (c := 88) (d := 80) rfl rfl (by decide)

theorem selected_frame (mem : Ram) (sp dst : BitVec 64) (low : dst.toNat + 89 ≤ 2^32) :
    RamWriteFrame mem (selectedPoint mem sp dst) [⟨dst.toNat, 89⟩] := by
  have within (k n : Nat) (bound : k + n ≤ 89) :
      InRegions [⟨dst.toNat, 89⟩] (dst + BitVec.ofNat 64 k) n := by
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    change dst.toNat ≤ _ ∧ _ + n ≤ dst.toNat + 89 ∧ _ + n ≤ 2^64
    have ha : (dst + BitVec.ofNat 64 k).toNat = dst.toNat + k := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega),
        Nat.mod_eq_of_lt (by omega)]
    rw [ha]
    omega
  have limbs (word : Nat → BitVec 64) (n : Nat) (bound : n ≤ 10) :
      RamWriteFrame mem (storeLimbs mem dst word n) [⟨dst.toNat, 89⟩] := by
    induction n with
    | zero => exact .refl _ _
    | succ n ih => exact (ih (by omega)).memStore _ (within (8*n) 8 (by omega))
  exact ((limbs _ 10 (by decide)).memStore _ (within 80 1 (by decide))).memStore _ (within 88 1 (by decide))

end K256.Proofs.Sec1.Affine
