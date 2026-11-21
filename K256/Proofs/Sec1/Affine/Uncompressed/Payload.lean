import K256.Proofs.Sec1.Affine.Uncompressed.Entry
import K256.Proofs.Sec1.Parser.Affine

namespace K256.Proofs.Sec1.Affine.Uncompressed

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
open K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Sec1.LIR

def limbOffset (i : Nat) : Word :=
  [80, 48, 88, 56, 32, 184, 168, 144, 160, 176].getD i 0

private def destOffset (dst : Word) (i : Nat) := if i = 0 then dst else wordAddr dst 64 i

def copyLimbs (sp dst : Word) (mem : Ram) : Nat → Ram
  | 0 => mem
  | n + 1 =>
    let m := copyLimbs sp dst mem n
    memStore m (destOffset dst n) (memLoad m (sp + limbOffset n) 64)

def pointMemory (sp dst : Word) (mem : Ram) : Ram :=
  memStore (copyLimbs sp dst mem 10) (dst + 80) (0 : BitVec 8)

private theorem writeOk {m : Ram} {code : CodeMap} {addr pc : Word} {size len : Nat}
    (w : Writable code m addr size)
    (cover : ∀ v ∈ codeRange 0x120298 bytes_l120298, v ∈ code)
    (within : (pc - 0x120298).toNat + len ≤ bytes_l120298.length) :
    StoreOk code m addr size pc len := by
  have hs := K256.Proofs.ParseSignature.storeOk_of_codeRange w cover within
  have ha : 0x120298 + BitVec.ofNat 64 (pc - 0x120298).toNat = pc := by
    rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega
  rwa [ha] at hs

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1800000 in
theorem copyPoint (code : CodeMap) (args : Values Value Reg.count) (mem : Ram)
    (sp dst : Word) (rsp : args[4].get 64 = sp) (pointer : memLoad mem (sp + 208) 64 = dst)
    (stack : Writable code mem (sp - 8) 224) (out : Writable code mem dst 89)
    (cover : ∀ v ∈ codeRange 0x120298 bytes_l120298, v ∈ code) :
    let m := pointMemory sp dst mem
    ∃ regs, program.runBlock (dialect code) ⟨.l120298, args, mem⟩ =
        .call ⟨.l127d50, regs, memStore m (sp - 8) (0x12031e : Word)⟩
          (choiceResume .l12031e 0x12031e rfl) ∧
      regs[3].get 64 = dst ∧ regs[4].get 64 = sp - 8 ∧
      regs[7].get 64 = (((memLoad m (sp + 192) 64).setWidth 8) &&&
        (args[0].get 64).setWidth 8).setWidth 64 ∧
      ∀ i : Fin Reg.count, i.val ∈ [5, 12, 13, 14, 15, 22, 39, 50, 51] → regs[i] = args[i] := by
  dsimp only
  refine ⟨?regs, ?eval, ?rest⟩
  case eval =>
    cfg_eval [rsp, pointer]
    repeat' (
      refine Eq.trans (ite_eq_left ?_) ?_
      first
        | refine LoadOk.of_offsets (x := sp) (b := sp - 8) (len := 224) ?_ rfl (addr_sub _ _) (by decide)
          apply Writable.readable (code := code)
          repeat' apply Writable.memStore
          exact stack
        | refine writeOk ?_ cover (by decide +kernel)
          first
            | apply Writable.sub (b := dst) (len := 89) _ (Nat.le_refl _) (by omega)
              repeat' apply Writable.memStore
              exact out
            | refine Writable.of_offsets (x := dst) (b := dst) (len := 89) ?_ rfl (BitVec.add_zero dst).symm (by decide)
              repeat' apply Writable.memStore
              exact out
            | apply Writable.sub (b := sp - 8) (len := 224) _ (Nat.le_refl _) (by omega)
              repeat' apply Writable.memStore
              exact stack)
    rfl
  case rest =>
    refine ⟨rfl, rfl, ?flag, ?preserved⟩
    · change BitVec.setWidth 64 (BitVec.setWidth 8 (mergeGPR 8 _ _)) = _
      rw [setWidth_mergeGPR8]
      rfl
    · intro ⟨i, _⟩ hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

private theorem destOffset_eq (dst : Word) (i : Nat) : destOffset dst i = wordAddr dst 64 i := by
  cases i with
  | zero => exact (BitVec.add_zero _).symm
  | succ i => simp [destOffset]

private theorem limbAddress (dst : Word) (n : Nat) (hn : n < 10)
    (low : dst.toNat + 89 ≤ 2^32) : (wordAddr dst 64 n).toNat = dst.toNat + 8*n := by
  simp only [wordAddr, Nat.reduceDiv, BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem pointMemory_frame (sp dst : Word) (mem : Ram) (low : dst.toNat + 89 ≤ 2^32) :
    RamWriteFrame mem (pointMemory sp dst mem) [⟨dst.toNat, 81⟩] := by
  have stage (n : Nat) (hn : n ≤ 10) :
      RamWriteFrame mem (copyLimbs sp dst mem n) [⟨dst.toNat, 81⟩] := by
    induction n with
    | zero => exact RamWriteFrame.refl _ _
    | succ n ih =>
      refine (ih (by omega)).memStore _ ⟨_, List.mem_cons_self, ?_⟩
      change dst.toNat ≤ (destOffset dst n).toNat ∧ (destOffset dst n).toNat + 8 ≤ dst.toNat + 81 ∧ _
      rw [destOffset_eq, limbAddress _ _ (by omega) low]
      omega
  refine (stage 10 (by decide)).memStore _ ⟨_, List.mem_cons_self, ?_⟩
  change dst.toNat ≤ (dst + 80).toNat ∧ (dst + 80).toNat + 1 ≤ dst.toNat + 81 ∧ _
  have h : (dst + 80).toNat = dst.toNat + 80 := by bv_omega
  rw [h]
  omega

private theorem sourceWord (sp dst : Word) (mem : Ram) (n : Nat) (hn : n ≤ 10)
    (apart : RangeApart dst 81 sp 216) (off : Word) (hoff : off.toNat + 8 ≤ 216) :
    memLoad (copyLimbs sp dst mem n) (sp + off) 64 = memLoad mem (sp + off) 64 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold copyLimbs
    rw [memLoad_memStore_of_rangeApart, ih (by omega)]
    rw [destOffset_eq]
    intro i hi j hj e
    have eq : dst + BitVec.ofNat 64 (8*n+i) = sp + BitVec.ofNat 64 (off.toNat+j) := by
      simpa only [wordAddr, Nat.reduceDiv, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq,
        BitVec.add_assoc] using e
    exact apart (8*n+i) (by omega) (off.toNat+j) (by omega) eq

theorem pointMemory_limb (sp dst : Word) (mem : Ram) (i : Nat) (hi : i < 10)
    (apart : RangeApart dst 81 sp 216) :
    memLoad (pointMemory sp dst mem) (wordAddr dst 64 i) 64 =
      memLoad mem (sp + limbOffset i) 64 := by
  have offset_bound : ∀ j : Fin 10, (limbOffset j.val).toNat + 8 ≤ 216 := by decide +kernel
  have after (n : Nat) (hn : n ≤ 10) (hi' : i < n) :
      memLoad (copyLimbs sp dst mem n) (wordAddr dst 64 i) 64 =
        memLoad mem (sp + limbOffset i) 64 := by
    induction n with
    | zero => omega
    | succ n ih =>
      unfold copyLimbs
      rw [destOffset_eq]
      by_cases h : i = n
      · subst i
        rw [memLoad_memStore_same _ _ _ (by decide) (by decide)]
        exact sourceWord _ _ _ _ (by omega) apart _ (offset_bound ⟨_, hi⟩)
      · rw [memLoad_memStore_of_rangeApart, ih (by omega) (by omega)]
        apply RangeApart.of_offsets (x := dst) rfl rfl
        change 8 ≤ (BitVec.ofNat 64 (8*i) - BitVec.ofNat 64 (8*n)).toNat ∧ _
        simp only [BitVec.toNat_sub, BitVec.toNat_ofNat]
        omega
  unfold pointMemory
  rw [memLoad_memStore_of_rangeApart, after 10 (by decide) hi]
  apply RangeApart.of_offsets (x := dst) rfl rfl
  change 1 ≤ (BitVec.ofNat 64 (8*i) - 80).toNat ∧ _
  simp only [BitVec.toNat_sub, BitVec.toNat_ofNat, show (80 : Word).toNat = 80 from rfl]
  omega

theorem pointMemory_affine (sp dst : Word) (mem : Ram) (x y : Fin modulus)
    (apart : RangeApart dst 81 sp 216)
    (coords : ∀ axis : Bool, FieldRepr (Vector.ofFn fun i : Fin 5 =>
      memLoad mem (sp + limbOffset ((if axis then 5 else 0) + i.val)) 64) (if axis then y else x) 8) :
    K256.Proofs.Sec1.Parser.AffineAt (pointMemory sp dst mem) dst x y := by
  refine ⟨_, _, ?_, ?_, memLoad_memStore_same _ _ _ (by decide) (by decide), coords false, coords true⟩
  · intro i hi
    rw [Vector.getElem_ofFn]
    simpa only [Bool.false_eq_true, ite_false, Nat.zero_add] using
      pointMemory_limb sp dst mem i (by omega : i < 10) apart
  · intro i hi
    rw [Vector.getElem_ofFn]
    have e : wordAddr (dst + 40) 64 i = wordAddr dst 64 (5 + i) := by
      simp only [wordAddr, Nat.reduceDiv, Nat.mul_add, Nat.reduceMul, BitVec.ofNat_add, BitVec.add_assoc]
      rfl
    rw [e]
    exact pointMemory_limb sp dst mem (5+i) (by omega) apart

end K256.Proofs.Sec1.Affine.Uncompressed
