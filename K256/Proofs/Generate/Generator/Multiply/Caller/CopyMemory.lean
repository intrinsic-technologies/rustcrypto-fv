import K256.Proofs.Generate.Generator.Multiply.Caller.FirstCopy
import K256.Proofs.Generate.Generator.Multiply.Caller.SecondCopy
import K256.Proofs.Generate.Generator.Multiply.Caller.CoreCall
import K256.Proofs.Sec1.Parser.Result.Copy

namespace K256.Proofs.Generate.Generator.Multiply.Caller

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR

private theorem copyStore {fr : Activation} {m : Ram} {w : Nat} {p : BitVec 64}
    (room : 9768 ≤ fr.rsp.toNat) (low : fr.low = fr.rsp - 9768)
    (frame : RamWriteFrame fr.original m [fr.region]) (v : BitVec w)
    (lo : fr.rsp.toNat - 9768 ≤ p.toNat) (hi : p.toNat + w / 8 ≤ fr.rsp.toNat) :
    RamWriteFrame fr.original (memStore m p v) [fr.region] := by
  apply frame.memStore
  refine ⟨_, List.mem_singleton_self _, ?_⟩
  have ln : fr.low.toNat = fr.rsp.toNat - 9768 := by
    rw [low, BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; exact room)]
    rfl
  simp only [InRegion, Activation.region, ln]
  have := fr.rsp.isLt
  omega

private theorem copyOffset {fr : Activation} (room : 9768 ≤ fr.rsp.toNat)
    (k : Nat) (hk : k ≤ 5960) :
    (fr.rsp - 5960 + BitVec.ofNat 64 k).toNat = fr.rsp.toNat - 5960 + k := by
  have hs : (fr.rsp - 5960).toNat = fr.rsp.toNat - 5960 := by
    rw [BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change 5960 ≤ _; omega))]
    rfl
  rw [BitVec.toNat_add, hs, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := k) (by omega),
    Nat.mod_eq_of_lt (by have := fr.rsp.isLt; omega)]

local macro "stack_bound" : tactic => `(tactic| (
  simp only [BitVec.toNat_sub, BitVec.toNat_add, BitVec.reduceToNat, BitVec.toNat_ofNat,
    Nat.reduceDiv, Nat.reduceMul]
  omega))

local macro "copy_frame" : tactic => `(tactic| (
  repeat' first | with_reducible assumption | with_reducible apply RamWriteFrame.refl |
    with_reducible refine copyStore (by assumption) (by assumption) ?_ _ (by stack_bound) (by stack_bound)))

theorem firstCopyFrame {fr : Activation} (room : 9768 ≤ fr.rsp.toNat)
    (low : fr.low = fr.rsp - 9768) :
    RamWriteFrame fr.original (firstCopyMemory fr) [fr.region] := by
  unfold firstCopyMemory firstCopyRecord firstCopySaved memCopy
  copy_frame

private theorem identityCopiesFrame {fr : Activation} {m : Ram} (room : 9768 ≤ fr.rsp.toNat)
    (low : fr.low = fr.rsp - 9768) (frame : RamWriteFrame fr.original m [fr.region])
    (i : Nat) (bound : i ≤ 16) :
    RamWriteFrame fr.original (identityCopies m (fr.rsp - 5960) i) [fr.region] := by
  induction i with
  | zero => exact frame
  | succ i ih =>
    have prev := ih (by omega)
    unfold identityCopies memCopy
    refine copyStore room low prev _ ?_ ?_ <;> rw [copyOffset room _ (by omega)] <;> omega

theorem secondCopyFrame {fr : Activation} {m : Ram} (room : 9768 ≤ fr.rsp.toNat)
    (low : fr.low = fr.rsp - 9768) (frame : RamWriteFrame fr.original m [fr.region]) :
    RamWriteFrame fr.original (secondCopyMemory m (fr.rsp - 5960)) [fr.region] := by
  have := identityCopiesFrame room low frame 16 (by decide)
  unfold secondCopyMemory memCopy
  copy_frame

theorem tableCoreFrame {fr : Activation} {m : Ram} (room : 9768 ≤ fr.rsp.toNat)
    (low : fr.low = fr.rsp - 9768) (frame : RamWriteFrame fr.original m [fr.region]) :
    let sp := fr.rsp - 5960
    RamWriteFrame fr.original (coreCallMemory (tableCopyMemory m sp) sp) [fr.region] := by
  dsimp only
  unfold coreCallMemory tableCopyMemory memCopy
  copy_frame

private theorem copyApart {sp a b : BitVec 64} {x y n k : Nat}
    (ha : a = sp + BitVec.ofNat 64 x) (hb : b = sp + BitVec.ofNat 64 y)
    (hx : x + n ≤ 2 ^ 64) (hy : y + k ≤ 2 ^ 64) (sep : x + n ≤ y ∨ y + k ≤ x) :
    RangeApart a n b k := by
  intro i hi j hj he
  rw [ha, hb, BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add,
    BitVec.add_right_inj] at he
  have := congrArg BitVec.toNat he
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : x + i < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : y + j < 2 ^ 64)] at this
  omega

private theorem fixedApart {sp a : BitVec 64} {x : BitVec 64} {y n k : Nat}
    (ha : a = sp + x) (hx : x.toNat + n ≤ 2 ^ 64) (hy : y + k ≤ 2 ^ 64)
    (sep : x.toNat + n ≤ y ∨ y + k ≤ x.toNat) :
    RangeApart a n (sp + BitVec.ofNat 64 y) k :=
  copyApart (x := x.toNat) (by simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using ha) rfl hx hy sep

local macro "copy_apart" sp:term : tactic => `(tactic| (
  apply fixedApart (sp := $sp)
  · first | apply addr_sub | apply addr_self | rfl
  all_goals simp only [BitVec.reduceSub, BitVec.reduceToNat, Nat.reduceDiv, Nat.reduceMul,
    BitVec.toNat_ofNat] <;> omega))

private theorem identityCopiesLoad {m : Ram} {sp : BitVec 64} (i k : Nat)
    (bound : i ≤ 16) (lower : 3848 ≤ k) (upper : k ≤ 5952) :
    memLoad (identityCopies m sp i) (sp + BitVec.ofNat 64 k) 64 =
    memLoad m (sp + BitVec.ofNat 64 k) 64 := by
  induction i with
  | zero => rfl
  | succ i ih =>
    rw [identityCopies, memCopy, memLoad_memStore_of_rangeApart]
    · exact ih (by omega)
    · exact copyApart (x := 1928 + 120 * i) rfl rfl (by omega) (by omega) (by omega)

local macro "skip_stores" sp:term : tactic => `(tactic| (
  repeat' with_reducible refine (memLoad_memStore_of_rangeApart _ _ _ _ _ (by copy_apart $sp)).trans ?_))

private theorem laterCopiesLoad {m : Ram} (sp : BitVec 64) (k : Nat)
    (protectedRange : (3848 ≤ k ∧ k + 8 ≤ 4000) ∨ (5920 ≤ k ∧ k ≤ 5952)) :
    let n := tableCopyMemory (secondCopyMemory m sp) sp
    memLoad (coreCallMemory n sp) (sp + BitVec.ofNat 64 k) 64 =
      memLoad m (sp + BitVec.ofNat 64 k) 64 := by
  dsimp only
  unfold coreCallMemory tableCopyMemory secondCopyMemory memCopy
  skip_stores sp
  exact identityCopiesLoad 16 k (by decide) (by omega) (by omega)

private theorem generatorRecord (fr : Activation) (i : Fin 15) :
    let sp := fr.rsp - 5960
    memLoad (firstCopyMemory fr) (sp + 3848 + BitVec.ofNat 64 (8 * i.val)) 64 =
      memLoad (firstCopySaved fr) (wordAddr 0x202bc8 64 i.val) 64 := by
  let sp := fr.rsp - 5960
  dsimp only
  unfold firstCopyMemory
  rw [Sec1.Parser.Result.memLoad_memCopy _ _ _ (by decide) (by have := i.isLt; omega)]
  change memLoad (memStore (firstCopyRecord fr) (sp - 8) _) (sp + 8 + _) 64 = _
  have addr : sp + 8 + BitVec.ofNat 64 (8 * i.val) = sp + BitVec.ofNat 64 (8 + 8 * i.val) := by
    rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl
  rw [addr]
  unfold firstCopyRecord
  have := i.isLt
  skip_stores sp
  rw [← addr]
  exact Sec1.Parser.Result.memLoad_memCopy _ _ _ (by decide) (by omega)

set_option maxRecDepth 4096 in
private theorem scalarRecord {fr : Activation} {d : Nat}
    (words : WordsAt fr.original fr.rsi 64 (scalarWords d)) :
    WordsAt (firstCopyMemory fr) (fr.rsp - 5960 + 3968) 64 (scalarWords d) := by
  intro i hi
  have src := words i hi
  let sp := fr.rsp - 5960
  have addr : wordAddr (sp + 3968) 64 i =
      sp + 3848 + BitVec.ofNat 64 (120 + 8 * i) := by
    simp only [wordAddr, Nat.reduceDiv, BitVec.ofNat_add, BitVec.add_assoc]
    rw [← BitVec.add_assoc (3848 : BitVec 64)]; rfl
  change memLoad (firstCopyMemory fr) (wordAddr (sp + 3968) 64 i) 64 = _
  rw [addr]
  unfold firstCopyMemory
  rw [Sec1.Parser.Result.memLoad_memCopy _ _ _ (by decide) (by omega)]
  unfold firstCopyRecord
  rcases (show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega) with rfl | rfl | rfl | rfl <;>
    refine Eq.trans ?_ src <;> simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceDiv, wordAddr,
      BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat, BitVec.add_zero] <;> segment_words [] <;> rfl

private theorem savedLoad (fr : Activation) (k : Nat) (lo : 5920 ≤ k) (hi : k ≤ 5952) :
    let sp := fr.rsp - 5960
    memLoad (firstCopyMemory fr) (sp + BitVec.ofNat 64 k) 64 =
      memLoad (firstCopySaved fr) (sp + BitVec.ofNat 64 k) 64 := by
  let sp := fr.rsp - 5960
  dsimp only
  unfold firstCopyMemory firstCopyRecord memCopy
  skip_stores sp
  rfl

abbrev callerMemory (fr : Activation) : Ram :=
  let sp := fr.rsp - 5960
  coreCallMemory (tableCopyMemory (secondCopyMemory (firstCopyMemory fr) sp) sp) sp

theorem callerMemoryFacts {fr : Activation} {a : Registers} {d : Nat}
    (atoms : Atom.All Extracted.programImage a fr.original (Fn10ee80.frameAt .l10ee80 fr))
    (image : ∀ b ∈ Extracted.programImage, fr.original[b.1]? = some b.2)
    (room : 9768 ≤ fr.rsp.toNat) (low : fr.low = fr.rsp - 9768)
    (words : WordsAt fr.original fr.rsi 64 (scalarWords d)) :
    let sp := fr.rsp - 5960
    let m := callerMemory fr
    (∀ i : Fin 15, memLoad m (wordAddr (sp + 3848) 64 i.val) 64 =
      memLoad m (wordAddr 0x202bc8 64 i.val) 64) ∧
    WordsAt m (sp + 3968) 64 (scalarWords d) ∧
    memLoad m (fr.rsp - 40) 64 = fr.rbx ∧ memLoad m (fr.rsp - 32) 64 = fr.r12 ∧
    memLoad m (fr.rsp - 24) 64 = fr.r13 ∧ memLoad m (fr.rsp - 16) 64 = fr.r14 ∧
    memLoad m (fr.rsp - 8) 64 = fr.r15 := by
  let sp := fr.rsp - 5960
  have stack : Writable Extracted.programImage fr.original (fr.rsp - 9768) 9768 := by
    simp only [Fn10ee80.frameAt, Fn10ee80.frameAtG1, Atom.All, Atom.Holds] at atoms
    obtain ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, stack, _⟩ := atoms
    exact stack
  have sep := (Affine.readableCodeSpan (n := 120) (base := 0x202bc8)
    generatorBytes image (by decide) (by decide) stack (by decide)).2
  have finalFrame := tableCoreFrame room low (secondCopyFrame room low (firstCopyFrame room low))
  have savedFrame : RamWriteFrame fr.original (firstCopySaved fr) [fr.region] := by
    unfold firstCopySaved
    copy_frame
  have generatorLoad {m : Ram} (f : RamWriteFrame fr.original m [fr.region]) (i : Fin 15) :
      memLoad m (wordAddr 0x202bc8 64 i.val) 64 = memLoad fr.original (wordAddr 0x202bc8 64 i.val) 64 := by
    apply f.memLoad_eq
    have hi := i.isLt
    have addr : (wordAddr 0x202bc8 64 i.val).toNat = 0x202bc8 + 8 * i.val := by
      simp only [wordAddr, Nat.reduceDiv, BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat,
        Nat.mod_eq_of_lt (by omega : 8 * i.val < 2 ^ 64), Nat.mod_eq_of_lt (by omega : 0x202bc8 + 8 * i.val < 2 ^ 64)]
    have top : (fr.rsp - 9768).toNat = fr.rsp.toNat - 9768 := by
      rw [BitVec.toNat_sub_of_le (by change 9768 ≤ _; exact room)]; rfl
    change 0x202bc8 + 120 ≤ (fr.rsp - 9768).toNat ∨ (fr.rsp - 9768).toNat + 9768 ≤ 0x202bc8 at sep
    simp only [Outside, List.mem_singleton, forall_eq, Activation.region, low, addr, Nat.reduceDiv, top]
    rw [top] at sep
    omega
  have later (k : Nat) (fits : (3848 ≤ k ∧ k + 8 ≤ 4000) ∨ (5920 ≤ k ∧ k ≤ 5952)) :=
    laterCopiesLoad (m := firstCopyMemory fr) sp k fits
  have word (c i : Nat) : wordAddr (sp + BitVec.ofNat 64 c) 64 i =
      sp + BitVec.ofNat 64 (c + 8 * i) := by rw [wordAddr, BitVec.ofNat_add, BitVec.add_assoc]
  have recordWord (c i : Nat) (lo : 3848 ≤ c + 8 * i) (hi : c + 8 * i + 8 ≤ 4000) :
      memLoad (callerMemory fr) (wordAddr (sp + BitVec.ofNat 64 c) 64 i) 64 =
        memLoad (firstCopyMemory fr) (wordAddr (sp + BitVec.ofNat 64 c) 64 i) 64 := by
    rw [word]
    exact later _ (Or.inl ⟨lo, hi⟩)
  have saved (k : BitVec 64) (lo : 5920 ≤ (5960 - k).toNat) (hi : (5960 - k).toNat ≤ 5952) :
      memLoad (callerMemory fr) (fr.rsp - k) 64 = memLoad (firstCopySaved fr) (fr.rsp - k) 64 := by
    have addr : fr.rsp - k = sp + BitVec.ofNat 64 (5960 - k).toNat := by
      simp only [sp, BitVec.ofNat_toNat, BitVec.setWidth_eq]; bv_omega
    rw [addr]
    exact (later _ (Or.inr ⟨lo, hi⟩)).trans (savedLoad fr _ lo hi)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i
    have hi := i.isLt
    exact (recordWord 3848 i (by omega) (by omega)).trans ((generatorRecord fr i).trans
      ((generatorLoad savedFrame i).trans (generatorLoad finalFrame i).symm))
  · intro i hi
    exact (recordWord 3968 i (by omega) (by omega)).trans (scalarRecord words i hi)
  all_goals
    refine (saved _ (by decide) (by decide)).trans ?_
    unfold firstCopySaved
    segment_words [] <;> rfl

end K256.Proofs.Generate.Generator.Multiply.Caller
