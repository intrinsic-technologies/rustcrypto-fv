import K256.Proofs.Verify.Core.Lincomb.Loop.State
import K256.Proofs.Verify.Core.Lincomb.Loop.Length
import K256.Proofs.Generate.Generator.Affine.Memory

namespace K256.Proofs.Verify.Core.Lincomb.Loop

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Multiply (Projective)
open Generate.Curve

structure LengthArguments (a : Registers) (m : Ram) (sp dst iterator dataPtr : BitVec 64)
    (b : Registers) (n : Ram) : Prop where
  rsp : b[4] = ⟨64, baseSp sp - 8⟩
  saved : SavedFrame a m sp dst (b.set 4 ⟨64, baseSp sp⟩) n
  rbx : b[3].width = 64
  r12 : b[12].width = 64
  front : b[13] = ⟨64, 0⟩
  nextTable : b[14] = ⟨64, dataPtr⟩
  tableEnd : b[5] = ⟨64, dataPtr + 0x1340⟩
  iter : b[15] = ⟨64, iterator⟩
  back : memLoad n (baseSp sp) 64 = 0
  tag : memLoad n (baseSp sp - 8) 64 = 0x1101de
  di : b[7].get 64 = baseSp sp + 0x58
  si : b[6].get 64 = memLoad n (dataPtr + 0x780) 64
  first : memLoad n (baseSp sp + 0x58) 64 = dataPtr + 0x9a0
  last : memLoad n (baseSp sp + 0x60) 64 = dataPtr + 0x1340
  table : memLoad n (baseSp sp + 0x68) 64 = dataPtr
  digits : memLoad n (baseSp sp + 0x78) 64 = dataPtr + 0x780
  index : memLoad n (baseSp sp + 0x88) 64 = 1
  limit : memLoad n (baseSp sp + 0x90) 64 = 2
  unset : memLoad n (baseSp sp + 0x98) 64 = 0

private theorem lengthJump {l r : Label} {a b : Registers} {m n : Ram}
    (run : program.runBlock (dialect Extracted.programImage) ⟨l, a, m⟩ = .jump ⟨r, b, n⟩) :
    Reaches l a m r b n := by
  apply Semantics.Reaches.single
  change (program.runBlock _ _).next _ [] = _
  rw [run]
  rfl

private theorem lengthWordApart (m : Ram) (base rd wr : BitVec 64) (word : BitVec 64)
    (apart : 8 ≤ (rd - wr).toNat ∧ 8 ≤ (wr - rd).toNat) :
    memLoad (memStore m (base + wr) word) (base + rd) 64 = memLoad m (base + rd) 64 :=
  memLoad_memStore_of_rangeApart _ _ _ _ _ (RangeApart.of_offsets rfl rfl apart)

theorem lengthArguments {a b : Registers} {m n : Ram} {sp dst iterator dataPtr : BitVec 64}
    (entry : RoutineEntry a m sp 0x478) (s : SavedFrame a m sp dst b n)
    (front : b[13] = ⟨64, 0⟩) (nextTable : b[14] = ⟨64, dataPtr⟩)
    (tableEnd : b[5] = ⟨64, dataPtr + 0x1340⟩) (iter : b[15] = ⟨64, iterator⟩)
    (rbx : b[3].width = 64) (r12 : b[12].width = 64)
    (back : memLoad n (baseSp sp) 64 = 0)
    (last : memLoad n (baseSp sp + 0x60) 64 = dataPtr + 0x1340)
    (unset : memLoad n (baseSp sp + 0x98) 64 = 0)
    (nonzero : dataPtr ≠ 0)
    (tableRead : Readable m dataPtr 0x1340)
    (dataApart : Outside [scratch sp 0x478, ⟨dst.toNat, 120⟩] dataPtr 0x1340) :
    ∃ c t d u, Reaches .l110156 b n .l1101c9 c t ∧
      program.runBlock (dialect Extracted.programImage) ⟨.l1101c9, c, t⟩ =
        .call ⟨.l11c0b0, d, u⟩ (Recode.returnTo .l1101de 0x1101de) ∧
      LengthArguments a m sp dst iterator dataPtr d u := by
  let base := baseSp sp
  let first := dataPtr + 0x9a0
  let digits := dataPtr + 0x780
  let n₁ := memStore n (base + 0x70) digits
  let n₂ := memStore n₁ (base + 0x78) digits
  let n₃ := memStore n₂ (base + 0x80) first
  let n₄ := memStore n₃ (base + 0x90) (2 : BitVec 64)
  let n₅ := memStore n₄ (base + 0x68) dataPtr
  let n₆ := memStore n₅ (base + 0x58) first
  let t := memStore n₆ (base + 0x88) (1 : BitVec 64)
  let u := memStore t (base - 8) (0x1101de : BitVec 64)
  have savedRsp : b[4].get 64 = base := congrArg (Value.get 64) s.rsp
  have nextWord : b[14].get 64 = dataPtr := congrArg (Value.get 64) nextTable
  have endWord : b[5].get 64 = dataPtr + 0x1340 := by rw [tableEnd, Value.get_mk]
  have nextNeEnd : dataPtr ≠ dataPtr + 0x1340 := by bv_omega
  have stackAddr (off : BitVec 64) : base + off = sp - (0x1d8 - off) := by
    dsimp only [base, baseSp]
    bv_omega
  have within (off : BitVec 64) (lower : (0x1d8 - off).toNat ≤ 0x478)
      (upper : 8 ≤ (0x1d8 - off).toNat) : InRegions [scratch sp 0x478] (base + off) 8 := by
    rw [stackAddr]
    exact ⟨_, .head _, Recode.inScratch entry.room lower upper⟩
  have tFrame : RamWriteFrame m t [scratch sp 0x478] := by
    dsimp only [t, n₆, n₅, n₄, n₃, n₂, n₁]
    repeat' refine RamWriteFrame.memStore ?_ _ (within _ (by decide) (by decide))
    exact s.frame
  have pushAddr : base - 8 = base + (-(8 : BitVec 64)) := by bv_omega
  have uFrame : RamWriteFrame m u [scratch sp 0x478] := by
    dsimp only [u]
    rw [pushAddr]
    exact tFrame.memStore _ (within _ (by decide) (by decide))
  have stack : Writable Extracted.programImage n base 0x1d8 :=
    (Recode.stackSlot entry (by decide) (by decide)).of_frame s.frame
  have push : StoreOk Extracted.programImage t (base - 8) 8 0x1101d9 5 := by
    rw [pushAddr, stackAddr]
    exact Recode.storeGuard (off := 0x10) (len := 5)
      ((Recode.stackSlot entry (by decide) (by decide)).of_frame tFrame) code_l1101c9 (by decide)
  have dataOffset : digits.toNat = dataPtr.toNat + 0x780 := by
    have := tableRead.low
    change (dataPtr + (0x780 : BitVec 64)).toNat = _
    simp only [BitVec.toNat_add, BitVec.reduceToNat]
    rw [Nat.mod_eq_of_lt (by omega)]
  have readDigits : LoadOk t digits 8 := by
    apply LoadOk.of_region (tableRead.of_frame tFrame) <;> rw [dataOffset] <;> omega
  have outsideDigits : Outside [scratch sp 0x478] digits 8 :=
    Generate.Generator.Affine.outside_subregion
      ⟨dataApart.1, fun r hr => by
        obtain rfl := List.mem_singleton.mp hr
        exact dataApart.2 _ (.head _)⟩
      (by rw [dataOffset]; omega) (by rw [dataOffset]; omega)
  have sameDigits : memLoad t digits 64 = memLoad u digits 64 :=
    (tFrame.memLoad_eq outsideDigits).trans (uFrame.memLoad_eq outsideDigits).symm
  have keepSaved (off : BitVec 64) (lower : 8 ≤ off.toNat) (upper : off.toNat ≤ 48) :
      memLoad u (sp - off) 64 = memLoad n (sp - off) 64 := by
    have address : sp - off = base + (0x1d8 - off) := by
      rw [stackAddr, show 0x1d8 - (0x1d8 - off) = off by bv_omega]
    rw [address]
    dsimp only [u, t, n₆, n₅, n₄, n₃, n₂, n₁]
    rw [pushAddr]
    simp (disch := bv_omega) only [lengthWordApart]
  refine ⟨?_, t, ?_, u, ?route, ?call, ?post⟩
  case route =>
    refine (lengthJump (r := .l11015f) (n := n) (b := ?_) ?edge).trans ?_
    case edge =>
      cfg_eval [nextWord, BitVec.and_self, testFlags, beq_eq_false_iff_ne.mpr nonzero]
      rfl
    refine (lengthJump (r := .l110168) (n := n) (b := ?_) ?edge).trans ?_
    case edge =>
      cfg_eval [nextWord, endWord, cmpSpec_ZF, beq_eq_false_iff_ne.mpr nextNeEnd]
      rfl
    refine (lengthJump (r := .l110193) (n := n) (b := ?_) ?edge).trans ?_
    case edge =>
      cfg_eval [nextWord, BitVec.xor_self]
      rfl
    apply lengthJump
    cfg_eval [savedRsp]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l110193)
    rfl
  case call =>
    cfg_eval [savedRsp, BitVec.reduceMul, BitVec.add_zero]
    dsimp only [t, digits] at readDigits
    dsimp only [t] at push
    simp only [readDigits, push, ↓reduceIte] <;> rfl
  case post =>
    change memLoad n (base + 0x60) 64 = _ at last
    change memLoad n (base + 0x98) 64 = _ at unset
    refine ⟨rfl, ?_, rbx, r12, front, nextTable, tableEnd, iter, ?_, ?_, rfl, sameDigits,
      ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · refine ⟨rfl, ?_, (keepSaved 48 (by decide) (by decide)).trans s.rbx,
        (keepSaved 40 (by decide) (by decide)).trans s.r12,
        (keepSaved 32 (by decide) (by decide)).trans s.r13,
        (keepSaved 24 (by decide) (by decide)).trans s.r14,
        (keepSaved 16 (by decide) (by decide)).trans s.r15,
        (keepSaved 8 (by decide) (by decide)).trans s.rbp, ?_, uFrame⟩
      · change memLoad u (base + 0xd0) 64 = dst
        dsimp only [u, t, n₆, n₅, n₄, n₃, n₂, n₁]
        rw [pushAddr]
        simp (disch := decide) only [lengthWordApart]
        exact s.dest
      · rintro ⟨i, hi⟩ h
        have saved := s.control ⟨i, hi⟩ h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl | rfl <;> exact saved
    · rw [show baseSp sp = base + 0 from (BitVec.add_zero base).symm]
      dsimp only [u, t, n₆, n₅, n₄, n₃, n₂, n₁]
      rw [pushAddr]
      simp (disch := decide) only [lengthWordApart]
      exact (congrArg (fun ptr => memLoad n ptr 64) (addr_self base).symm).trans back
    · exact memLoad_memStore_same t (base - 8) (0x1101de : BitVec 64) (by decide) (by decide)
    all_goals
      change memLoad u (base + _) 64 = _
      dsimp only [u, t, n₆, n₅, n₄, n₃, n₂, n₁]
      rw [pushAddr]
      simp (disch := decide) only [lengthWordApart, memLoad_memStore_same, last, unset] <;> rfl

end K256.Proofs.Verify.Core.Lincomb.Loop
