import K256.Proofs.Common.Tactic
import K256.Proofs.Ecdh.Decode.Convert.Resume
import K256.Proofs.Sec1.Affine.Output

namespace K256.Proofs.Ecdh.Decode.Convert

open Prelude X86.Machine X86.UserProcess X86Proofs K256.Spec.Program K256.Proofs.CFG
open K256.Proofs.Refine K256.Proofs.Lift Ecdh.LIR
open Sec1.Affine (storeLimbs)

private theorem wordAddrNat {base : BitVec 64} {i : Nat}
    (low : base.toNat + 8 * i + 8 ≤ 2 ^ 32) :
    (wordAddr base 64 i).toNat = base.toNat + 8 * i := by
  simp only [wordAddr, Nat.reduceDiv, BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := 8*i) (by omega), Nat.mod_eq_of_lt (by omega)]

private theorem storedWords {m : Ram} {base : BitVec 64} (words : Nat → BitVec 64)
    (low : base.toNat + 120 ≤ 2 ^ 32) (n : Nat) (bound : n ≤ 15) :
    RamWriteFrame m (storeLimbs m base words n) [⟨base.toNat,120⟩] ∧
      ∀ i < n, memLoad (storeLimbs m base words n) (wordAddr base 64 i) 64 = words i := by
  induction n with
  | zero => exact ⟨RamWriteFrame.refl _ _, fun i h => by omega⟩
  | succ n ih =>
    obtain ⟨frame, read⟩ := ih (by omega)
    have addr (i : Nat) (hi : i < 15) := wordAddrNat (base := base) (i := i) (by omega)
    rw [storeLimbs]
    refine ⟨frame.memStore _ ⟨_, List.mem_singleton_self _, ?_⟩, ?_⟩
    · simp only [InRegion, Nat.reduceDiv, addr n (by omega)]
      omega
    · intro i hi
      by_cases eq : i = n
      · subst i
        exact memLoad_memStore_same _ _ _ (by decide) (by decide)
      · rw [memLoad_memStore_of_rangeApart]
        · exact read i (by omega)
        · apply RangeApart.of_toNat <;> simp only [addr n (by omega), addr i (by omega)] <;> omega

set_option maxHeartbeats 650000 in
set_option maxRecDepth 4096 in
theorem convertReturn (fr : Activation) (a : Values Value Reg.count) (m : Ram)
    (atoms : Atom.All Extracted.programImage a m (Fn10fa10.frameAt .l10fa68 fr))
    (coords : coordinates fr a m) (flag : a[0].get 8 = inputFlag fr)
    (bit : inputFlag fr = 0 ∨ inputFlag fr = 1) (w : ParseSignature.ArgumentWidths a)
    (dst : Writable Extracted.programImage m fr.rdi 120)
    (sep : Outside [ParseSignature.callStack fr] fr.rdi 120) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l10fa68,a,m⟩,[]⟩ out ∧
      out.tag = some ⟨64,fr.ret⟩ ∧ Atom.All Extracted.programImage out.values out.store (Fn10fa10.doneAt fr) ∧
      RamWriteFrame m out.store [⟨fr.rdi.toNat,120⟩] ∧ ParseSignature.ArgumentWidths out.values ∧
      ∀ i < 15, memLoad out.store (wordAddr fr.rdi 64 i) 64 = outputWord fr i := by
  simp only [Fn10fa10.frameAt, Fn10fa10.frameAtG1, Atom.All, Atom.Holds] at atoms
  obtain ⟨sp, df, bx, mx, ft, fc, s3, s12, s13, s14, s15, s5, hr, hret, retLow, win, room, _, _⟩ := atoms
  obtain ⟨r13,r5,r14,r15,r12,ys⟩ := coords
  have spBits : a[4].get 64 = fr.rsp - 88 := congrArg (Value.get 64) sp
  have dstBits : a[3].get 64 = fr.rdi := congrArg (Value.get 64) bx
  have al : (a[0].get 64).setWidth 8 = inputFlag fr :=
    (BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64)).trans flag
  let finalMem := storeLimbs m fr.rdi (outputWord fr) 15
  obtain ⟨finalFrame, finalWords⟩ := storedWords (m := m) (base := fr.rdi) (outputWord fr) dst.readable.low 15 (by decide)
  have stackSlot (off : BitVec 64) (small : off.toNat ≤ 48) :
      memLoad finalMem (fr.rsp - off) 64 = memLoad m (fr.rsp - off) 64 := by
    apply finalFrame.memLoad_eq
    have ha : (fr.rsp - off).toNat = fr.rsp.toNat - off.toNat :=
      BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega)
    have retRoom := hr.low
    have apart := sep.2 _ (List.mem_singleton_self _)
    change fr.rdi.toNat + 120 ≤ fr.low.toNat ∨
      fr.low.toNat + (fr.rsp.toNat + 8 - fr.low.toNat) ≤ fr.rdi.toNat at apart
    refine ⟨by rw [ha]; omega, ?_⟩
    intro r hm
    obtain rfl := List.mem_singleton.mp hm
    change _ ≤ fr.rdi.toNat ∨ fr.rdi.toNat + 120 ≤ _
    rw [ha]
    change fr.rsp.toNat - off.toNat + 8 ≤ _ ∨ _
    omega
  have finalRet : memLoad finalMem fr.rsp 64 = fr.ret := by
    have keep := stackSlot 0 (by decide)
    rw [show fr.rsp - 0 = fr.rsp by bv_omega] at keep
    exact keep.trans hret
  have firstY : memLoad m (fr.rsp - 88) 64 = inputWord fr 5 := by
    simpa only [wordAddr, Nat.reduceDiv, Nat.mul_zero, BitVec.add_zero] using ys 0 (by decide)
  have y1 : memLoad m (fr.rsp - 88 + 8) 64 = inputWord fr 6 := ys 1 (by decide)
  have y2 : memLoad m (fr.rsp - 88 + 16) 64 = inputWord fr 7 := ys 2 (by decide)
  have y3 : memLoad m (fr.rsp - 88 + 24) 64 = inputWord fr 8 := ys 3 (by decide)
  have y4 : memLoad m (fr.rsp - 88 + 32) 64 = inputWord fr 9 := ys 4 (by decide)
  have masked (i : Nat) (hi : i < 10) (hne : i ≠ 5) :
      inputWord fr i &&& ((inputFlag fr).setWidth 64 - 1) = outputWord fr i := by
    rcases bit with f | f
    · rw [f, show (0 : BitVec 8).setWidth 64 - 1 = BitVec.allOnes 64 from rfl, BitVec.and_allOnes]
      simp only [outputWord, f, hi, BitVec.reduceEq, ite_false, ite_true]
    · rw [f, show (1 : BitVec 8).setWidth 64 - 1 = 0#64 from rfl, BitVec.and_zero]
      simp only [outputWord, f, hne, ite_true, ite_false, BitVec.ofNat_eq_ofNat]
  have identityY :
      ((inputWord fr 5 ^^^ 1) &&& -(inputFlag fr).setWidth 64) ^^^ inputWord fr 5 =
        outputWord fr 5 := by
    have cancel (x : BitVec 64) : (x ^^^ 1) ^^^ x = 1 := by
      rw [BitVec.xor_comm x 1, BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]
    rcases bit with f | f
    · rw [f, show -(0 : BitVec 8).setWidth 64 = 0#64 from rfl, BitVec.and_zero, BitVec.zero_xor]
      rw [outputWord, f]
      rfl
    · rw [f, show -(1 : BitVec 8).setWidth 64 = BitVec.allOnes 64 from rfl, BitVec.and_allOnes, cancel]
      rw [outputWord, f]
      rfl
  have z :
      ((~~~ (-(inputFlag fr).setWidth 64).setWidth 32) &&& 1).setWidth 64 = outputWord fr 10 := by
    rcases bit with f | f <;> rw [outputWord, f] <;> rfl
  have pad (i : Nat) (h : 10 < i) : outputWord fr i = 0 := by
    unfold outputWord
    split
    · rw [ite_eq_right (by omega)]
    · rw [ite_eq_right (by omega), ite_eq_right (by omega)]
  have goodRet : LoadOk finalMem fr.rsp 8 ∧ (memLoad finalMem fr.rsp 64).toNat < 2^32 :=
    ⟨⟨hr.low, (hr.of_frame finalFrame).present⟩, finalRet ▸ retLow⟩
  have incl := fun x hx => Common.fnCode_subset_programImage x (code_l10fa68 x hx)
  simp only [finalMem, storeLimbs, wordAddr, Nat.reduceDiv, Nat.reduceMul, BitVec.add_zero,
    pad 11 (by decide), pad 12 (by decide), pad 13 (by decide), pad 14 (by decide)]
    at stackSlot finalRet goodRet finalFrame finalWords
  refine ⟨?out, Program.Exec.done ?run, ?tag, ?done_, ?frame_, ?width, ?words⟩
  case run =>
    simp only [Program.step]
    cfg_eval [b_l10fa68,b_l10fa68_1,b_l10fa68_2]
    simp only [spBits, dstBits, al, r13, r5, r14, r15, r12,
      Value.get_mk_setWidth, BitVec.setWidth_eq, firstY]
    simp only [y1, y2, y3, y4,
      BitVec.and_comm ((inputFlag fr).setWidth 64 - 1) (inputWord fr 9),
      masked 0 (by decide) (by decide), masked 1 (by decide) (by decide),
      masked 2 (by decide) (by decide), masked 3 (by decide) (by decide),
      masked 4 (by decide) (by decide), masked 6 (by decide) (by decide),
      masked 7 (by decide) (by decide), masked 8 (by decide) (by decide),
      masked 9 (by decide) (by decide), identityY, z,
      show fr.rsp - 88 + 40 = fr.rsp - 48 by bv_omega,
      show fr.rsp - 88 + 48 = fr.rsp - 40 by bv_omega,
      show fr.rsp - 88 + 56 = fr.rsp - 32 by bv_omega,
      show fr.rsp - 88 + 64 = fr.rsp - 24 by bv_omega,
      show fr.rsp - 88 + 72 = fr.rsp - 16 by bv_omega,
      show fr.rsp - 88 + 80 = fr.rsp - 8 by bv_omega,
      show fr.rsp - 88 + 88 = fr.rsp by bv_omega,
      show fr.rsp - 88 + 96 = fr.rsp + 8 by bv_omega]
    iterate 27
      refine Eq.trans (congrArg (fun t => Transfer.next (dialect Extracted.programImage) [] t)
        (ite_eq_left ?_)) ?_
      first | exact goodRet | slot_guard using incl
    rfl
  case tag => exact congrArg (fun bits => some (⟨64, bits⟩ : Value)) finalRet
  case done_ =>
    let gpr := fun bits : BitVec 64 => (⟨64, bits⟩ : Value)
    exact ⟨rfl, df, congrArg gpr ((stackSlot 48 (by decide)).trans s3),
      congrArg gpr ((stackSlot 8 (by decide)).trans s5),
      congrArg gpr ((stackSlot 40 (by decide)).trans s12),
      congrArg gpr ((stackSlot 32 (by decide)).trans s13),
      congrArg gpr ((stackSlot 24 (by decide)).trans s14),
      congrArg gpr ((stackSlot 16 (by decide)).trans s15), mx, ft, fc, trivial⟩
  case frame_ =>
    exact finalFrame
  case width =>
    intro ⟨i, hi⟩ ha
    have keep := w ⟨i, hi⟩ ha
    simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl | rfl | rfl | rfl <;> first | rfl | exact keep
  case words =>
    exact finalWords

end K256.Proofs.Ecdh.Decode.Convert
