import K256.Proofs.Sec1.SqrtCounted.Types
import K256.Proofs.ParseSignature.Memory
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Store2

set_option autoImplicit false

namespace K256.Proofs.Sec1.SqrtCounted

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open CFG Lift Refine LIR Common.Field

private def resumeBytes : Sqrt.SquareLoop → List UInt8
  | .first44 => bytes_l11804b
  | .middle88 => bytes_l1184db
  | .last44 => bytes_l11895b

private theorem resumeCode (site : Sqrt.SquareLoop) :
    ∀ x ∈ codeRange (address site.resume) (resumeBytes site), x ∈ fnCode := by
  cases site
  · exact code_l11804b
  · exact code_l1184db
  · exact code_l11895b

private theorem stackWord {code : CodeMap} {m : Ram} {base offset : BitVec 64}
    (stack : Writable code m (base - 112) 192) (inside : (offset + 112).toNat + 8 ≤ 192) :
    Writable code m (base + offset) 8 := by
  have he : offset - (0 - 112) = offset + 112 := by bv_omega
  exact stack.of_offsets (x := base) rfl (addr_sub base 112) (he ▸ inside)

private theorem storeWord {code : CodeMap} {base offset : BitVec 64} {m t : Ram}
    (stack : Writable code m (base - 112) 192) (inside : (offset + 112).toNat + 8 ≤ 192)
    (frame : RamWriteFrame m t [Sqrt.roundStack base]) (v : BitVec 64) :
    RamWriteFrame m (memStore t (base + offset) v) [Sqrt.roundStack base] := by
  have he : offset - (0 - 112) = offset + 112 := by bv_omega
  have hlow := stack.readable.low
  have haddr := toNat_of_offsets (a := base + offset) (c := offset) rfl (addr_sub base 112)
    hlow (he ▸ inside)
  refine frame.memStore v ⟨_, List.mem_cons_self .., ?_⟩
  change (base - 112).toNat ≤ (base + offset).toNat ∧
    (base + offset).toNat + 8 ≤ (base - 112).toNat + 192 ∧
    (base + offset).toNat + 8 ≤ 2 ^ 64
  rw [haddr, he]
  omega

private theorem storeGuard {code : CodeMap} {base offset : BitVec 64} {m t : Ram}
    {off len : Nat} (site : Sqrt.SquareLoop)
    (hcode : ∀ x ∈ fnCode, x ∈ code)
    (stack : Writable code m (base - 112) 192) (inside : (offset + 112).toNat + 8 ≤ 192)
    (frame : RamWriteFrame m t [Sqrt.roundStack base]) (instr : off + len ≤ 54) :
    StoreOk code t (base + offset) 8 (address site.resume + BitVec.ofNat 64 off) len := by
  apply ParseSignature.storeOk_of_codeRange (stackWord (stack.of_frame frame) inside)
    (fun x hx => hcode x (resumeCode site x hx))
  cases site <;> exact instr

private theorem loadGuard {code : CodeMap} {base offset : BitVec 64} {m t : Ram}
    (stack : Writable code m (base - 112) 192) (inside : (offset + 112).toNat + 8 ≤ 192)
    (frame : RamWriteFrame m t [Sqrt.roundStack base]) :
    LoadOk t (base + offset) 8 :=
  let read := (stackWord (stack.of_frame frame) inside).readable
  ⟨read.low, read.present⟩

private theorem sourceWord {mem : Ram} {base : BitVec 64} {limbs : Limbs}
    (source : WordsAt mem (base + 40) 64 limbs) (i : Nat) (hi : i < 5) :
    memLoad mem (base + BitVec.ofNat 64 (40 + 8 * i)) 64 = limbs[i] := by
  have h := source i hi
  change memLoad mem (base + BitVec.ofNat 64 40 + BitVec.ofNat 64 (8 * i)) 64 = _ at h
  rwa [BitVec.add_assoc, ← BitVec.ofNat_add] at h

set_option maxHeartbeats 1500000 in
theorem copyBlock (site : Sqrt.SquareLoop) {code : CodeMap} {base w : BitVec 64}
    {args : Vector Value Reg.count} {mem : Ram} {limbs : Limbs}
    (hcode : ∀ x ∈ fnCode, x ∈ code)
    (rsp : args[4].get 64 = base)
    (stack : Writable code mem (base - 112) 192)
    (counter : args[site.countReg].get 64 = w)
    (source : WordsAt mem (base + 40) 64 limbs) :
    ∃ (next : Vector Value Reg.count) (m' : Ram),
      program.runBlock (dialect code) ⟨site.resume, args, mem⟩ =
        .jump ⟨if w - 1 = 0 then site.exit else site.head, next, m'⟩ ∧
      next[4] = args[4] ∧ next[site.countReg] = ⟨64, w - 1⟩ ∧
      (∀ r : Fin Reg.count, r.val ∈ [3, 5, 12, 13, 14, 15, 22, 39, 50, 51] →
        r ≠ site.countReg → next[r] = args[r]) ∧
      WordsAt m' base 64 limbs ∧ WordsAt m' (base + 40) 64 limbs ∧
      (∀ r : Fin Reg.count, r.val ∈ [1, 2, 8, 9] → args[r].width = 64 → next[r].width = 64) ∧
      RamWriteFrame mem m' [Sqrt.roundStack base] := by
  let m4 := memStore mem (base + 32) limbs[4]
  let m3 := memStore m4 (base + 24) limbs[3]
  let m2 := memStore m3 (base + 16) limbs[2]
  let m1 := memStore m2 (base + 8) limbs[1]
  let m0 := memStore m1 (base + 0) limbs[0]
  have m0eq : m0 = memStore m1 base limbs[0] :=
    congrArg (fun a => memStore m1 a limbs[0]) (BitVec.add_zero base)
  have f := RamWriteFrame.refl mem [Sqrt.roundStack base]
  have f4 : RamWriteFrame mem m4 [Sqrt.roundStack base] :=
    storeWord stack (by decide : ((32 : BitVec 64) + 112).toNat + 8 ≤ 192) f limbs[4]
  have f3 : RamWriteFrame mem m3 [Sqrt.roundStack base] :=
    storeWord stack (by decide : ((24 : BitVec 64) + 112).toNat + 8 ≤ 192) f4 limbs[3]
  have f2 : RamWriteFrame mem m2 [Sqrt.roundStack base] :=
    storeWord stack (by decide : ((16 : BitVec 64) + 112).toNat + 8 ≤ 192) f3 limbs[2]
  have f1 : RamWriteFrame mem m1 [Sqrt.roundStack base] :=
    storeWord stack (by decide : ((8 : BitVec 64) + 112).toNat + 8 ≤ 192) f2 limbs[1]
  have f0 : RamWriteFrame mem m0 [Sqrt.roundStack base] :=
    storeWord stack (by decide : ((0 : BitVec 64) + 112).toNat + 8 ≤ 192) f1 limbs[0]
  have apart (off : BitVec 64) (h : 8 ≤ (40 - off).toNat ∧ 40 ≤ (off - 40).toNat) :
      RangeApart (base + off) 8 (base + 40) 40 :=
    Refine.RangeApart.of_offsets (x := base) rfl rfl h
  have s4 : WordsAt m4 (base + 40) 64 limbs :=
    source.write_apart _ _ (apart 32 (by decide))
  have s3 : WordsAt m3 (base + 40) 64 limbs :=
    s4.write_apart _ _ (apart 24 (by decide))
  have s2 : WordsAt m2 (base + 40) 64 limbs :=
    s3.write_apart _ _ (apart 16 (by decide))
  have s1 : WordsAt m1 (base + 40) 64 limbs :=
    s2.write_apart _ _ (apart 8 (by decide))
  have s0 : WordsAt m0 (base + 40) 64 limbs :=
    s1.write_apart _ _ (apart 0 (by decide))
  have hlow := stack.readable.low
  have addr := toNat_of_offsets (c := (0 : BitVec 64)) (n := 40)
    (addr_self base) (addr_sub base 112) hlow (by decide)
  have dstLow : base.toNat + 64 / 8 * 5 ≤ 2 ^ 64 := by
    change base.toNat = (base - 112).toNat + 112 at addr
    omega
  let before := Vector.ofFn fun i : Fin 5 => memLoad mem (wordAddr base 64 i.val) 64
  have d : WordsAt mem base 64 before := by
    intro i hi
    simp only [before, Vector.getElem_ofFn]
  have d4 := d.write_set (j := 4) (by decide) limbs[4] (by decide) (by decide) (by decide) dstLow
  have d3 := d4.write_set (j := 3) (by decide) limbs[3] (by decide) (by decide) (by decide) dstLow
  have d2 := d3.write_set (j := 2) (by decide) limbs[2] (by decide) (by decide) (by decide) dstLow
  have d1 := d2.write_set (j := 1) (by decide) limbs[1] (by decide) (by decide) (by decide) dstLow
  have d0 := d1.write_set (j := 0) (by decide) limbs[0] (by decide) (by decide) (by decide) dstLow
  have dst : WordsAt m0 base 64 limbs := by
    intro i hi
    have written := d0 i hi
    change memLoad m0 (wordAddr base 64 i) 64 = _ at written
    rw [written]
    obtain rfl | rfl | rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    all_goals rfl
  have r4 : LoadOk mem (base + 72) 8 := loadGuard stack (by decide) f
  have r3 : LoadOk m4 (base + 64) 8 := loadGuard stack (by decide) f4
  have r2 : LoadOk m3 (base + 56) 8 := loadGuard stack (by decide) f3
  have r0 : LoadOk m2 (base + 40) 8 := loadGuard stack (by decide) f2
  have r1 : LoadOk m2 (base + 48) 8 := loadGuard stack (by decide) f2
  have v4 : memLoad mem (base + 72) 64 = limbs[4] := sourceWord source 4 (by decide)
  have v3 : memLoad m4 (base + 64) 64 = limbs[3] := sourceWord s4 3 (by decide)
  have v2 : memLoad m3 (base + 56) 64 = limbs[2] := sourceWord s3 2 (by decide)
  have v0 : memLoad m2 (base + 40) 64 = limbs[0] := sourceWord s2 0 (by decide)
  have v1 : memLoad m2 (base + 48) 64 = limbs[1] := sourceWord s2 1 (by decide)
  have g4 := storeGuard (offset := 32) (off := 5) (len := 5) site hcode stack (by decide) f (by decide)
  have g3 := storeGuard (offset := 24) (off := 15) (len := 5) site hcode stack (by decide) f4 (by decide)
  have g2 := storeGuard (offset := 16) (off := 25) (len := 5) site hcode stack (by decide) f3 (by decide)
  have g1 := storeGuard (offset := 8) (off := 40) (len := 5) site hcode stack (by decide) f2 (by decide)
  have g0 := storeGuard (offset := 0) (off := 45) (len := 4) site hcode stack (by decide) f1 (by decide)
  dsimp only [m4, m3, m2, m1] at r3 r2 r1 r0 v3 v2 v1 v0 g3 g2 g1 g0
  cases site
  all_goals
    simp only [Sqrt.SquareLoop.resume, address, Label.G1.address, BitVec.reduceAdd] at g4 g3 g2 g1 g0
    simp only [← BitVec.ofNat_eq_ofNat] at g4 g3 g2 g1 g0
    rw [show base + (0 : BitVec 64) = base from BitVec.add_zero base] at g0
    simp only [Sqrt.SquareLoop.head, Sqrt.SquareLoop.resume, Sqrt.SquareLoop.exit,
      Sqrt.SquareLoop.countReg] at counter ⊢
    first | change args[3].get 64 = w at counter | change args[15].get 64 = w at counter
    refine ⟨?_, m0, ?_, ?_⟩
    rotate_left
    · cfg_eval
      simp only [rsp, counter, r4, r3, r2, r0, r1, v4, v3, v2, v0, v1, g4, g3, g2, g1, g0, ite_true,
        Bool.not_eq_true', beq_eq_false_iff_ne, ite_not, m0eq, m1, m2, m3, m4]
      split <;> rename_i h
      · rw [ite_eq_left h]
      · rw [ite_eq_right h]
    · refine ⟨rfl, rfl, ?_, dst, s0, ?_, f0⟩
      · intro ⟨r, _⟩ hr hne
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals first | rfl | exact False.elim (hne rfl)
      · intro ⟨r, _⟩ hr hw
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl <;> first | rfl | exact hw

end K256.Proofs.Sec1.SqrtCounted
