import K256.Proofs.Common.SignatureRun
import K256.Proofs.Sec1.Affine.Finish
import K256.Proofs.Ecdh.Decode.Repr

namespace K256.Proofs.Ecdh.Decode.Affine

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine
open K256.Spec.Program K256.Proofs.Sec1.LIR K256.Proofs.Sec1.Affine

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

theorem selectedPointAt {mem : Ram} {sp dst : BitVec 64} {point : Standards.SECG.ECC.Curve.Point}
    (low : dst.toNat + 89 ≤ 2^32) (valid : memLoad mem (sp + 88) 8 = 1)
    (key : AffinePointAt mem sp point) : AffinePointAt (selectedPoint mem sp dst) dst point := by
  let limbs := storeLimbs mem dst (fun i => memLoad mem (wordAddr sp 64 i) 64) 10
  have after : selectedPoint mem sp dst = memStore (memStore limbs (dst + 80) (memLoad mem (sp + 80) 8))
      (dst + 88) (1 : BitVec 8) := by
    unfold selectedPoint
    rw [valid]
    have flag : ∀ x : BitVec 8, ((x ^^^ 1) &&& (-1)) ^^^ 1 = x := by decide +kernel
    dsimp only
    rw [flag]
    change memStore (memStore (storeLimbs mem dst _ 10) (dst + 80) (memLoad mem (sp + 80) 8)) (dst + 88) (1 : BitVec 8) = _
    have mask (w : BitVec 64) : w &&& (-(1#8).setWidth 64) = w := BitVec.and_allOnes
    exact congrArg (fun word => memStore (memStore (storeLimbs mem dst word 10) (dst + 80)
      (memLoad mem (sp + 80) 8)) (dst + 88) (1 : BitVec 8))
      (funext fun i => mask (memLoad mem (wordAddr sp 64 i) 64))
  have coord (i : Nat) (hi : i < 10) :
      memLoad (selectedPoint mem sp dst) (wordAddr dst 64 i) 64 = memLoad mem (wordAddr sp 64 i) 64 := by
    rw [after, memLoad_memStore_of_rangeApart, memLoad_memStore_of_rangeApart]
    · exact storeLimbs_read low 10 (by decide) i hi
    all_goals apply RangeApart.right_sub (m := 80) (off := 8*i) _ (by omega)
    · exact RangeApart.of_offsets (x := dst) (c := 80) (d := 0) rfl (BitVec.add_zero _).symm (by decide)
    · exact RangeApart.of_offsets (x := dst) (c := 88) (d := 0) rfl (BitVec.add_zero _).symm (by decide)
  have flagEq : memLoad (selectedPoint mem sp dst) (dst + 80) 8 = memLoad mem (sp + 80) 8 := by
    rw [after, memLoad_memStore_of_rangeApart]
    · exact memLoad_memStore_same _ _ _ (by decide) (by decide)
    · exact RangeApart.of_offsets (x := dst) (c := 88) (d := 80) rfl rfl (by decide)
  cases point with
  | infinity => exact flagEq.trans key
  | affine x y =>
    obtain ⟨a,b,ha,hb,xl,yl,wx,wy,ident,rx,ry⟩ := key
    refine ⟨a,b,ha,hb,xl,yl,?_,?_,flagEq.trans ident,rx,ry⟩
    · intro i hi
      exact (coord i (by omega)).trans (wx i hi)
    · intro i hi
      have step (base : BitVec 64) : wordAddr (base + 40) 64 i = wordAddr base 64 (5 + i) := by
        simp only [wordAddr, Nat.mul_add, BitVec.ofNat_add, BitVec.add_assoc]
        rfl
      rw [step, coord (5+i) (by omega), ← step]
      exact wy i hi

def CallerWidths (a : Vector Value 53) : Prop :=
  ∀ i : Fin Reg.count, i.val ∈ [2,8,9] → a[i].width = 64

theorem afterJump {code : CodeMap} {l l' : Label} {a b : Vector Value 53} {m n : Ram}
    {out : Output Value Ram Reg.count} (run : program.Exec (dialect code) ⟨⟨l,a,m⟩,[]⟩ out)
    (step : program.runBlock (dialect code) ⟨l,a,m⟩ = .jump ⟨l',b,n⟩) :
    program.Exec (dialect code) ⟨⟨l',b,n⟩,[]⟩ out := by
  cases run with
  | done h => simp only [Program.step, step, Transfer.next, reduceCtorEq] at h
  | next h tail =>
    simp only [Program.step, step, Transfer.next, Outcome.next.injEq] at h
    cases h
    exact tail

theorem returnState {args : Vector Value 53} {m : Ram} {out : Output Value Ram Reg.count}
    (run : program.Exec (dialect Extracted.programImage) ⟨⟨.l121599,args,m⟩,[]⟩ out) :
    out.store = m ∧ (CallerWidths args → CallerWidths out.values) := by
  cases run with
  | done h =>
    change (program.runBlock _ ⟨.l121599,args,m⟩).next _ [] = .done out at h
    cfg_eval [b_l121599] at h
    repeat' (split at h)
    all_goals simp only [Transfer.next, Outcome.done.injEq, reduceCtorEq] at h
    subst out
    refine ⟨rfl, fun widths i hi => ?_⟩
    obtain ⟨i,ilt⟩ := i
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl
    · exact widths 2 (by decide)
    · exact widths 8 (by decide)
    · exact widths 9 (by decide)
  | next h _ =>
    change (program.runBlock _ ⟨.l121599,args,m⟩).next _ [] = .next _ at h
    cfg_eval [b_l121599] at h
    repeat' (split at h)
    all_goals simp only [Transfer.next, reduceCtorEq] at h

private theorem guardJump {c : Prop} [Decidable c] {t : Transfer Value Ram Label signature Reg.count}
    {l : Location Value Ram Label signature} (h : (if c then t else .stuck) = .jump l) : t = .jump l := by
  split at h <;> first | exact h | contradiction

set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
private theorem selectedWidths {a b : Vector Value 53} {m n : Ram}
    (step : program.runBlock (dialect Extracted.programImage) ⟨.l121502,a,m⟩ = .jump ⟨.l121599,b,n⟩) :
    CallerWidths b := by
  cfg_eval [b_l121502, b_l121502_1] at step
  repeat' replace step := guardJump step
  injection step with eq
  cases eq
  rintro ⟨i,hi⟩ h
  simp only [List.mem_cons,List.not_mem_nil,or_false] at h
  rcases h with rfl | rfl | rfl <;> rfl

theorem finishPointAt {fr : Activation} {a : Vector Value 53} {m : Ram}
    (before : Atom.All Extracted.programImage a m (Fn121480.frameAt .l121599 fr))
    (dst : Writable Extracted.programImage m fr.rdi 89) {out : Output Value Ram Reg.count}
    (run : program.Exec (dialect Extracted.programImage) ⟨⟨.l121502,a,m⟩,[]⟩ out)
    (valid : memLoad m (fr.rsp-136+88) 8 = 1) {p : Standards.SECG.ECC.Curve.Point}
    (pt : AffinePointAt m (fr.rsp-136) p) : AffinePointAt out.store fr.rdi p ∧ CallerWidths out.values := by
  simp only [Fn121480.frameAt, Fn121480.frameAtG2, Atom.All, Atom.Holds] at before
  obtain ⟨rsp,_,ptr,_,_,_,_,_,_,_,_,_,_,_,_,win,_,_,_⟩ := before
  have read : Readable m (fr.rsp-136) 89 := win.readable.of_offsets (addr_sub _ _) (addr_sub _ _) (by decide)
  obtain ⟨next,step,_⟩ := selectBlock Common.fnCode_subset_programImage a m _ _
    (congrArg (Value.get 64) rsp) (congrArg (Value.get 64) ptr) read dst
  obtain ⟨store, widths⟩ := returnState (afterJump run step)
  refine ⟨?_, widths (selectedWidths step)⟩
  rw [store]
  exact selectedPointAt dst.readable.low valid pt

end K256.Proofs.Ecdh.Decode.Affine
