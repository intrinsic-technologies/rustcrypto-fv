import K256.Proofs.Signing.UpdateV.Finalize.Padding.Copy
import K256.Proofs.Verify.LIR.Fn107a50
import K256.Proofs.Verify.Hash.Mark.Copy

namespace K256.Proofs.Signing.UpdateV.Finalize.Mark

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

abbrev marked (mem : Ram) (sp : BitVec 64) (n : Nat) :=
  memStore mem (sp+8+BitVec.ofNat 64 n) (128 : BitVec 8)

def ret (outer : Bool) : BitVec 64 := if outer then 0x107dec else 0x107b27

def branchLabel (outer : Bool) : Label := if outer then .l107dec else .l107b27

def resume (outer : Bool) : StackFrame Value Label signature Reg.count :=
  { target := branchLabel outer, kept := #v[], arity := rfl, guard := some ⟨64, ret outer⟩ }

theorem call (outer : Bool) {a : Registers} {m : Ram} {sp src : BitVec 64} (n : Nat)
    (rsp : a[4].get 64 = sp) (df : a[22].get 1 = 0)
    (source : if outer then src = sp + 208 else a[15].get 64 + 64 = src)
    (clear : outer = false → StoreOk Extracted.programImage m (sp+271) 1 0x107adb 8)
    (copy : RepMovsOk Extracted.programImage (copyInput outer m sp) 0 src (sp+8) 13 8
      (if outer then 0x107db9 else 0x107af4) 3)
    (used : LoadOk (copyMemory outer m sp src) (sp+71) 1)
    (count : LoadOk (copyMemory outer m sp src) (sp+104) 8)
    (usedVal : memLoad (copyMemory outer m sp src) (sp+71) 8 = BitVec.ofNat 8 (n%64))
    (countVal : memLoad (copyMemory outer m sp src) (sp+104) 64 = BitVec.ofNat 64 (n/64))
    (mark : StoreOk Extracted.programImage (copyMemory outer m sp src) (sp+8+BitVec.ofNat 64 (n%64))
      1 (if outer then 0x107dd3 else 0x107b0e) 6)
    (push : StoreOk Extracted.programImage (marked (copyMemory outer m sp src) sp (n%64))
      (sp-8) 8 (if outer then 0x107de6 else 0x107b21) 6)
    (got : LoadOk (marked (copyMemory outer m sp src) sp (n%64)) 0x203e10 8)
    (target : memLoad (marked (copyMemory outer m sp src) sp (n%64)) 0x203e10 64 = 0x12a700)
    (widths : ∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15] → a[i].width = 64) :
    ∃ b : Registers, program.runBlock (dialect Extracted.programImage) ⟨padStart outer, a, m⟩ =
        .call ⟨.l12a700,b,memStore (marked (copyMemory outer m sp src) sp (n%64)) (sp-8) (ret outer)⟩
          (resume outer) ∧
      b[4] = ⟨64,sp-8⟩ ∧ b[2] = ⟨64,BitVec.ofNat 64 (63-n%64)⟩ ∧ b[6] = ⟨64,0⟩ ∧
      b[7] = ⟨64,sp+9+BitVec.ofNat 64 (n%64)⟩ ∧
      b[(if outer then 15 else 12 : Fin Reg.count)] = ⟨64,BitVec.ofNat 64 (63-n%64)⟩ ∧
      b[(if outer then 14 else 15 : Fin Reg.count)] = ⟨64,sp+72⟩ ∧
      b[(if outer then 12 else 13 : Fin Reg.count)] = ⟨64,BitVec.ofNat 64 (n%64)⟩ ∧
      b[(if outer then 13 else 5 : Fin Reg.count)] = ⟨64,BitVec.ofNat 64 (n/64)⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ savedRegs → b[i] = a[i]) ∧
      (∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15] → b[i].width = 64) := by
  have bound := Nat.mod_lt n (by decide : 0 < 64)
  have zext : (BitVec.ofNat 8 (n % 64)).setWidth 64 = BitVec.ofNat 64 (n % 64) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  have addr (k : BitVec 64) : sp + BitVec.ofNat 64 (n % 64) + k =
      sp + k + BitVec.ofNat 64 (n % 64) := by bv_omega
  have remaining := congrArg (Value.mk 64) (Verify.Hash.Mark.remaining_xor _ bound)
  cases outer <;>
    dsimp only [copyMemory, copyInput, marked] at copy used count usedVal countVal mark push got target <;>
    simp only [Bool.false_eq_true, ↓reduceIte] at source copy used count usedVal countVal mark push got target
  all_goals
    refine ⟨?_, ?_, ?_⟩
    rotate_left
    · first
      | change program.runBlock (dialect Extracted.programImage) ⟨.l107adb, a, m⟩ = _
        have clearOk := clear rfl
        cfg_eval [rsp, df, clearOk, source, copy, used, count, usedVal, countVal, zext,
          addr 8, mark, push, got, target]
      | change program.runBlock (dialect Extracted.programImage) ⟨.l107da7, a, m⟩ = _
        cfg_eval [rsp, df, ← source, copy, used, count, usedVal, countVal, zext,
          addr 8, mark, push, got, target]
      rw [ite_eq_left (Or.inr trivial), ite_eq_left ⟨target, push, got⟩]
      rfl
    · refine ⟨rfl, remaining, rfl, congrArg (Value.mk 64) (addr 9), remaining,
        rfl, rfl, rfl, ?_, ?_⟩
      · intro ⟨j,_⟩ hj
        simp only [savedRegs, List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl | rfl | rfl <;> rfl
      · intro ⟨j,_⟩ hj
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
        rcases hj with rfl | rfl | rfl | rfl | rfl | rfl <;>
          first
          | rfl
          | exact widths 3 (by decide)
          | exact widths 5 (by decide)
          | exact widths 14 (by decide)

theorem branch (outer : Bool) (a : Registers) (m : Ram) (n : Nat) (small : n%64 < 56)
    (rem : a[(if outer then 15 else 12 : Fin Reg.count)].get 64 = BitVec.ofNat 64 (63-n%64)) :
    ∃ b, Reaches (branchLabel outer) a m (compressStart outer) b m ∧
      ∀ i : Fin Reg.count, i.val ∈ [3,4,5,12,13,14,15,22,39,50,51] → b[i] = a[i] := by
  have route : ∀ k : Fin 64,
      let flags := cmpSpec (BitVec.ofNat 64 (63-k.val)) 7
      (!(flags.CF || flags.ZF)) = decide (k.val < 56) := by
    decide +kernel
  have h := route ⟨n % 64, Nat.mod_lt _ (by decide)⟩
  simp only [small, decide_true] at h
  suffices ∃ b, program.runBlock (dialect Extracted.programImage) ⟨branchLabel outer, a, m⟩ =
      .jump ⟨compressStart outer, b, m⟩ ∧
      ∀ i : Fin Reg.count, i.val ∈ [3,4,5,12,13,14,15,22,39,50,51] → b[i] = a[i] by
    obtain ⟨b, run, keep⟩ := this
    exact ⟨b, .step (congrArg (Transfer.next _ []) run) (.refl _), keep⟩
  cases outer
  all_goals
    refine ⟨?_, ?_, ?_⟩
    rotate_left
    · first
      | change program.runBlock (dialect Extracted.programImage) ⟨.l107b27, a, m⟩ = _
        change a[12].get 64 = _ at rem
      | change program.runBlock (dialect Extracted.programImage) ⟨.l107dec, a, m⟩ = _
        change a[15].get 64 = _ at rem
      cfg_eval
      rw [rem, h, ite_eq_left rfl]
      rfl
    · intro ⟨j,_⟩ hj
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

end K256.Proofs.Signing.UpdateV.Finalize.Mark
