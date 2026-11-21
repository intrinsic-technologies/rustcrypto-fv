import K256.Proofs.Verify.Core.Lincomb.Loop.ColumnFrame

namespace K256.Proofs.Verify.Core.Lincomb.Loop

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1

private theorem nextBlock {l t r : Label} {a b c : Registers} {m n store : Ram}
    (run : program.runBlock (dialect Extracted.programImage) ⟨l,a,m⟩ = .jump ⟨t,b,n⟩)
    (endRun : Reaches t b n r c store) : Reaches l a m r c store :=
  .step (by change (program.runBlock _ _).next _ [] = _; rw [run]; rfl) endRun

local macro "advance_to " l:term " using " "[" hs:Lean.Parser.Tactic.simpLemma,* "]" : tactic =>
  `(tactic| (
    refine nextBlock (t := $l) (b := ?_) (n := ?_) ?edge ?_
    case edge =>
      cfg_eval [$hs,*]
      rfl))

private theorem rowNonzero {table : BitVec 64} (h : Readable m table 0x1340) (off : BitVec 64)
    (pos : 0 < off.toNat) (small : off.toNat ≤ 0x1340) : table + off ≠ 0 := by
  intro eq
  have low := h.low
  have natEq := congrArg BitVec.toNat eq
  rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)] at natEq
  change table.toNat + off.toNat = 0 at natEq
  omega

private theorem advanceComponent {a b : Registers} {m n : Ram} {sp dst table : BitVec 64}
    {k : Nat} {p : Curve.Point} {j : Fin 4} (state : Column a m sp dst table k p b n)
    (cursor : Cursor sp table j 1 b n) (baseNe : row table j ≠ 0) :
    ∃ c, Reaches .l11037b b n .l11034e c n ∧ Column a m sp dst table k p c n ∧
      Cursor sp table j 1 c n := by
  have base := congrArg (Value.get 64) cursor.base
  change b[13].get 64 = row table j at base
  have r12 := congrArg (Value.get 64) cursor.component
  change b[12].get 64 = 1 at r12
  have r3 : b[3].get 64 = 2 := congrArg (Value.get 64) cursor.count
  have below : (cmpSpec (1 : BitVec 64) 2).CF = true := by decide
  refine ⟨?_,?path,?post⟩
  case path =>
    advance_to .l110380 using [base, BitVec.and_self, testFlags, beq_eq_false_iff_ne.mpr baseNe]
    advance_to .l11034e using [r12,r3,below]
    exact .refl _
  case post =>
    refine ⟨state.withRegs ?_,cursor.count,cursor.component,cursor.base,cursor.next,cursor.digits⟩
    rintro ⟨i,hi⟩ h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
theorem advance {a b : Registers} {m n : Ram} {sp dst table : BitVec 64} {k : Nat} {p : Curve.Point}
    (j : Fin 4) (entry : RoutineEntry a m sp 0x478) (nonzero : table ≠ 0) (read : Readable m table 0x1340)
    (state : Column a m sp dst table k p b n) (cursor : Cursor sp table j (j.val%2+1) b n) :
    ∃ c store, Reaches .l11037b b n (if j.val = 3 then .l110260 else .l11034e) c store ∧
      Column a m sp dst table k p c store ∧
      (∀ h : j.val + 1 < 4, Cursor sp table ⟨j.val+1,h⟩ ((j.val+1)%2) c store) := by
  have r3 := congrArg (Value.get 64) cursor.count
  change b[3].get 64 = 2 at r3
  have r5 := congrArg (Value.get 64) state.last
  change b[5].get 64 = table + 0x1340 at r5
  have r8 := congrArg (Value.get 64) state.back
  change b[8].get 64 = 0 at r8
  have r12 := congrArg (Value.get 64) cursor.component
  change b[12].get 64 = BitVec.ofNat 64 (j.val%2+1) at r12
  have r13 := congrArg (Value.get 64) cursor.base
  change b[13].get 64 = row table j at r13
  have r14 := congrArg (Value.get 64) cursor.next
  change b[14].get 64 = row table j + 0x9a0 at r14
  have spEq := congrArg (Value.get 64) state.rsp
  change b[4].get 64 = baseSp sp at spEq
  have nz1 := rowNonzero read 0x9a0 (by decide) (by decide)
  have nz2 := rowNonzero read 0x1340 (by decide) (by decide)
  have far : table + (0x9a0 : BitVec 64) ≠ table + 0x1340 := by bv_omega
  have wr : Writable Extracted.programImage n (baseSp sp + 0x18) 8 :=
    (entry.stack.of_frame state.frame).of_offsets (x := sp) (c := -(0x1d8-0x18)) (d := -0x478)
      (by unfold baseSp; bv_omega) (by bv_omega) (by decide)
  have ok : StoreOk Extracted.programImage n (baseSp sp + 0x18) 8 0x110337 5 :=
    ParseSignature.storeOk_of_codeRange (off := 7) wr
      (fun x hx => Common.fnCode_subset_programImage x (code_l110330 x hx)) (by decide)
  have f2 : (cmpSpec (2 : BitVec 64) 2).CF = false := by decide
  rcases (by decide : ∀ j : Fin 4, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) j with rfl|rfl|rfl|rfl
  · obtain ⟨c,run,post,cur⟩ := advanceComponent state cursor nonzero
    exact ⟨c,n,run,post,fun _ => ⟨cur.count,cur.component,cur.base,cur.next,cur.digits⟩⟩
  · change b[12].get 64 = 2 at r12
    have base : b[13].get 64 = table := r13
    have next : b[14].get 64 = table + 0x9a0 := by rw [r14]; change table + _ = _; bv_omega
    refine ⟨?_,(memStore n (baseSp sp + 24) (table + 0x1120 : BitVec 64)),?path,?post⟩
    case path =>
      advance_to .l110380 using [base,BitVec.and_self,testFlags,beq_eq_false_iff_ne.mpr nonzero]
      advance_to .l110385 using [r12,r3,f2]
      advance_to .l11038a using [next,BitVec.and_self,testFlags,beq_eq_false_iff_ne.mpr nz1]
      advance_to .l110330 using [next,r5,cmpSpec_ZF,beq_eq_false_iff_ne.mpr far]
      advance_to .l11034e using [next,spEq,ok,BitVec.add_assoc,BitVec.reduceAdd]
      exact .refl _
    case post =>
      constructor
      · apply Column.withRegs (state.setDigits entry _)
        rintro ⟨i,hi⟩ h
        simp only [List.mem_cons,List.not_mem_nil,or_false] at h
        rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
      · intro _
        refine ⟨rfl,rfl,?_,?_,?_⟩
        · rfl
        · apply congrArg (Value.mk 64)
          change table + 0x1340 = (table + 0x9a0) + 0x9a0
          bv_omega
        · rw [memLoad_memStore_same _ _ _ (by decide) (by decide)]
          change table + 0x1120 = (table + 0x9a0) + 0x780
          bv_omega
  · obtain ⟨c,run,post,cur⟩ := advanceComponent state cursor nz1
    exact ⟨c,n,run,post,fun _ => ⟨cur.count,cur.component,cur.base,cur.next,cur.digits⟩⟩
  · change b[12].get 64 = 2 at r12
    have base : b[13].get 64 = table + 0x9a0 := r13
    have next : b[14].get 64 = table + 0x1340 := by rw [r14]; change table + 0x9a0 + 0x9a0 = _; bv_omega
    refine ⟨?_,n,?path,?post⟩
    case path =>
      advance_to .l110380 using [base,BitVec.and_self,testFlags,beq_eq_false_iff_ne.mpr nz1]
      advance_to .l110385 using [r12,r3,f2]
      advance_to .l11038a using [next,BitVec.and_self,testFlags,beq_eq_false_iff_ne.mpr nz2]
      advance_to .l11038f using [next,r5,cmpSpec_ZF,beq_self_eq_true]
      advance_to .l110260 using [r8,BitVec.and_self,testFlags,beq_self_eq_true]
      exact .refl _
    case post =>
      constructor
      · apply Column.withRegs state
        rintro ⟨i,hi⟩ h
        simp only [List.mem_cons,List.not_mem_nil,or_false] at h
        rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
      · intro h
        exact False.elim ((by decide : ¬(3+1 < 4)) h)

end K256.Proofs.Verify.Core.Lincomb.Loop
