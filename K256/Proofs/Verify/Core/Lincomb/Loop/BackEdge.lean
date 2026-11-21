import K256.Proofs.Verify.Core.Lincomb.Loop.State

namespace K256.Proofs.Verify.Core.Lincomb.Loop

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Multiply (Projective)

theorem backEdge {initial a : Registers} {original m : Ram} {sp dst dataPtr : BitVec 64}
    {bases : Fin 4 → Curve.Point} {ds : Fin 4 → List Int} {k : Nat}
    (entry : RoutineEntry initial original sp 0x478) (s : SavedFrame initial original sp dst a m)
    (count : a[9].get 64 = BitVec.ofNat 64 k) (bound : k ≤ 129)
    (last : a[5] = ⟨64,dataPtr + 0x1340⟩) (back : a[8] = ⟨64,0⟩)
    (frontMem : memLoad m (baseSp sp + 0x40) 64 = 0)
    (nextMem : memLoad m (baseSp sp + 0x38) 64 = dataPtr)
    (backMem : memLoad m (baseSp sp) 64 = 0)
    (point : ∃ q : Projective, q.Stored m (baseSp sp + 0x130) ∧ q.valid ∧ q.value = suffix bases ds k)
    (inactive : memLoad m (baseSp sp + 0x28) 8 &&& 1 = 0 → suffix bases ds k = .infinity) :
    ∃ b : Registers, Reaches .l110260 a m (if k = 0 then .l11075a else .l110278) b m ∧
      RoundState initial original sp dst dataPtr bases ds k b m := by
  have read := (entry.stack.of_frame s.frame).readable
  have spEq : a[4].get 64 = baseSp sp := congrArg (Value.get 64) s.rsp
  have slot (off : BitVec 64) (fit : ((off - 0x1d8) - (0 - 0x478)).toNat + 8 ≤ 0x478) :
      LoadOk m (baseSp sp + off) 8 :=
    LoadOk.of_offsets (x := sp) read (by unfold baseSp; bv_omega)
      (by change sp - 0x478 = sp + (0 - 0x478); bv_omega) fit
  have zero : (BitVec.ofNat 64 k == 0) = decide (k = 0) := by
    by_cases h : k = 0
    · subst k; rfl
    · have hn : BitVec.ofNat 64 k ≠ 0 := by
        intro eq
        have := congrArg BitVec.toNat eq
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)] at this
        exact h this
      simpa [h] using hn
  by_cases h : k = 0
  all_goals
    refine ⟨?_,?reach,?state⟩
    case reach =>
      apply Semantics.Reaches.single
      change (program.runBlock (dialect Extracted.programImage) _).next _ [] = _
      first | rw [ite_eq_left h] | rw [ite_eq_right h]
      cfg_eval [spEq, slot 0x40 (by decide), slot 0x38 (by decide), slot 0x30 (by decide), count]
      simp only [BitVec.and_self, testFlags, Option.getD_some, zero, h, decide_false,
        Bool.false_eq_true, ↓reduceIte, Transfer.next]
      rfl
    case state =>
      refine ⟨⟨s.rsp,s.dest,s.rbx,s.r12,s.r13,s.r14,s.r15,s.rbp,?_,s.frame⟩,
        count,frontMem,nextMem,last,back,frontMem,nextMem,backMem,point,inactive⟩
      rintro ⟨i,hi⟩ live
      simp only [List.mem_cons,List.not_mem_nil,or_false] at live
      rcases live with rfl|rfl|rfl|rfl
      · exact s.control 22 (by decide)
      · exact s.control 39 (by decide)
      · exact s.control 50 (by decide)
      · exact s.control 51 (by decide)

end K256.Proofs.Verify.Core.Lincomb.Loop
