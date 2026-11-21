import K256.Proofs.Verify.Core.Lincomb.Recode.Odd

namespace K256.Proofs.Verify.Core.Lincomb.Recode

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

structure IndexAdvance (a b : Registers) (sp : BitVec 64) (i step c : Nat) : Prop where
  stack : b[4] = ⟨64,sp-136⟩
  width : b[12] = ⟨64,5⟩
  index : b[15] = ⟨64,BitVec.ofNat 64 i⟩
  length : b[14] = ⟨64,BitVec.ofNat 64 (i+step)⟩
  stride : b[5] = ⟨64,BitVec.ofNat 64 step⟩
  carry : b[13] = ⟨64,BitVec.ofNat 64 c⟩
  saved : ControlSaved a b

theorem advanceOne {a b : Registers} {m : Ram} {sp dst : BitVec 64} {i w : Nat}
    (regs : OddRegisters a b sp dst i w) (one : Naf.skip (128-i) w = 1) :
    ∃ r, Continues .l110830 b m .l110833 r m ∧ IndexAdvance a r sp i 1 (Naf.carry w) := by
  have len : b[14].get 64 = BitVec.ofNat 64 i := congrArg (Value.get 64) regs.length
  have inc : BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (i+1) := by rw [BitVec.ofNat_add]; rfl
  refine ⟨?_, continueJump ?step, ?post⟩
  case step =>
    cfg_eval [len, inc]
    rfl
  case post =>
    refine ⟨regs.stack, regs.width, regs.bitIndex, ?_, ?_, regs.carry, ?_⟩
    · first | rfl | exact congrArg (fun x : BitVec 64 => (⟨64,x⟩ : Value)) inc
    · rw [regs.skip, one]
      rfl
    · intro ⟨j,hj⟩ keep
      simp only [List.mem_cons, List.not_mem_nil, or_false] at keep
      rcases keep with rfl | rfl | rfl | rfl
      · exact regs.saved 22 (by decide)
      · exact regs.saved 39 (by decide)
      · exact regs.saved 50 (by decide)
      · exact regs.saved 51 (by decide)

theorem advanceIndex {a b : Registers} {m : Ram} {sp dst : BitVec 64} {i s c : Nat}
    (regs : IndexAdvance a b sp i s c) (fields : LoopMemory m sp dst) (limit : i+s ≤ 128)
    (read : LoadOk m (sp-112) 8) :
    ∃ r : Registers, Continues .l110833 b m (nextRound (i+s)) r m ∧ LoopRegisters a r sp (i+s) c := by
  have rsp : b[4].get 64 = sp-136 := congrArg (Value.get 64) regs.stack
  have index : b[15].get 64 = BitVec.ofNat 64 i := congrArg (Value.get 64) regs.index
  have skip : b[5].get 64 = BitVec.ofNat 64 s := congrArg (Value.get 64) regs.stride
  have inc : BitVec.ofNat 64 i + BitVec.ofNat 64 s = BitVec.ofNat 64 (i+s) :=
    (BitVec.ofNat_add i s).symm
  have cf : (cmpSpec (BitVec.ofNat 64 (i+s)) 128).CF = decide (i+s < 128) := by
    rw [cmpSpec_CF, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i+s < 2^64)]
    rfl
  by_cases loop : i+s < 128
  all_goals
    refine ⟨?_, continueJump ?step, ?post⟩
    case step =>
      cfg_eval [rsp, index, skip, inc, read, fields.bits, cf]
      first
      | rw [decide_eq_true loop, ite_eq_right (by decide : (!true) ≠ true),
          show nextRound (i+s) = .l110847 from ite_eq_left loop]
      | rw [decide_eq_false loop, ite_eq_left (by rfl),
          show nextRound (i+s) = .l11093a from ite_eq_right loop]
    case post =>
      refine ⟨regs.stack, regs.width, rfl, regs.length, rfl, regs.carry, ?_⟩
      intro ⟨j,hj⟩ keep
      simp only [List.mem_cons, List.not_mem_nil, or_false] at keep
      rcases keep with rfl | rfl | rfl | rfl
      · exact regs.saved 22 (by decide)
      · exact regs.saved 39 (by decide)
      · exact regs.saved 50 (by decide)
      · exact regs.saved 51 (by decide)

end K256.Proofs.Verify.Core.Lincomb.Recode
