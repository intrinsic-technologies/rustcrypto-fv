import K256.Proofs.Verify.Core.Lincomb.Recode.Even

namespace K256.Proofs.Verify.Core.Lincomb.Recode

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

theorem finalCarry {a b : Registers} {m : Ram} {sp dst : BitVec 64} {c : Nat}
    (regs : LoopRegisters a b sp 128 c) (bound : c ≤ 1) (fields : LoopMemory m sp dst)
    (capacity : LoadOk m (sp-136) 8) (dest : LoadOk m (sp-120) 8)
    (write : Writable Extracted.programImage m dst 257) :
    let m' := if c = 0 then m else memStore m (digitAddr dst 128) (1 : BitVec 8)
    ∃ r : Registers, Continues .l11093a b m .l110955 r m' ∧
      r[4] = ⟨64,sp-136⟩ ∧ r[14] = ⟨64, BitVec.ofNat 64 (128+c)⟩ ∧ ControlSaved a r := by
  have rsp : b[4].get 64 = sp-136 := congrArg (Value.get 64) regs.stack
  have len : b[14].get 64 = 128 := congrArg (Value.get 64) regs.length
  have cy : b[13].get 64 = BitVec.ofNat 64 c := congrArg (Value.get 64) regs.carry
  have ok : StoreOk Extracted.programImage m (dst+128) 1 0x11094d 5 :=
    storeGuard (off := 5) (writableDigit write (by decide)) code_l110948 (by decide)
  have cases : c = 0 ∨ c = 1 := by omega
  rcases cases with rfl | rfl
  · refine ⟨?_, continueJump ?step, ?post⟩
    case step =>
      cfg_eval [cy, testFlags, show ((0 : BitVec 64) == 0) = true by decide]
      rfl
    case post =>
      refine ⟨regs.stack,regs.length,?_⟩
      intro ⟨j,hj⟩ keep
      simp only [List.mem_cons,List.not_mem_nil,or_false] at keep
      rcases keep with rfl | rfl | rfl | rfl
      · exact regs.saved 22 (by decide)
      · exact regs.saved 39 (by decide)
      · exact regs.saved 50 (by decide)
      · exact regs.saved 51 (by decide)
  · have cf : (cmpSpec (128 : BitVec 64) 257).CF = true := by decide
    have route : ∃ r s t : Registers,
        program.runBlock machine ⟨.l11093a,b,m⟩ = .jump ⟨.l11093f,r,m⟩ ∧
        program.runBlock machine ⟨.l11093f,r,m⟩ = .jump ⟨.l110948,s,m⟩ ∧
        program.runBlock machine ⟨.l110948,s,m⟩ =
          .jump ⟨.l110955,t,memStore m (digitAddr dst 128) (1 : BitVec 8)⟩ ∧
        t[4] = ⟨64,sp-136⟩ ∧ t[14] = ⟨64,129⟩ ∧ ControlSaved a t := by
      refine ⟨?_,?_,?_,?first,?second,?third,?post⟩
      case first =>
        cfg_eval [cy, testFlags, show ((1 : BitVec 64) == 0) = false by decide]
        rfl
      case second =>
        cfg_eval [rsp, len, capacity, fields.limit, cf]
        rfl
      case third =>
        cfg_eval [rsp, len, dest, fields.buffer]
        rw [ite_eq_left ok]
        rfl
      case post =>
        refine ⟨regs.stack,rfl,?_⟩
        intro ⟨j,hj⟩ keep
        simp only [List.mem_cons,List.not_mem_nil,or_false] at keep
        rcases keep with rfl | rfl | rfl | rfl
        · exact regs.saved 22 (by decide)
        · exact regs.saved 39 (by decide)
        · exact regs.saved 50 (by decide)
        · exact regs.saved 51 (by decide)
    obtain ⟨r,s,t,first,second,third,sp',count,kept⟩ := route
    exact ⟨t,(continueJump first).trans ((continueJump second).trans (continueJump third)),sp',count,kept⟩

end K256.Proofs.Verify.Core.Lincomb.Recode
