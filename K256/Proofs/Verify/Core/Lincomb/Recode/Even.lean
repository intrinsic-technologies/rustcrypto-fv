import K256.Proofs.Verify.Core.Lincomb.Recode.Digits

namespace K256.Proofs.Verify.Core.Lincomb.Recode

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

abbrev nextRound (i : Nat) : Label := if i < 128 then .l110847 else .l11093a

def Continues (fromLabel : Label) (a : Registers) (m : Ram)
    (toLabel : Label) (b : Registers) (n : Ram) : Prop :=
  ∀ out, program.Exec machine ⟨⟨toLabel,b,n⟩,[]⟩ out →
    program.Exec machine ⟨⟨fromLabel,a,m⟩,[]⟩ out

theorem Continues.trans {l₁ l₂ l₃ : Label} {a b c : Registers} {m n p : Ram}
    (ab : Continues l₁ a m l₂ b n) (bc : Continues l₂ b n l₃ c p) :
    Continues l₁ a m l₃ c p := fun out tail => ab out (bc out tail)

theorem continueJump {l₁ l₂ : Label} {a b : Registers} {m n : Ram}
    (h : program.runBlock machine ⟨l₁,a,m⟩ = .jump ⟨l₂,b,n⟩) :
    Continues l₁ a m l₂ b n := fun _ tail => jump h tail

theorem evenStep {a b : Registers} {m : Ram} {sp dst : BitVec 64} {i c : Nat}
    (regs : LoopRegisters a b sp i c) (fields : LoopMemory m sp dst) (bound : i < 128)
    (dest : b[6].get 64 = dst) (capacity : LoadOk m (sp-136) 8)
    (write : Writable Extracted.programImage m dst 257)
    (bits : LoadOk (memStore m (digitAddr dst i) (0 : BitVec 8)) (sp-112) 8)
    (bitsWord : memLoad (memStore m (digitAddr dst i) (0 : BitVec 8)) (sp-112) 64 = 128) :
    ∃ e, Continues .l11089f b m (nextRound (i+1)) e (memStore m (digitAddr dst i) (0 : BitVec 8)) ∧
      LoopRegisters a e sp (i+1) c := by
  let m' := memStore m (digitAddr dst i) (0 : BitVec 8)
  have rsp : b[4].get 64 = sp-136 := congrArg (Value.get 64) regs.stack
  have length : b[14].get 64 = BitVec.ofNat 64 i := congrArg (Value.get 64) regs.length
  have numer : (BitVec.ofNat 64 i).toNat = i := by
    exact Nat.mod_eq_of_lt (by omega)
  have capCF : (cmpSpec (257 : BitVec 64) (BitVec.ofNat 64 i)).CF = false := by
    simp only [cmpSpec_CF, numer, BitVec.reduceToNat, decide_eq_false_iff_not]
    omega
  have capZF : (cmpSpec (257 : BitVec 64) (BitVec.ofNat 64 i)).ZF = false := by
    rw [cmpSpec_ZF, beq_eq_false_iff_ne]
    intro h
    have eq := congrArg BitVec.toNat h
    simp only [numer, BitVec.reduceToNat] at eq
    omega
  have capStep : ∃ r, program.runBlock machine ⟨.l11089f,b,m⟩ = .jump ⟨.l1108a9,r,m⟩ ∧
      r[4] = b[4] ∧ r[6] = b[6] ∧ r[14] = b[14] ∧ r[15] = b[15] ∧
      ControlSaved b r ∧ r[12] = b[12] ∧ r[13] = b[13] := by
    refine ⟨?_, ?step, ?post⟩
    case step =>
      cfg_eval [rsp, length, capacity, fields.limit, capCF, capZF]
      rfl
    case post =>
      refine ⟨rfl, rfl, rfl, rfl, ?_, rfl, rfl⟩
      intro ⟨j, hj⟩ live
      simp only [List.mem_cons, List.not_mem_nil, or_false] at live
      rcases live with rfl | rfl | rfl | rfl <;> rfl
  obtain ⟨r, step, r4, r6, r14, r15, keep, r12, r13⟩ := capStep
  have rrsp : r[4].get 64 = sp-136 := congrArg (Value.get 64) (r4.trans regs.stack)
  have rdest : r[6].get 64 = dst := (congrArg (Value.get 64) r6).trans dest
  have rlength : r[14].get 64 = BitVec.ofNat 64 i := congrArg (Value.get 64) (r14.trans regs.length)
  have rindex : r[15].get 64 = BitVec.ofNat 64 i := congrArg (Value.get 64) (r15.trans regs.bitIndex)
  have ok : StoreOk Extracted.programImage m (digitAddr dst i) 1 0x1108a9 5 :=
    storeGuard (off := 0) (writableDigit write (by omega)) code_l1108a9 (by decide)
  have inc : BitVec.ofNat 64 i + 1 = BitVec.ofNat 64 (i+1) := by rw [BitVec.ofNat_add]; rfl
  have contCF : (cmpSpec (BitVec.ofNat 64 (i+1)) 128).CF = decide (i+1 < 128) := by
    rw [cmpSpec_CF, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i+1 < 2^64)]
    rfl
  let l := if i+1 < 128 then Label.l110847 else Label.l1108c1
  have branch : ∃ e : Registers, program.runBlock machine ⟨.l1108a9,r,m⟩ = .jump ⟨l,e,m'⟩ ∧
      LoopRegisters a e sp (i+1) c := by
    by_cases running : i+1 < 128
    all_goals
      refine ⟨?_, ?step, ?post⟩
      case step =>
        cfg_eval [rrsp, rdest, rlength, rindex, ok, inc, bits, bitsWord, contCF]
        first
        | rw [decide_eq_true running, ite_eq_left (by rfl), show l = .l110847 from ite_eq_left running]
        | rw [decide_eq_false running, ite_eq_right (by decide : false ≠ true), show l = .l1108c1 from ite_eq_right running]
      case post =>
        refine ⟨r4.trans regs.stack, r12.trans regs.width, rfl, rfl, rfl, r13.trans regs.carry, ?_⟩
        apply regs.saved.trans
        apply keep.trans
        intro ⟨j,hj⟩ live
        simp only [List.mem_cons, List.not_mem_nil, or_false] at live
        rcases live with rfl | rfl | rfl | rfl <;> rfl
  obtain ⟨e, edge, nextRegs⟩ := branch
  by_cases running : i+1 < 128
  · refine ⟨e, ?_, nextRegs⟩
    simpa only [nextRound, running, ite_true, l] using
      (continueJump step).trans (continueJump edge)
  · have exit : ∃ f, program.runBlock machine ⟨.l1108c1,e,m'⟩ = .jump ⟨.l11093a,f,m'⟩ ∧
        LoopRegisters a f sp (i+1) c := by
      refine ⟨?_, ?step, ?post⟩
      case step =>
        cfg_eval
        rfl
      case post =>
        refine ⟨nextRegs.stack, nextRegs.width, nextRegs.bitIndex, nextRegs.length,
          nextRegs.negIndex, nextRegs.carry, ?_⟩
        intro ⟨j, hj⟩ live
        simp only [List.mem_cons, List.not_mem_nil, or_false] at live
        rcases live with rfl | rfl | rfl | rfl
        · exact nextRegs.saved 22 (by decide)
        · exact nextRegs.saved 39 (by decide)
        · exact nextRegs.saved 50 (by decide)
        · exact nextRegs.saved 51 (by decide)
    obtain ⟨f, finish, finalRegs⟩ := exit
    refine ⟨f, ?_, finalRegs⟩
    have lbl : l = .l1108c1 := ite_eq_right running
    rw [lbl] at edge
    rw [show nextRound (i+1) = .l11093a from ite_eq_right running]
    have later : Continues .l1108a9 r m .l1108c1 e m' := continueJump edge
    exact (continueJump step).trans (later.trans (continueJump finish))

end K256.Proofs.Verify.Core.Lincomb.Recode
