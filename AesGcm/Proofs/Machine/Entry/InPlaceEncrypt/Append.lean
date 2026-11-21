import AesGcm.Proofs.Machine.Entry.InPlaceEncrypt.Selection

namespace AesGcm.Proofs.Machine.Entry.InPlaceEncrypt

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

def appendMemory (args : Values Value Reg.count) (mem : Ram) : Ram :=
  let sp := args[4].get 64
  let dst := args[14].get 64 + args[3].get 64
  let lo := memLoad mem (sp + 32) 64
  let hi := memLoad mem (sp + 40) 64
  memStore (memStore mem (dst + 8) hi) dst lo

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 2048 in
theorem append_runBlock (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) (args : Values Value Reg.count) (mem : Ram)
    (hread : Readable mem (args[4].get 64 + 32) 16)
    (hwrite : Writable code mem (args[14].get 64 + args[3].get 64) 16) :
    ∃ target,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l101724 else .l101444), args, mem⟩ = .jump target ∧
      target.label = (if use256 then .l101739 else .l101459) ∧
      target.store = appendMemory args mem ∧
      target.arguments[0]'(by change 0 < 53; decide) = ⟨64, 0⟩ ∧
      (∀ r : Fin 53, r.val ∈ [3,4,5,12,13,14,15,22,39,50,51] →
        target.arguments[r] = args[r]) ∧
      (GPRsTyped args → GPRsTyped target.arguments) := by
  have hhelperApart {m : Ram} {a : BitVec 64} {n : Nat}
      (h : Writable code m a n) :
      RangeApart a n (if use256 then 0x101724 else 0x101444) 21 := by
    cases use256
    · exact (storeOk_of_codeRange h (fun x hx => hcode x (LIR.code_l101444 x hx))).apart
    · exact (storeOk_of_codeRange h (fun x hx => hcode x (LIR.code_l101724 x hx))).apart
  cases use256
  all_goals
    simp only [Bool.false_eq_true, ↓reduceIte] at hhelperApart ⊢
    refine ⟨?_, ?exec, ?_, ?_, ?_, ?_, ?_⟩
    case exec =>
      first
        | change LIR.program.runBlock (dialect code) ⟨.l101444, args, mem⟩ = _
        | change LIR.program.runBlock (dialect code) ⟨.l101724, args, mem⟩ = _
      cfg_eval []
      refine_norm []
      runtime_guards transfer
      rfl
    all_goals first
      | rfl
      | (intro hTypes; runtime_typed)
      | (rintro ⟨r, hr⟩ hin; simp only [List.mem_cons, List.not_mem_nil, or_false] at hin;
          rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
      | runtime_finish [appendMemory]

theorem append_condition (len capacity high : BitVec 64) :
    (!(orFlags
      ((mergeGPR 8 (if !((cmpSpec (len + 16) capacity).CF ||
        (cmpSpec (len + 16) capacity).ZF) then 1 else 0) (len + 16)).setWidth 8 |||
      (mergeGPR 8 (if !(subSpec len 0xfffffffffffffff0).2.CF then 1 else 0) high).setWidth 8)).ZF.getD false) =
      decide (capacity.toNat < len.toNat + 16) := by
  have hflags (a b : Bool) (x y : BitVec 64) :
      (!(orFlags ((mergeGPR 8 (if a then 1 else 0) x).setWidth 8 |||
        (mergeGPR 8 (if b then 1 else 0) y).setWidth 8)).ZF.getD false) = (b || a) := by
    rw [setWidth_mergeGPR8, setWidth_mergeGPR8]
    cases a <;> cases b <;> rfl
  rw [hflags, append_overflow_or_gt]

private theorem_by subR64Imm8Effect_CF (p : BitVec 64) (dst : BitVec 5) (imm : BitVec 8)
    (t t' : RamState) :
    (EffectPart.flag .CF).value (subR64Imm8Effect p dst imm t) t' = _ := by
  lift_value [subR64Imm8Effect]

def tagScratchMemory (args : Values Value Reg.count) (mem : Ram) : Ram :=
  let sp := args[4].get 64
  memStore (memStore mem (sp + 40) (memLoad mem (sp + 24) 64))
    (sp + 32) (memLoad mem (sp + 16) 64)

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 2048 in
theorem capacity_branch_runBlock (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) (args : Values Value Reg.count) (mem : Ram)
    (hread : Readable mem (args[4].get 64 + 16) 16)
    (hwrite : Writable code mem (args[4].get 64 + 32) 16) :
    ∃ target,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l1016f7 else .l101417), args, mem⟩ = .jump target ∧
      target.label =
        (if (args[3].get 64).toNat + 16 ≤ (args[5].get 64).toNat then
          if use256 then .l101724 else .l101444
        else if use256 then .l101739 else .l101459) ∧
      target.store = tagScratchMemory args mem ∧
      target.arguments[0]'(by change 0 < 53; decide) = ⟨64, 1⟩ ∧
      (∀ r : Fin 53, r.val ∈ [3,4,5,12,13,14,15,22,39,50,51] →
        target.arguments[r] = args[r]) ∧
      (GPRsTyped args → GPRsTyped target.arguments) := by
  have hhelperApart {m : Ram} {a : BitVec 64} {n : Nat}
      (h : Writable code m a n) :
      RangeApart a n (if use256 then 0x1016f7 else 0x101417) 45 := by
    cases use256
    · exact (storeOk_of_codeRange h (fun x hx => hcode x (LIR.code_l101417 x hx))).apart
    · exact (storeOk_of_codeRange h (fun x hx => hcode x (LIR.code_l1016f7 x hx))).apart
  cases use256
  all_goals
    simp only [Bool.false_eq_true, ↓reduceIte] at hhelperApart ⊢
    by_cases hfit : (args[3].get 64).toNat + 16 ≤ (args[5].get 64).toNat
    all_goals
      have hgt : ((args[5].get 64).toNat < (args[3].get 64).toNat + 16) =
          (¬ (args[3].get 64).toNat + 16 ≤ (args[5].get 64).toNat) := propext (by omega)
      simp only [hfit, ↓reduceIte]
      refine ⟨?_, ?exec, ?_, ?_, ?_, ?_, ?_⟩
      case exec =>
        first
          | change LIR.program.runBlock (dialect code) ⟨.l101417, args, mem⟩ = _
          | change LIR.program.runBlock (dialect code) ⟨.l1016f7, args, mem⟩ = _
        cfg_eval [subR64Imm8Effect_CF,
          show (0xf0 : BitVec 8).signExtend 64 = 0xfffffffffffffff0 by rfl]
        simp only [append_condition, hgt, hfit, not_true_eq_false, not_false_eq_true,
          decide_true, decide_false, Bool.false_eq_true, ↓reduceIte]
        runtime_guards transfer
        rfl
      all_goals first
        | rfl
        | (intro hTypes; runtime_typed)
        | (rintro ⟨r, hr⟩ hin; simp only [List.mem_cons, List.not_mem_nil, or_false] at hin;
            rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
        | runtime_finish [tagScratchMemory]

set_option maxHeartbeats 800000 in
set_option maxRecDepth 2048 in
theorem status_runBlock (use256 : Bool) (code : CodeMap)
    (args : Values Value Reg.count) (mem : Ram)
    (hread : Readable mem (args[4].get 64 + 15) 1)
    (hstatus : memLoad mem (args[4].get 64 + 15) 8 = 0) :
    ∃ target,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l1016e9 else .l101409), args, mem⟩ = .jump target ∧
      target.label = (if use256 then .l1016f7 else .l101417) ∧
      target.store = mem ∧
      (∀ r : Fin 53, r.val ∈ [3,4,5,12,13,14,15,22,39,50,51] →
        target.arguments[r] = args[r]) ∧
      (GPRsTyped args → GPRsTyped target.arguments) := by
  cases use256
  all_goals
    simp only [Bool.false_eq_true, ↓reduceIte]
    refine ⟨?_, ?exec, ?_, ?_, ?_, ?_⟩
    case exec =>
      first
        | change LIR.program.runBlock (dialect code) ⟨.l101409, args, mem⟩ = _
        | change LIR.program.runBlock (dialect code) ⟨.l1016e9, args, mem⟩ = _
      cfg_eval []
      refine_norm [hstatus]
      runtime_guards transfer
      rfl
    all_goals first
      | rfl
      | (intro hTypes; runtime_typed)
      | (rintro ⟨r, hr⟩ hin; simp only [List.mem_cons, List.not_mem_nil, or_false] at hin;
          rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 2048 in
theorem tail_reaches_exit (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) (args : Values Value Reg.count) (mem : Ram)
    (hTypes : GPRsTyped args)
    (hread : Readable mem (args[4].get 64 + 15) 17)
    (hstatus : memLoad mem (args[4].get 64 + 15) 8 = 0)
    (hwrite : Writable code mem (args[4].get 64 + 32) 16)
    (hbuffer : (args[3].get 64).toNat + 16 ≤ (args[5].get 64).toNat →
      Writable code mem (args[14].get 64 + args[3].get 64) 16) :
    ∃ target,
      (LIR.program.sem (dialect code)).Reaches
        ⟨⟨(if use256 then .l1016e9 else .l101409), args, mem⟩, []⟩ ⟨target, []⟩ ∧
      target.label = (if use256 then .l101739 else .l101459) ∧
      target.store =
        (if (args[3].get 64).toNat + 16 ≤ (args[5].get 64).toNat then
          appendMemory args (tagScratchMemory args mem) else tagScratchMemory args mem) ∧
      target.arguments[0]'(by change 0 < 53; decide) =
        ⟨64, if (args[3].get 64).toNat + 16 ≤ (args[5].get 64).toNat then 0 else 1⟩ ∧
      (∀ r : Fin 53, r.val ∈ [3,4,5,12,13,14,15,22,39,50,51] →
        target.arguments[r] = args[r]) ∧
      GPRsTyped target.arguments := by
  have hreadStatus : Readable mem (args[4].get 64 + 15) 1 :=
    hread.of_offsets rfl rfl (by decide)
  have hreadTag : Readable mem (args[4].get 64 + 16) 16 :=
    hread.of_offsets rfl rfl (by decide)
  obtain ⟨tested, htest, tl, tm, tk, tt⟩ :=
    status_runBlock use256 code args mem hreadStatus hstatus
  have t4 := tk ⟨4, by decide⟩ (by decide)
  have t3 := tk ⟨3, by decide⟩ (by decide)
  have t5 := tk ⟨5, by decide⟩ (by decide)
  simp only [Fin.getElem_fin] at t4 t3 t5
  obtain ⟨branched, hbranch, bl, bm, b0, bk, bt⟩ :=
    capacity_branch_runBlock use256 code hcode tested.arguments tested.store
      (by rw [tm, t4]; exact hreadTag)
      (by rw [tm, t4]; exact hwrite)
  have hfirst : (LIR.program.sem (dialect code)).Reaches
      ⟨⟨(if use256 then .l1016e9 else .l101409), args, mem⟩, []⟩ ⟨tested, []⟩ := by
    refine Semantics.Reaches.single ?_
    simp only [Program.sem, Program.step, htest, Transfer.next]
  have hsecond : (LIR.program.sem (dialect code)).Reaches
      ⟨tested, []⟩ ⟨branched, []⟩ := by
    refine Semantics.Reaches.single ?_
    change LIR.program.step (dialect code) ⟨tested, []⟩ = _
    have htloc : tested = ⟨(if use256 then .l1016f7 else .l101417), tested.arguments, tested.store⟩ := by
      cases tested
      cases tl
      rfl
    rw [htloc]
    simp only [Program.step, hbranch, Transfer.next]
  have bkeep (r : Fin 53) (hr : r.val ∈ [3,4,5,12,13,14,15,22,39,50,51]) :
      branched.arguments[r] = args[r] := (bk r hr).trans (tk r hr)
  have b4 := bkeep ⟨4, by decide⟩ (by decide)
  have b3 := bkeep ⟨3, by decide⟩ (by decide)
  have b14 := bkeep ⟨14, by decide⟩ (by decide)
  simp only [Fin.getElem_fin] at b4 b3 b14
  have bmem : branched.store = tagScratchMemory args mem := by
    simpa only [tagScratchMemory, t4, tm] using bm
  have btypes := bt (tt hTypes)
  rw [t3, t5] at bl
  by_cases hfit : (args[3].get 64).toNat + 16 ≤ (args[5].get 64).toNat
  · have bread : Readable branched.store ((branched.arguments[4]'(by change 4 < 53; decide)).get 64 + 32) 16 := by
      rw [b4, bmem]
      exact (hwrite.readable.memStore _ _).memStore _ _
    have bwrite : Writable code branched.store
        ((branched.arguments[14]'(by change 14 < 53; decide)).get 64 + (branched.arguments[3]'(by change 3 < 53; decide)).get 64) 16 := by
      rw [b14, b3, bmem]
      exact ((hbuffer hfit).memStore _ _).memStore _ _
    obtain ⟨appended, happend, al, am, a0, ak, atypes⟩ :=
      append_runBlock use256 code hcode branched.arguments branched.store bread bwrite
    have hthird : (LIR.program.sem (dialect code)).Reaches
        ⟨branched, []⟩ ⟨appended, []⟩ := by
      refine Semantics.Reaches.single ?_
      change LIR.program.step (dialect code) ⟨branched, []⟩ = _
      have hbloc : branched =
          ⟨(if use256 then .l101724 else .l101444), branched.arguments, branched.store⟩ := by
        cases branched
        simp only [hfit, ↓reduceIte] at bl
        cases bl
        rfl
      rw [hbloc]
      simp only [Program.step, happend, Transfer.next]
    refine ⟨appended, (hfirst.trans hsecond).trans hthird, al, ?_, ?_, ?_, atypes btypes⟩
    · simpa only [hfit, ↓reduceIte, appendMemory, b4, b3, b14, bmem] using am
    · simpa only [hfit, ↓reduceIte] using a0
    · intro r hr
      exact (ak r hr).trans (bkeep r hr)
  · refine ⟨branched, hfirst.trans hsecond, ?_, ?_, ?_, bkeep, btypes⟩
    · simpa only [hfit, ↓reduceIte] using bl
    · simpa only [hfit, ↓reduceIte] using bmem
    · simpa only [hfit, ↓reduceIte] using b0

end AesGcm.Proofs.Machine.Entry.InPlaceEncrypt
