import AesGcm.Proofs.Machine.CTR.KeyCopy
import AesGcm.Proofs.Machine.Runtime.Memcpy
import AesGcm.Proofs.Machine.Runtime.Frame
import AesGcm.Proofs.Machine.Runtime.Call

namespace AesGcm.Proofs.Machine.CTR

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift
  X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

private theorem wordsAt_of_byteCopy {before after : Ram} {src dst : BitVec 64}
    {w n : Nat} {words : Vector (BitVec w) n} (hs : WordsAt before src w words)
    (hc : ∀ j < w / 8 * n,
      after[dst + BitVec.ofNat 64 j]? = before[src + BitVec.ofNat 64 j]?) :
    WordsAt after dst w words := by
  intro i hi
  apply Eq.trans _ (hs i hi)
  apply memLoad_congr
  intro j hj
  have h := hc (w / 8 * i + j) (by
    have hle := Nat.mul_le_mul_left (w / 8) (Nat.succ_le_of_lt hi)
    rw [Nat.mul_succ] at hle
    omega)
  simp only [wordAddr, BitVec.add_assoc, ← BitVec.ofNat_add, memByte, PhysicalMemory.read, h]

set_option maxHeartbeats 800000 in
theorem key_setup_reaches (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (args : Values Value Reg.count) (mem : Ram) (sp schedule : BitVec 64)
    (keys : Vector (BitVec 16) (keyWords use256))
    (hTypes : GPRsTyped args)
    (hDF : args[22] = ⟨1, 0⟩)
    (h39 : args[39] = ⟨32, args[39].get 32⟩)
    (h50 : args[50] = ⟨16, args[50].get 16⟩)
    (h51 : args[51] = ⟨16, args[51].get 16⟩)
    (hAlign : sp.toNat % 16 = 0)
    (hread : Readable mem schedule (2 * keyWords use256))
    (hwrite : Writable code mem (sp + wideningOffset use256) (8 * keyWords use256))
    (hapart : RangeApart (sp + wideningOffset use256) (8 * keyWords use256)
      schedule (2 * keyWords use256))
    (hkeys : WordsAt mem schedule 16 keys)
    (hDest : Writable code mem (sp + 0x158) (8 * keyWords use256))
    (hStack : Writable code mem (sp - 8) 352)
    (hSlotRead : Readable mem 0x201208 8)
    (hSlot : memLoad mem 0x201208 64 = 0x103f00)
    (hApart : (sp + wideningOffset use256).toNat + 8 * keyWords use256 ≤ 0x201208 ∨
      0x201210 ≤ sp.toNat - 8) :
    ∃ next : LIR.lifted.Location,
      (LIR.program.sem (dialect code)).Reaches
        ⟨⟨wideningLabel use256, wideningRegisters args schedule sp 0, mem⟩, []⟩
        ⟨next, []⟩ ∧
      next.label = (if use256 then .l108590 else .l107100) ∧
      Readable next.store (sp + 344) (if use256 then 960 else 704) ∧
      WordsAt next.store (sp + 344) 64 (keys.map Fixslice16.widenWord) ∧
      next.arguments[4]'(by change 4 < 53; decide) = ⟨64, sp⟩ ∧
      GPRsTyped next.arguments ∧
      RamWriteFrame mem next.store
        [span (sp - 8) 352, span (sp + 0x158) (8 * keyWords use256),
          span (sp + wideningOffset use256) (8 * keyWords use256)] ∧
      (∀ r : Fin 53, r.val ∈ [3, 22, 39, 50, 51] →
        next.arguments[r] = args[r]) ∧
      memLoad next.store (sp + 336) 64 = schedule := by
  obtain ⟨mid, widen, midLabel, widened, widenFrame, _, regs, midTyped⟩ :=
    widening_loop use256 code hcode keys 0 (by cases use256 <;> decide)
      args schedule sp mem hTypes hread hwrite hapart hkeys (by intros; omega)
  have stackLow := hStack.readable.low
  have spRoom : 8 ≤ sp.toNat := by bv_omega
  have nsub : (sp - 8).toNat = sp.toNat - 8 := by bv_omega
  rw [nsub] at stackLow
  have ndst : (sp + 344).toNat = sp.toNat + 344 := by bv_omega
  have nsave : (sp + 336).toNat = sp.toNat + 336 := by bv_omega
  have nsrc : (sp + wideningOffset use256).toNat =
      sp.toNat + (if use256 then 1304 else 1048) := by
    cases use256 <;> simp only [wideningOffset, Bool.false_eq_true, ↓reduceIte] <;> bv_omega
  have gap : 344 + 8 * keyWords use256 = (if use256 then 1304 else 1048) := by
    cases use256 <;> rfl
  have srcLow := hwrite.readable.low
  have dstLow := hDest.readable.low
  rw [nsrc] at srcLow hApart
  rw [ndst] at dstLow
  have slotOutside : Outside [span (sp + wideningOffset use256) (8 * keyWords use256)]
      0x201208 8 := by
    refine ⟨by decide, fun r hr ↦ ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    change 0x201210 ≤ (sp + wideningOffset use256).toNat ∨ (sp + wideningOffset use256).toNat + 8 * keyWords use256 ≤ 0x201208
    rw [nsrc]
    omega
  have midSp : mid.arguments[4]'(by change 4 < 53; decide) = ⟨64,sp⟩ :=
    regs 4 (by decide) (by decide) (by decide) (by decide) (by decide)
  have midRax : mid.arguments[0]'(by change 0 < 53; decide) = ⟨64,schedule⟩ :=
    regs 0 (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨callee, call, label, c4, c7, c6, c2, store, keep, typed, prepareFrame⟩ :=
    keyCopy_prepare use256 code hcode mid.arguments mid.store sp midTyped
      (congrArg (Value.get 64) midSp) (hStack.of_frame widenFrame)
      (hSlotRead.of_frame widenFrame) ((widenFrame.memLoad_eq slotOutside).trans hSlot) (by omega)
  let av : Values Value Reg.count := callee.arguments
  have rsp : av[4].get 64 = sp - 8 := congrArg (Value.get 64) c4
  have dst : av[7].get 64 = sp + 344 := congrArg (Value.get 64) c7
  have src : av[6].get 64 = sp + wideningOffset use256 := congrArg (Value.get 64) c6
  have count : (av[2].get 64).toNat = 8 * keyWords use256 := by
    change ((callee.arguments[2]'(by change 2 < 53; decide)).get 64).toNat = _
    rw [c2]
    cases use256 <;> rfl
  have preserved (r : Fin 53) (hr : r.val ∈ [3,22,39,50,51]) : av[r.val] = args[r.val] := by
    have hk := keep r (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hr ⊢; omega)
    have hne (i : Fin 53) (hi : i.val ∈ [1,8,9,10,19]) : r ≠ i := by
      intro eq; subst i
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr hi
      omega
    refine hk.trans ((regs r (hne 1 (by decide)) (hne 8 (by decide)) (hne 9 (by decide))
      (hne 10 (by decide)) (hne 19 (by decide))).trans ?_)
    rcases r with ⟨r,lt⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> rfl
  have same39 : av[39] = args[39] := preserved 39 (by decide)
  have same50 : av[50] = args[50] := preserved 50 (by decide)
  have same51 : av[51] = args[51] := preserved 51 (by decide)
  have saved : memLoad callee.store (sp + 336) 64 = schedule := by
    rw [store, memLoad_memStore_of_rangeApart, memLoad_memStore_same, midRax]
    · rfl
    · decide
    · decide
    · apply RangeApart.of_toNat <;> simp only [nsub, nsave, Nat.reduceDiv] <;> omega
  let ret := keyCopyReturn use256
  let fr := activationOfValues callee.store av ret (av[4].get 64)
  have pre : memcpyPre code fr callee.store := by
    simp only [memcpyPre,fr,activationOfValues,src,dst,count,rsp]
    refine ⟨(hwrite.readable.of_frame widenFrame).of_frame prepareFrame,
      (hDest.of_frame widenFrame).of_frame prepareFrame, Or.inr ?_, ?_⟩
    · rw [ndst, nsrc]; omega
    · apply RangeApart.of_toNat <;> simp only [ndst,nsub] <;> omega
  obtain ⟨out, exec, tag, done, outTyped, outFrame, copied⟩ := callContract_exec_values
    LIR.lifted code .l103f00 LIR.Fn103f00.frameInfo _ _ _
    (memcpy_call code (fun x hx ↦ hcode x (LIR.code_l103f00 x hx)))
    callee.store av ret (av[4].get 64) typed
    (by rw [same39]; exact h39)
    (by rw [same50]; exact h50)
    (by rw [same51]; exact h51)
    ((preserved 22 (by decide)).trans hDF)
    (by rw [rsp]; apply ((hStack.readable.of_frame widenFrame).of_frame prepareFrame).sub <;> omega)
    (by rw [rsp, store]; exact memLoad_memStore_same _ _ _ (by decide) (by decide))
    (by cases use256 <;> decide) (by intro h; contradiction)
    (by change _ + 0 ≤ _; omega) (by rw [rsp,nsub]; omega) (by trivial) pre
  change Atom.All code out.values out.store (LIR.Fn103f00.frameInfo.doneAtoms fr) at done
  rcases done with ⟨o4,o22,o3,_,_,_,_,_,o39,o50,o51,_⟩
  change RamWriteFrame callee.store out.store [fr.region,span fr.rdi fr.rdx.toNat] at outFrame
  have region : fr.region = span (sp - 8) 0 := by
    simp only [fr, Activation.region, activationOfValues, rsp, Nat.sub_self, span]
  rw [region] at outFrame
  simp only [fr,activationOfValues,dst,count] at outFrame
  change ∀ j < fr.rdx.toNat, out.store[fr.rdi + BitVec.ofNat 64 j]? =
    callee.store[fr.rsi + BitVec.ofNat 64 j]? at copied
  simp only [fr, activationOfValues, dst, src, count] at copied
  have srcWords : WordsAt callee.store (sp + wideningOffset use256) 64
      (keys.map Fixslice16.widenWord) := by
    apply widened.of_frame prepareFrame (by decide)
    refine ⟨?_, fun r hr ↦ ?_⟩
    · rw [nsrc]; change _ + 8 * keyWords use256 ≤ _; omega
    · obtain rfl := List.mem_singleton.mp hr
      simp only [span, nsub, nsrc]
      omega
  have frame : RamWriteFrame mem out.store
      [span (sp - 8) 352, span (sp + 344) (8 * keyWords use256),
       span (sp + wideningOffset use256) (8 * keyWords use256)] := by
    refine RamWriteFrame.trans ?_ outFrame ?_
    · refine RamWriteFrame.trans ?_ prepareFrame ?_
      · apply (RamWriteFrame.refl _ _).trans widenFrame
        intro r hr
        obtain rfl := List.mem_singleton.mp hr
        exact ⟨_, by simp, Nat.le_refl _, Nat.le_refl _⟩
      · intro r hr
        obtain rfl := List.mem_singleton.mp hr
        exact ⟨_, by simp, Nat.le_refl _, Nat.le_refl _⟩
    · intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨span (sp - 8) 352, by simp, Nat.le_refl _, by simp [span]⟩
      · exact ⟨_, by simp, Nat.le_refl _, Nat.le_refl _⟩
  have callStep : LIR.program.step (dialect code) ⟨mid,[]⟩ =
      .next ⟨callee,[keyCopyFrame use256]⟩ := by
    change LIR.program.step (dialect code) ⟨⟨mid.label,mid.arguments,mid.store⟩,[]⟩ = _
    rw [midLabel, Program.step, call]; rfl
  have calleeExec : LIR.program.Exec (dialect code) ⟨callee,[]⟩ out := by
    change LIR.program.Exec (dialect code) ⟨⟨callee.label,av,callee.store⟩,[]⟩ out
    rw [label]; exact exec
  have accept : (keyCopyFrame use256).Accepts (dialect code) out.tag = true := by
    rw [tag]
    cases use256 <;> rfl
  let next := (keyCopyFrame use256).resume out
  have values : next.arguments = out.values := CFGCall.resume_arguments (keyCopyFrame use256) out
  refine ⟨next, widen.trans ((Semantics.Reaches.single callStep).trans
    (CFGCall.exec_reaches_resume calleeExec (keyCopyFrame use256) [] accept)), rfl, ?_,
    wordsAt_of_byteCopy srcWords copied, ?_, ?_, frame, ?_, ?_⟩
  · have size : (if use256 then 960 else 704) = 8 * keyWords use256 := by cases use256 <;> rfl
    rw [size]
    exact hDest.readable.of_frame frame
  · rw [values]
    change out.values[4] = ⟨64, sp⟩
    apply o4.trans
    change Value.mk 64 (av[4].get 64 + 8) = _
    rw [rsp, BitVec.sub_add_cancel]
  · rw [values]; exact outTyped
  · intro r hr
    rw [values]
    rcases r with ⟨r,lt⟩
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl
    · exact o3.trans ((typed.value 3).symm.trans (preserved 3 (by decide)))
    · exact o22.trans hDF.symm
    · apply o39.trans
      change Value.mk 32 (av[39].get 32) = _
      rw [same39]; exact h39.symm
    · apply o50.trans
      change Value.mk 16 (av[50].get 16) = _
      rw [same50]; exact h50.symm
    · apply o51.trans
      change Value.mk 16 (av[51].get 16) = _
      rw [same51]; exact h51.symm
  · apply Eq.trans (outFrame.memLoad_eq _) saved
    refine ⟨by rw [nsave]; omega, fun r hr ↦ ?_⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> simp only [span, nsave, nsub, ndst, Nat.reduceDiv] <;> omega

end AesGcm.Proofs.Machine.CTR
