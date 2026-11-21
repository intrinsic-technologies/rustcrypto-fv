import K256.Proofs.ParseSignature.Contract
import K256.Proofs.LIR.Fn127f50.Frame
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Common.Lift.Eval
import X86Proofs.Instructions.Adc.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Adc.Generated.MImm32.Triple
import X86Proofs.Instructions.Adc.Generated.MImm8.Triple
import X86Proofs.Instructions.Adc.Generated.MR.Triple
import X86Proofs.Instructions.Add.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Add.Generated.MImm32.Triple
import X86Proofs.Instructions.Add.Generated.MImm8.Triple
import X86Proofs.Instructions.Add.Generated.MR.Triple
import X86Proofs.Instructions.And.Generated.M8Imm8.Triple
import X86Proofs.Instructions.And.Generated.MImm32.Triple
import X86Proofs.Instructions.And.Generated.MImm8.Triple
import X86Proofs.Instructions.And.Generated.MR.Triple
import X86Proofs.Instructions.Or.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Or.Generated.MImm32.Triple
import X86Proofs.Instructions.Or.Generated.MImm8.Triple
import X86Proofs.Instructions.Or.Generated.MR.Triple
import X86Proofs.Instructions.Sbb.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Sbb.Generated.MImm32.Triple
import X86Proofs.Instructions.Sbb.Generated.MImm8.Triple
import X86Proofs.Instructions.Sbb.Generated.MR.Triple
import X86Proofs.Instructions.Setcc.Generated.M8.Triple
import X86Proofs.Instructions.Shld.Generated.MRCl.Triple
import X86Proofs.Instructions.Shld.Generated.MRImm8.Triple
import X86Proofs.Instructions.Shrd.Generated.MRCl.Triple
import X86Proofs.Instructions.Shrd.Generated.MRImm8.Triple
import X86Proofs.Instructions.Sub.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Sub.Generated.MImm32.Triple
import X86Proofs.Instructions.Sub.Generated.MImm8.Triple
import X86Proofs.Instructions.Sub.Generated.MR.Triple
import X86Proofs.Instructions.Xor.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Xor.Generated.MImm32.Triple
import X86Proofs.Instructions.Xor.Generated.MImm8.Triple
import X86Proofs.Instructions.Xor.Generated.MR.Triple
import K256.Proofs.Common.Lift.Generated.Values.Store2
import K256.Proofs.Common.Refine.Lemma.Store

namespace K256.Proofs.ParseSignature

open K256.Spec K256.Proofs.Common Prelude X86 X86.Machine X86.UserProcess X86Proofs
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine

set_option maxHeartbeats 1200000 in
set_option linter.unusedVariables false in
theorem ctEq_call {code : CodeMap} (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (fr : Activation) (hn : fr.rsi = 4) (hm : fr.rcx = 4)
    (hl : Readable fr.original fr.rdi 32) (hr : Readable fr.original fr.rdx 32) :
    Call code .l127f50 LIR.Fn127f50.frameInfo fr [] fun out =>
      out.store = fr.original ∧
      (out.values[0].get 8 = 1 ↔ ∀ i < 4,
        memLoad fr.original (wordAddr fr.rdi 64 i) 64 =
          memLoad fr.original (wordAddr fr.rdx 64 i) 64) ∧
      (out.values[0].get 8 = 0 ∨ out.values[0].get 8 = 1) := by
  clear hcode
  let CompareRegs := Values Value Reg.count

  let compareRegsPreserved (before after : CompareRegs) : Prop :=
    ∀ i : Fin Reg.count, i.val ∈ [2, 4, 6, 7, 3, 5, 12, 13, 14, 15, 22, 39, 50, 51] →
      after[i] = before[i]

  let equalPrefix (m : Ram) (l r : BitVec 64) (n : Nat) : Prop :=
    ∀ i < n, memLoad m (wordAddr l 64 i) 64 = memLoad m (wordAddr r 64 i) 64

  let compareByte (m : Ram) (l r : BitVec 64) (n : Nat) : BitVec 8 :=
    open Classical in if equalPrefix m l r n then 1 else 0

  have equalPrefix_succ (m : Ram) (l r : BitVec 64) (i : Nat) :
      equalPrefix m l r (i + 1) ↔ equalPrefix m l r i ∧
        memLoad m (wordAddr l 64 i) 64 = memLoad m (wordAddr r 64 i) 64 := by
    constructor
    · intro h
      exact ⟨fun j hj => h j (by omega), h i (by omega)⟩
    · rintro ⟨hp, hw⟩ j hj
      by_cases h : j < i
      · exact hp j h
      · simpa only [show j = i by omega] using hw

  have compareAddr (base : BitVec 64) (i : Nat) :
      base + (BitVec.ofNat 64 i <<< 3) = wordAddr base 64 i := by
    rw [wordAddr, BitVec.shiftLeft_eq_mul_twoPow]
    change base + BitVec.ofNat 64 i * BitVec.ofNat 64 8 = base + BitVec.ofNat 64 (8 * i)
    rw [← BitVec.ofNat_mul, Nat.mul_comm i 8]

  have compareLoad {m : Ram} {base : BitVec 64} {i : Nat}
      (hm : Readable m base 32) (hi : i < 4) : LoadOk m (wordAddr base 64 i) 8 := by
    have hb := hm.low
    have haddr : (wordAddr base 64 i).toNat = base.toNat + 8 * i := by
      simp only [wordAddr, BitVec.toNat_add, BitVec.toNat_ofNat]
      rw [show 64 / 8 = 8 by decide, Nat.mod_eq_of_lt (a := 8 * i) (by omega),
        Nat.mod_eq_of_lt (by omega)]
    exact LoadOk.of_region hm (by rw [haddr]; omega) (by rw [haddr]; omega)

  have compareGet (v : Value) : (v.get 64).setWidth 8 = v.get 8 :=
    BitVec.setWidth_setWidth_of_le v.bits (by decide)

  have compareXor (x y : BitVec 64) :
      (!(xorFlags (x ^^^ y)).ZF.getD false) = true ↔ x ≠ y := by
    simp [xorFlags, BitVec.xor_eq_zero_iff]

  have compareLoopBlock {code : CodeMap} {args : CompareRegs} {mem : Ram}
      {l r : BitVec 64} {i : Nat}
      (hsi : args[6] = ⟨64, 4⟩) (hleft : args[7] = ⟨64, l⟩)
      (hright : args[2] = ⟨64, r⟩) (hi : args[8] = ⟨64, BitVec.ofNat 64 i⟩)
      (hzero : args[1] = ⟨64, 0⟩) (hacc : args[0].get 8 = compareByte mem l r i)
      (hlt : i < 4) (hl : Readable mem l 32) (hr : Readable mem r 32)
      (hwidths : ArgumentWidths args) :
      ∃ next : CompareRegs, LIR.program.runBlock (dialect code) ⟨.l127f70, args, mem⟩ =
        (if i + 1 < 4 then .jump ⟨.l127f70, next, mem⟩ else .jump ⟨.l127f8a, next, mem⟩) ∧
        compareRegsPreserved args next ∧ ArgumentWidths next ∧ next[1] = ⟨64, 0⟩ ∧
        next[8] = ⟨64, BitVec.ofNat 64 (i + 1)⟩ ∧
        next[0].get 8 = compareByte mem l r (i + 1) := by
    have hiBits : args[8].get 64 = BitVec.ofNat 64 i := by rw [hi, Value.get_mk]
    have hnext : args[8].get 64 + 1 = BitVec.ofNat 64 (i + 1) := by
      rw [hiBits, BitVec.ofNat_add]
      rfl
    have hbranch : (!(cmpSpec (args[6].get 64) (args[8].get 64 + 1)).ZF) = true ↔ i + 1 < 4 := by
      simp only [hsi, Value.get_mk, hnext, cmpSpec_ZF, Bool.not_eq_true', beq_eq_false_iff_ne,
        ne_eq, ← BitVec.toNat_inj, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i + 1 < 2^64)]
      change ¬(4 = i + 1) ↔ i + 1 < 4
      omega
    have haddrLeft : args[7].get 64 + (args[8].get 64 <<< 3) = wordAddr l 64 i := by
      rw [hleft, Value.get_mk, hiBits, compareAddr]
    have haddrRight : args[2].get 64 + (args[8].get 64 <<< 3) = wordAddr r 64 i := by
      rw [hright, Value.get_mk, hiBits, compareAddr]
    have hstep (q : Prop) [Decidable q] :
        (if q then 0 else BitVec.setWidth 64 (compareByte mem l r i)).setWidth 8 =
          if q then 0 else compareByte mem l r i := by
      by_cases hq : q
      · rw [ite_eq_left hq, ite_eq_left hq]
        rfl
      · rw [ite_eq_right hq, ite_eq_right hq, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64),
          BitVec.setWidth_eq]
    refine ⟨?loopNext, ?loopEval, ?loopPost⟩
    case loopEval =>
      cfg_eval
      simp only [haddrLeft, haddrRight, compareLoad hl hlt, compareLoad hr hlt, ite_true, hbranch]
      by_cases h : i + 1 < 4 <;> simp only [h, ite_true, ite_false] <;> rfl
    case loopPost =>
      refine ⟨?loopKeep, ?loopWidths, hzero, ?loopIndex, ?loopAcc⟩
      case loopKeep =>
        intro ⟨j, hj⟩ h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
      case loopWidths =>
        intro ⟨j, hj⟩ h
        have hw := hwidths ⟨j, hj⟩ h
        simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact hw | rfl
      case loopIndex =>
        change Value.mk 64 (args[8].get 64 + 1) = _
        rw [hnext]
      case loopAcc =>
        change (if _ then args[1].get 64 else (args[0].get 64 |>.setWidth 8).setWidth 64).setWidth 8 = _
        rw [hzero, Value.get_mk, compareGet, hacc, hstep]
        classical
        unfold compareByte
        simp only [equalPrefix_succ]
        have hx := compareXor (memLoad mem (wordAddr l 64 i) 64) (memLoad mem (wordAddr r 64 i) 64)
        by_cases h : memLoad mem (wordAddr l 64 i) 64 = memLoad mem (wordAddr r 64 i) 64
        · rw [ite_eq_right (fun hc => hx.mp hc h)]
          simp only [and_iff_left h]
        · rw [ite_eq_left (hx.mpr h), ite_eq_right (fun hp => h hp.2)]

  have compareMovOne (v : BitVec 64) : (mergeGPR 16 1 v).setWidth 16 = 1 := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    simp only [mergeGPR, show (16 : Nat) ≠ 32 by decide, ite_false,
      BitVec.getLsbD_setWidth, hj]
    rw [getLsbD_setSlice _ _ _ _ _ (by omega)]
    simp only [Nat.zero_le, decide_true, Nat.zero_add, hj, true_and, Bool.true_and, ite_true, Nat.sub_zero]

  have compareEnter {code : CodeMap} {args : CompareRegs} {mem : Ram}
      (hsi : args[6] = ⟨64, 4⟩) (hcx : args[1] = ⟨64, 4⟩) (hwidths : ArgumentWidths args) :
      ∃ a b c : CompareRegs,
        LIR.program.runBlock (dialect code) ⟨.l127f50, args, mem⟩ = .jump ⟨.l127f55, a, mem⟩ ∧
        LIR.program.runBlock (dialect code) ⟨.l127f55, a, mem⟩ = .jump ⟨.l127f5a, b, mem⟩ ∧
        LIR.program.runBlock (dialect code) ⟨.l127f5a, b, mem⟩ = .jump ⟨.l127f70, c, mem⟩ ∧
        compareRegsPreserved args c ∧ ArgumentWidths c ∧
        c[1] = ⟨64, 0⟩ ∧ c[8] = ⟨64, 0⟩ ∧ c[0].get 8 = 1 := by
    refine ⟨?entryA, ?entryB, ?entryC, ?entryEa, ?entryEb, ?entryEc, ?entryPost⟩
    case entryEa =>
      have hcond : ¬ (!(cmpSpec (args[6].get 64) (args[1].get 64)).ZF) = true := by
        rw [hsi, hcx, Value.get_mk]
        decide +kernel
      cfg_eval
      rw [ite_eq_right hcond]
    case entryEb =>
      have hcond : ¬ (testFlags (args[6].get 64 &&& args[6].get 64)).ZF.getD false = true := by
        rw [hsi, Value.get_mk]
        decide +kernel
      cfg_eval
      rw [ite_eq_right hcond]
    case entryEc =>
      cfg_eval
      rfl
    case entryPost =>
      refine ⟨?entryKeep, ?entryWidths, rfl, rfl, ?entryAcc⟩
      case entryKeep =>
        intro ⟨j, hj⟩ h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
      case entryWidths =>
        intro ⟨j, hj⟩ h
        have hw := hwidths ⟨j, hj⟩ h
        simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact hw | rfl
      case entryAcc =>
        change (mergeGPR 16 1 (args[0].get 64)).setWidth 8 = _
        rw [← BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 16), compareMovOne]
        rfl

  have compareReturn {code : CodeMap} {args : CompareRegs} {mem : Ram}
      {sp ret : BitVec 64} {a : BitVec 8} (hsp : args[4] = ⟨64, sp⟩)
      (hretRead : LoadOk mem sp 8) (hret : memLoad mem sp 64 = ret)
      (hretLow : ret.toNat < 2^32) (hacc : args[0].get 8 = a)
      (hbool : a = 0 ∨ a = 1) (hwidths : ArgumentWidths args) :
      ∃ out, LIR.program.runBlock (dialect code) ⟨.l127f8a, args, mem⟩ = .returned out ∧
        out.store = mem ∧ out.tag = some ⟨64, ret⟩ ∧
        out.values[4] = ⟨64, sp + 8⟩ ∧ out.values[0].get 8 = a ∧ ArgumentWidths out.values ∧
        (∀ i : Fin Reg.count, i.val ∈ [3, 5, 12, 13, 14, 15, 22, 39, 50, 51] →
          out.values[i] = args[i]) := by
    have hspBits : args[4].get 64 = sp := by rw [hsp, Value.get_mk]
    refine ⟨?retOut, ?retEval, ?retPost⟩
    case retEval =>
      cfg_eval
      simp only [hspBits, hretRead, hret, hretLow, and_self, ite_true]
      rfl
    case retPost =>
      refine ⟨rfl, rfl, rfl, ?retAcc, ?retWidths, ?retKeep⟩
      case retAcc =>
        let one := mergeGPR 16 1 (args[2].get 64)
        have h16 : one.setWidth 16 = 1 := compareMovOne _
        have h8 : one.setWidth 8 = 1 := by
          rw [← BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 16), h16]
          rfl
        change (BitVec.setWidth 64 (if (xorFlags
          ((BitVec.setWidth 16 ((args[0].get 64).setWidth 8)) ^^^ one.setWidth 16)).ZF.getD false = true
          then one.setWidth 32 else 0)).setWidth 8 = a
        rw [compareGet, hacc, h16, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64)]
        rcases hbool with rfl | rfl
        · have hf : (xorFlags ((0 : BitVec 8).setWidth 16 ^^^ (1 : BitVec 16))).ZF.getD false ≠ true := by
            decide +kernel
          rw [ite_eq_right hf]
          rfl
        · have ht : (xorFlags ((1 : BitVec 8).setWidth 16 ^^^ (1 : BitVec 16))).ZF.getD false = true := by
            decide +kernel
          rw [ite_eq_left ht, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32), h8]
      case retWidths =>
        intro ⟨j, hj⟩ h
        have hw := hwidths ⟨j, hj⟩ h
        simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact hw | rfl
      case retKeep =>
        intro ⟨j, hj⟩ h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  intro args hentry
  change args[4] = ⟨64, fr.rsp⟩ ∧ args[22] = ⟨1, 0⟩ ∧ args[1] = ⟨64, fr.rcx⟩ ∧
    args[2] = ⟨64, fr.rdx⟩ ∧ args[3] = ⟨64, fr.rbx⟩ ∧ args[5] = ⟨64, fr.rbp⟩ ∧
    args[6] = ⟨64, fr.rsi⟩ ∧ args[7] = ⟨64, fr.rdi⟩ ∧ args[8] = ⟨64, fr.r8⟩ ∧
    args[9] = ⟨64, fr.r9⟩ ∧ args[12] = ⟨64, fr.r12⟩ ∧ args[13] = ⟨64, fr.r13⟩ ∧
    args[14] = ⟨64, fr.r14⟩ ∧ args[15] = ⟨64, fr.r15⟩ ∧ args[39] = ⟨32, fr.mxcsr⟩ ∧
    args[50] = ⟨16, fr.ftw⟩ ∧ args[51] = ⟨16, fr.fcw⟩ ∧
    Readable fr.original fr.rsp 8 ∧ memLoad fr.original fr.rsp 64 = fr.ret ∧
    fr.ret.toNat < 2^32 ∧ fr.low.toNat ≤ fr.rsp.toNat ∧ fr.rsp.toNat % 16 = 8 ∧ True at hentry
  rcases hentry with ⟨hsp, hdf, hcx, hdx, hbx, hbp, hsi, hdi, h8, h9, h12, h13, h14, h15,
    h39, h50, h51, hretRead, hret, hretLow, _, _, _⟩
  rw [hn] at hsi
  rw [hm] at hcx
  have entryWidths : ArgumentWidths args := by
    intro ⟨j, hj⟩ h
    simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl
    · exact congrArg Value.width hdi
    · exact congrArg Value.width hsi
    · exact congrArg Value.width hdx
    · exact congrArg Value.width hcx
    · exact congrArg Value.width h8
    · exact congrArg Value.width h9
  let m := fr.original
  let spec := compareByte m fr.rdi fr.rdx
  let stateAt (i : Nat) (a : CompareRegs) : CFG.State Value Ram LIR.Label (signature (Label := LIR.Label)) Reg.count :=
    if i < 4 then ⟨⟨.l127f70, a, m⟩, []⟩ else ⟨⟨.l127f8a, a, m⟩, []⟩
  have jump {src dst : LIR.Label} {a b : CompareRegs} {out}
      (he : LIR.program.runBlock (dialect code) ⟨src, a, m⟩ = .jump ⟨dst, b, m⟩)
      (ht : LIR.program.Exec (dialect code) ⟨⟨dst, b, m⟩, []⟩ out) :
      LIR.program.Exec (dialect code) ⟨⟨src, a, m⟩, []⟩ out := by
    refine Program.Exec.next ?_ ht
    change (LIR.program.runBlock (dialect code) ⟨src, a, m⟩).next (dialect code) [] = _
    rw [he]
    rfl
  have hbool (i : Nat) : spec i = 0 ∨ spec i = 1 := by
    classical
    dsimp only [spec, compareByte]
    split <;> first | exact Or.inr rfl | exact Or.inl rfl
  let returned (out : Output Value Ram Reg.count) : Prop :=
    out.tag = some ⟨64, fr.ret⟩ ∧
    Atom.All code out.values out.store (LIR.Fn127f50.frameInfo.doneAtoms fr) ∧
    ArgumentWidths out.values ∧ out.store = m ∧ out.values[0].get 8 = spec 4
  have loop (left i : Nat) (a : CompareRegs) (hcount : i + left = 4)
      (hkeep : compareRegsPreserved args a) (hwidths : ArgumentWidths a)
      (hzero : a[1] = ⟨64, 0⟩) (hindex : a[8] = ⟨64, BitVec.ofNat 64 i⟩)
      (hacc : a[0].get 8 = spec i) :
      ∃ out, LIR.program.Exec (dialect code) (stateAt i a) out ∧ returned out := by
    induction left generalizing i a with
    | zero =>
      have h : i = 4 := by omega
      subst i
      obtain ⟨out, he, hmem, htag, hspOut, haccOut, houtWidths, hregs⟩ :=
        compareReturn (code := code) ((hkeep 4 (by decide)).trans hsp)
          ⟨hretRead.low, hretRead.present⟩ hret hretLow hacc (hbool 4) hwidths
      have hkeepOut (j : Fin Reg.count)
          (hj : j.val ∈ [3, 5, 12, 13, 14, 15, 22, 39, 50, 51]) :
          out.values[j] = args[j] :=
        (hregs j hj).trans (hkeep j (List.mem_append_right [2, 4, 6, 7] hj))
      refine ⟨out, ?_, htag, ?_, houtWidths, hmem, haccOut⟩
      · dsimp only [stateAt]
        rw [ite_eq_right (by omega : ¬ 4 < 4)]
        apply Program.Exec.done
        change (LIR.program.runBlock (dialect code) ⟨.l127f8a, a, m⟩).next (dialect code) [] = _
        rw [he]
        rfl
      · change out.values[4] = ⟨64, fr.rsp + 8⟩ ∧ out.values[22] = ⟨1, 0⟩ ∧
          out.values[3] = ⟨64, fr.rbx⟩ ∧ out.values[5] = ⟨64, fr.rbp⟩ ∧
          out.values[12] = ⟨64, fr.r12⟩ ∧ out.values[13] = ⟨64, fr.r13⟩ ∧
          out.values[14] = ⟨64, fr.r14⟩ ∧ out.values[15] = ⟨64, fr.r15⟩ ∧
          out.values[39] = ⟨32, fr.mxcsr⟩ ∧ out.values[50] = ⟨16, fr.ftw⟩ ∧
          out.values[51] = ⟨16, fr.fcw⟩ ∧ True
        exact ⟨hspOut, (hkeepOut 22 (by decide)).trans hdf,
          (hkeepOut 3 (by decide)).trans hbx, (hkeepOut 5 (by decide)).trans hbp,
          (hkeepOut 12 (by decide)).trans h12, (hkeepOut 13 (by decide)).trans h13,
          (hkeepOut 14 (by decide)).trans h14, (hkeepOut 15 (by decide)).trans h15,
          (hkeepOut 39 (by decide)).trans h39, (hkeepOut 50 (by decide)).trans h50,
          (hkeepOut 51 (by decide)).trans h51, trivial⟩
    | succ left ih =>
      have hi : i < 4 := by omega
      obtain ⟨next, he, hkeepNext, hwidthsNext, hzeroNext, hindexNext, haccNext⟩ :=
        compareLoopBlock (code := code) ((hkeep 6 (by decide)).trans hsi)
          ((hkeep 7 (by decide)).trans hdi) ((hkeep 2 (by decide)).trans hdx)
          hindex hzero hacc hi hl hr hwidths
      obtain ⟨out, hexec, hp⟩ := ih (i + 1) next (by omega)
        (fun j hj => (hkeepNext j hj).trans (hkeep j hj)) hwidthsNext hzeroNext hindexNext haccNext
      refine ⟨out, ?_, hp⟩
      dsimp only [stateAt]
      rw [ite_eq_left hi]
      by_cases h : i + 1 < 4
      · rw [ite_eq_left h] at he
        dsimp only [stateAt] at hexec
        rw [ite_eq_left h] at hexec
        exact jump he hexec
      · rw [ite_eq_right h] at he
        dsimp only [stateAt] at hexec
        rw [ite_eq_right h] at hexec
        exact jump he hexec
  obtain ⟨a, b, c, ea, eb, ec, hkeep, hwidths, hzero, hindex, hacc⟩ :=
    compareEnter (code := code) (mem := m) hsi hcx entryWidths
  have hbase : spec 0 = 1 := by
    classical
    exact ite_eq_left (fun i hi => (Nat.not_lt_zero i hi).elim)
  obtain ⟨out, hexec, htag, hdone, houtWidths, hmem, hbyte⟩ :=
    loop 4 0 c rfl hkeep hwidths hzero hindex (hacc.trans hbase.symm)
  dsimp only [stateAt] at hexec
  rw [ite_eq_left (by decide : 0 < 4)] at hexec
  have hframe : RamWriteFrame m out.store [fr.region] := by
    rw [hmem]
    exact RamWriteFrame.refl _ _
  refine ⟨out, jump ea (jump eb (jump ec hexec)), htag, hdone, hframe, houtWidths, hmem, ?_, hbyte ▸ hbool 4⟩
  rw [hbyte]
  change spec 4 = 1 ↔ equalPrefix m fr.rdi fr.rdx 4
  classical
  dsimp only [spec, compareByte]
  have hne : (0 : BitVec 8) ≠ 1 := by decide +kernel
  split <;> rename_i h <;> simp only [h, hne]

end K256.Proofs.ParseSignature
