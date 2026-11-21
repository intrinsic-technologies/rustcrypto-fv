import K256.Proofs.Verify.Core.Memory
import K256.Proofs.Verify.LIR.Generated.Values
import K256.Proofs.Generate.Generator.Sample.Calls
import K256.Proofs.Generate.Serialize.Transfer.Blocks
import K256.Proofs.Verify.Choice
import K256.Proofs.Sec1.Serialize.Choice
import K256.Proofs.Generate.Generator.Multiply.Split.WideProduct
import K256.Proofs.ParseSignature.Call

namespace K256.Proofs.Verify.Core

open K256.Spec.Program Prelude X86.Machine X86Proofs K256.Proofs.Lift K256.Proofs.Refine
  Standards.SECG.ECC
open X86 X86.UserProcess K256.Proofs.CFG K256.Proofs.Verify.LIR
open Generate.Generator.Multiply (scalarWords)

private def keptRegs (a b : Registers) : Prop :=
  ∀ i : Fin Reg.count, i.val ∈ [3, 5, 22, 39, 50, 51] → b[i] = a[i]

private theorem keptRegs.trans {a b c : Registers} (ab : keptRegs a b) (bc : keptRegs b c) :
    keptRegs a c := fun i hi => (bc i hi).trans (ab i hi)

local macro "kept_registers" : tactic => `(tactic|
  (intro ⟨i, bound⟩ h
   simp only [List.mem_cons, List.not_mem_nil, or_false] at h
   rcases h with h | h | h | h | h | h <;> subst i <;> rfl))

set_option maxHeartbeats 1200000 in
private theorem compareWords {code : CodeMap} (args : Registers) (m : Ram)
    {sp ret left right : BitVec 64}
    (hsp : args[4] = ⟨64, sp⟩) (hdi : args[7] = ⟨64, left⟩) (hdx : args[2] = ⟨64, right⟩)
    (hsi : args[6] = ⟨64, 4⟩) (hcx : args[1] = ⟨64, 4⟩)
    (hretRead : Readable m sp 8) (hret : memLoad m sp 64 = ret) (hretLow : ret.toNat < 2^32)
    (hl : Readable m left 32) (hr : Readable m right 32) :
    ∃ out, Generate.LIR.program.Exec (dialect code) ⟨⟨.l127f50, args, m⟩, []⟩ out ∧
      out.tag = some ⟨64, ret⟩ ∧ out.values[4] = ⟨64, sp + 8⟩ ∧ keptRegs args out.values ∧
      out.store = m ∧
      (out.values[0].get 8 = 1 ↔ ∀ i < 4, memLoad m (wordAddr left 64 i) 64 = memLoad m (wordAddr right 64 i) 64) ∧
      (out.values[0].get 8 = 0 ∨ out.values[0].get 8 = 1) := by
  let compareRegsPreserved (before after : Registers) : Prop :=
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

  have compareLoopBlock {code : CodeMap} {args : Registers} {mem : Ram}
      {l r : BitVec 64} {i : Nat}
      (hsi : args[6] = ⟨64, 4⟩) (hleft : args[7] = ⟨64, l⟩)
      (hright : args[2] = ⟨64, r⟩) (hi : args[8] = ⟨64, BitVec.ofNat 64 i⟩)
      (hzero : args[1] = ⟨64, 0⟩) (hacc : args[0].get 8 = compareByte mem l r i)
      (hlt : i < 4) (hl : Readable mem l 32) (hr : Readable mem r 32)
      :
      ∃ next : Registers, Generate.LIR.program.runBlock (dialect code) ⟨.l127f70, args, mem⟩ =
        (if i + 1 < 4 then .jump ⟨.l127f70, next, mem⟩ else .jump ⟨.l127f8a, next, mem⟩) ∧
        compareRegsPreserved args next ∧ next[1] = ⟨64, 0⟩ ∧
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
      refine ⟨?loopKeep, hzero, ?loopIndex, ?loopAcc⟩
      case loopKeep =>
        intro ⟨j, hj⟩ h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
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

  have compareEnter {code : CodeMap} {args : Registers} {mem : Ram}
      (hsi : args[6] = ⟨64, 4⟩) (hcx : args[1] = ⟨64, 4⟩) :
      ∃ a b c : Registers,
        Generate.LIR.program.runBlock (dialect code) ⟨.l127f50, args, mem⟩ = .jump ⟨.l127f55, a, mem⟩ ∧
        Generate.LIR.program.runBlock (dialect code) ⟨.l127f55, a, mem⟩ = .jump ⟨.l127f5a, b, mem⟩ ∧
        Generate.LIR.program.runBlock (dialect code) ⟨.l127f5a, b, mem⟩ = .jump ⟨.l127f70, c, mem⟩ ∧
        compareRegsPreserved args c ∧
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
      refine ⟨?entryKeep, rfl, rfl, ?entryAcc⟩
      case entryKeep =>
        intro ⟨j, hj⟩ h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
      case entryAcc =>
        change (mergeGPR 16 1 (args[0].get 64)).setWidth 8 = _
        rw [← BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 16), compareMovOne]
        rfl

  have compareReturn {code : CodeMap} {args : Registers} {mem : Ram}
      {sp ret : BitVec 64} {a : BitVec 8} (hsp : args[4] = ⟨64, sp⟩)
      (hretRead : LoadOk mem sp 8) (hret : memLoad mem sp 64 = ret)
      (hretLow : ret.toNat < 2^32) (hacc : args[0].get 8 = a)
      (hbool : a = 0 ∨ a = 1) :
      ∃ out, Generate.LIR.program.runBlock (dialect code) ⟨.l127f8a, args, mem⟩ = .returned out ∧
        out.store = mem ∧ out.tag = some ⟨64, ret⟩ ∧
        out.values[4] = ⟨64, sp + 8⟩ ∧ out.values[0].get 8 = a ∧
        (∀ i : Fin Reg.count, i.val ∈ [3, 5, 12, 13, 14, 15, 22, 39, 50, 51] →
          out.values[i] = args[i]) := by
    have hspBits : args[4].get 64 = sp := by rw [hsp, Value.get_mk]
    refine ⟨?retOut, ?retEval, ?retPost⟩
    case retEval =>
      cfg_eval
      simp only [hspBits, hretRead, hret, hretLow, and_self, ite_true]
      rfl
    case retPost =>
      refine ⟨rfl, rfl, rfl, ?retAcc, ?retKeep⟩
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
      case retKeep =>
        intro ⟨j, hj⟩ h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  let spec := compareByte m left right
  let stateAt (i : Nat) (a : Registers) : CFG.State Value Ram Generate.LIR.Label (signature (Label := Generate.LIR.Label)) Reg.count :=
    if i < 4 then ⟨⟨.l127f70, a, m⟩, []⟩ else ⟨⟨.l127f8a, a, m⟩, []⟩
  have jump {src dst : Generate.LIR.Label} {a b : Registers} {out}
      (he : Generate.LIR.program.runBlock (dialect code) ⟨src, a, m⟩ = .jump ⟨dst, b, m⟩)
      (ht : Generate.LIR.program.Exec (dialect code) ⟨⟨dst, b, m⟩, []⟩ out) :
      Generate.LIR.program.Exec (dialect code) ⟨⟨src, a, m⟩, []⟩ out := by
    refine Program.Exec.next ?_ ht
    change (Generate.LIR.program.runBlock (dialect code) ⟨src, a, m⟩).next (dialect code) [] = _
    rw [he]
    rfl
  have hbool (i : Nat) : spec i = 0 ∨ spec i = 1 := by
    classical
    dsimp only [spec, compareByte]
    split <;> first | exact Or.inr rfl | exact Or.inl rfl
  let returned (out : Output Value Ram Reg.count) : Prop :=
    out.tag = some ⟨64, ret⟩ ∧
    out.values[4] = ⟨64, sp + 8⟩ ∧ keptRegs args out.values ∧
    out.store = m ∧ out.values[0].get 8 = spec 4
  have loop (remaining i : Nat) (a : Registers) (hcount : i + remaining = 4)
      (hkeep : compareRegsPreserved args a)
      (hzero : a[1] = ⟨64, 0⟩) (hindex : a[8] = ⟨64, BitVec.ofNat 64 i⟩)
      (hacc : a[0].get 8 = spec i) :
      ∃ out, Generate.LIR.program.Exec (dialect code) (stateAt i a) out ∧ returned out := by
    induction remaining generalizing i a with
    | zero =>
      have h : i = 4 := by omega
      subst i
      obtain ⟨out, he, hmem, htag, hspOut, haccOut, hregs⟩ :=
        compareReturn (code := code) ((hkeep 4 (by decide)).trans hsp)
          ⟨hretRead.low, hretRead.present⟩ hret hretLow hacc (hbool 4)
      have hkeepOut (j : Fin Reg.count)
          (hj : j.val ∈ [3, 5, 12, 13, 14, 15, 22, 39, 50, 51]) :
          out.values[j] = args[j] :=
        (hregs j hj).trans (hkeep j (List.mem_append_right [2, 4, 6, 7] hj))
      refine ⟨out, ?_, htag, hspOut, ?_, hmem, haccOut⟩
      · dsimp only [stateAt]
        rw [ite_eq_right (by omega : ¬ 4 < 4)]
        apply Program.Exec.done
        change (Generate.LIR.program.runBlock (dialect code) ⟨.l127f8a, a, m⟩).next (dialect code) [] = _
        rw [he]
        rfl
      · intro j hj
        apply hkeepOut j
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hj ⊢
        omega
    | succ left ih =>
      have hi : i < 4 := by omega
      obtain ⟨next, he, hkeepNext, hzeroNext, hindexNext, haccNext⟩ :=
        compareLoopBlock (code := code) ((hkeep 6 (by decide)).trans hsi)
          ((hkeep 7 (by decide)).trans hdi) ((hkeep 2 (by decide)).trans hdx)
          hindex hzero hacc hi hl hr
      obtain ⟨out, hexec, hp⟩ := ih (i + 1) next (by omega)
        (fun j hj => (hkeepNext j hj).trans (hkeep j hj)) hzeroNext hindexNext haccNext
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
  obtain ⟨a, b, c, ea, eb, ec, hkeep, hzero, hindex, hacc⟩ :=
    compareEnter (code := code) (mem := m) hsi hcx
  have hbase : spec 0 = 1 := by
    classical
    exact ite_eq_left (fun i hi => (Nat.not_lt_zero i hi).elim)
  obtain ⟨out, hexec, htag, hspOut, hkeepOut, hmem, hbyte⟩ :=
    loop 4 0 c rfl hkeep hzero hindex (hacc.trans hbase.symm)
  dsimp only [stateAt] at hexec
  rw [ite_eq_left (by decide : 0 < 4)] at hexec
  refine ⟨out, jump ea (jump eb (jump ec hexec)), htag, hspOut, hkeepOut, hmem, ?_, hbyte ▸ hbool 4⟩
  rw [hbyte]
  change spec 4 = 1 ↔ equalPrefix m left right 4
  classical
  dsimp only [spec, compareByte]
  have hne : (0 : BitVec 8) ≠ 1 := by decide +kernel
  split <;> rename_i h <;> simp only [h, hne]


private abbrev comparisonReturn (label : Label) (pc : BitVec 64) :
    StackFrame Value Label signature Reg.count :=
  ⟨label, #v[], rfl, some ⟨64, pc⟩⟩

private theorem compareCall {b : Registers} {m : Ram} {sp : BitVec 64}
    (rsp : b[4].get 64 = sp) (ptr : b[14].get 64 = sp + 136)
    (write : StoreOk Extracted.programImage m (sp-8) 8 0x105362 5) :
    ∃ c, program.runBlock (dialect Extracted.programImage) ⟨.l105357,b,m⟩ =
      .call ⟨.l10a2a0,c,memStore m (sp-8) (0x105367 : BitVec 64)⟩
        (comparisonReturn .l105367 0x105367) ∧
      c[4] = ⟨64,sp-8⟩ ∧ c[6] = ⟨64,sp+136⟩ ∧ c[7] = ⟨64,sp+256⟩ ∧ keptRegs b c := by
  refine ⟨?_, ?step, ?post⟩
  case step =>
    cfg_eval [rsp, ptr, write]
    rfl
  case post => exact ⟨rfl, rfl, rfl, by kept_registers⟩

private theorem compareEntry {a : Registers} {m : Ram} {sp l r : BitVec 64}
    (rsp : a[4].get 64 = sp) (si : a[6].get 64 = r) (di : a[7] = ⟨64,l⟩)
    (push : StoreOk Extracted.programImage m (sp-8) 8 0x10a2a0 1)
    (call : StoreOk Extracted.programImage (memStore m (sp-8) (a[0].get 64)) (sp-16) 8 0x10a2ae 5) :
    ∃ b, program.runBlock (dialect Extracted.programImage) ⟨.l10a2a0,a,m⟩ =
      .call ⟨.l127f50,b,memStore (memStore m (sp-8) (a[0].get 64)) (sp-16) (0x10a2b3 : BitVec 64)⟩
        (comparisonReturn .l10a2b3 0x10a2b3) ∧
      b[4] = ⟨64,sp-16⟩ ∧ b[7] = ⟨64,l⟩ ∧ b[2] = ⟨64,r⟩ ∧
      b[6] = ⟨64,4⟩ ∧ b[1] = ⟨64,4⟩ ∧ keptRegs a b := by
  refine ⟨?_, ?step, ?post⟩
  case step =>
    have sub : sp-8-8 = sp-16 := by bv_omega
    cfg_eval [rsp, si, push, sub, call]
    rfl
  case post => exact ⟨rfl, di, rfl, rfl, rfl, by kept_registers⟩

private theorem compareChoice {a : Registers} {m : Ram} {sp : BitVec 64} {v : BitVec 8}
    (rsp : a[4].get 64 = sp) (low : a[0].get 8 = v) (binary : v = 0 ∨ v = 1)
    (write : StoreOk Extracted.programImage m (sp-8) 8 0x10a2b8 5) :
    ∃ b, program.runBlock (dialect Extracted.programImage) ⟨.l10a2b3,a,m⟩ =
      .call ⟨.l127d50,b,memStore m (sp-8) (0x10a2bd : BitVec 64)⟩
        (comparisonReturn .l10a2bd 0x10a2bd) ∧
      b[4] = ⟨64,sp-8⟩ ∧ b[7].get 64 = v.setWidth 64 ∧ keptRegs a b := by
  refine ⟨?_, ?step, ?post⟩
  case step =>
    cfg_eval [rsp, write]
    rfl
  case post =>
    refine ⟨rfl, ?_, by kept_registers⟩
    have same : (a[0].get 64).setWidth 8 = v :=
      (BitVec.setWidth_setWidth_of_le _ (by decide)).trans low
    change ((mergeGPR 8 _ (a[0].get 64)).setWidth 8).setWidth 64 = v.setWidth 64
    rw [setWidth_mergeGPR8, same]
    rcases binary with rfl | rfl <;> rfl

private theorem choiceExec {a : Registers} {m : Ram} {sp ret : BitVec 64} {v : BitVec 8}
    (rsp : a[4].get 64 = sp) (di : a[7].get 64 = v.setWidth 64)
    (slot : Writable Extracted.programImage m (sp-1) 1) (address : Readable m sp 8)
    (saved : memLoad m sp 64 = ret) (small : ret.toNat < 2^32) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l127d50,a,m⟩,[]⟩ out ∧
      out.tag = some ⟨64,ret⟩ ∧ out.values[4] = ⟨64,sp+8⟩ ∧
      out.values[0].get 8 = v ∧ keptRegs a out.values ∧
      RamWriteFrame m out.store [⟨(sp-1).toNat, 1⟩] := by
  obtain ⟨out, step, tag, stack, flag, frame, kept⟩ := Sec1.Serialize.choiceBlock
    (fun w hw => Common.fnCode_subset_programImage w (Sec1.LIR.code_l127d50 w hw))
    rsp slot address (saved ▸ small)
  have sec : Sec1.LIR.program.Exec (dialect Extracted.programImage) ⟨⟨.l127d50,a,m⟩,[]⟩ out :=
    .done (by simp only [Program.step, step, CFG.Transfer.next])
  have gen : Generate.LIR.program.Exec (dialect Extracted.programImage) ⟨⟨.l127d50,a,m⟩,[]⟩ out :=
    Generate.Serialize.Relabel.exec Generate.Serialize.matches_blocks sec rfl
  refine ⟨out, K256.Proofs.Verify.Transfer.compareExec rfl gen, saved ▸ tag, stack, ?_, ?_, frame⟩
  · rw [flag]
    change (((a[7].get 64).setWidth 8).setWidth 64).setWidth 8 = v
    rw [di]
    simp
  · intro i hi
    apply kept i
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
    omega

private theorem compareReturn {a : Registers} {m : Ram} {sp ret : BitVec 64} {v : BitVec 8}
    (rsp : a[4].get 64 = sp-16) (byte : a[0].get 8 = v) (binary : v = 0 ∨ v = 1)
    (pop : LoadOk m (sp-16) 8) (read : LoadOk m (sp-8) 8)
    (addr : memLoad m (sp-8) 64 = ret) (small : ret.toNat < 2^32) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l10a2bd,a,m⟩,[]⟩ out ∧
      out.tag = some ⟨64,ret⟩ ∧ out.values[4] = ⟨64,sp⟩ ∧
      out.values[0].get 8 = v ∧ keptRegs a out.values ∧ out.store = m := by
  have same : (a[0].get 64).setWidth 8 = v :=
    (BitVec.setWidth_setWidth_of_le _ (by decide)).trans byte
  have afterPop : sp-16+8 = sp-8 := by bv_omega
  have afterRet : sp-8+8 = sp := by bv_omega
  have test (x : BitVec 8) : (testFlags (x &&& x)).ZF.getD false = (x == 0) := by
    simp only [testFlags, BitVec.and_self, Option.getD_some]
  rcases binary with rfl | rfl
  all_goals
    refine ⟨?_, .done ?step, ?post⟩
    case step =>
      change program.step _ _ = _
      cfg_eval [rsp, same, test, pop, read, addr, small, afterPop, afterRet]
      rfl
    case post =>
      refine ⟨rfl, rfl, ?_, by kept_registers, rfl⟩
      change (mergeGPR 8 _ (a[0].get 64)).setWidth 8 = _
      rw [setWidth_mergeGPR8]
      decide +kernel

private theorem compareBranch {a : Registers} {m : Ram} {v : BitVec 8}
    (byte : a[0].get 8 = v) (binary : v = 0 ∨ v = 1) :
    ∃ b, Reaches .l105367 a m (if v = 1 then .l10536b else .l10536f) b m ∧
      b[4] = a[4] ∧ keptRegs a b := by
  have same : (a[0].get 64).setWidth 8 = v :=
    (BitVec.setWidth_setWidth_of_le _ (by decide)).trans byte
  rcases binary with rfl | rfl
  all_goals
    refine ⟨?_, Semantics.Reaches.single ?step, ?post⟩
    case step =>
      change program.step _ _ = _
      cfg_eval [same]
      rfl
    case post => exact ⟨rfl, by kept_registers⟩

private theorem resumeComparison (label : Label) (pc : BitVec 64) (out : Output Value Ram Reg.count) :
    (comparisonReturn label pc).resume out = ⟨label, out.values, out.store⟩ := by
  change Location.mk label ((comparisonReturn label pc).resume out).arguments out.store = _
  rw [ParseSignature.resume_arguments]

private theorem stackAfterChoice (sp : BitVec 64) : sp - 24 + 8 = sp - 16 := by
  bv_omega

theorem compareScalars {fr : Activation} {a b : Registers} {p : Curve.Point}
    {digest : ByteArray} {r s x : Nat} {m : Ram} (e : Entry fr a p digest r s)
    (h : Phase fr b m) (ptr : b[14] = ⟨64, localSp fr + 136⟩)
    (hx : WordsAt m (localSp fr + 136) 64 (scalarWords x))
    (hr : WordsAt m (localSp fr + 256) 64 (scalarWords r))
    (bound : x < 2^256) :
    ∃ c n, Reaches .l105357 b m (if x = r then .l10536b else .l10536f) c n ∧ Phase fr c n := by
  let sp := localSp fr
  let scratch : MemoryRegion := ⟨sp.toNat - 25, 25⟩
  have room := e.stackRoom
  have low := e.low
  have base := e.low_toNat
  have spNat : sp.toNat = fr.rsp.toNat - 488 :=
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by change 488 ≤ fr.rsp.toNat; omega))
  have subNat (off : BitVec 64) (fit : off.toNat ≤ 25) :
      (sp-off).toNat = sp.toNat - off.toNat :=
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))
  have within {off : BitVec 64} {len : Nat} (fit : off.toNat ≤ 25) (endBefore : len ≤ off.toNat) :
      InRegions [scratch] (sp-off) len := by
    refine ⟨scratch, List.mem_singleton_self _, ?_⟩
    simp only [InRegion, scratch, subNat off fit]
    omega
  have inside : RegionsWithin [scratch] [fr.region] := by
    intro reg hreg
    obtain rfl := List.mem_singleton.mp hreg
    refine ⟨fr.region, List.mem_singleton_self _, ?_⟩
    simp only [Activation.region, scratch, base, spNat]
    omega
  have stackAt {addr offset : BitVec 64} {len : Nat} (eq : addr = fr.rsp + offset)
      (fit : (offset - (0 - 12456)).toNat + len ≤ 12456) :
      Writable Extracted.programImage m addr len :=
    (e.stack.of_frame h.frame).of_offsets eq (e.stackBase.trans (addr_sub _ _)) fit
  have scratchWrite : Writable Extracted.programImage m (sp - 25) 25 :=
    stackAt (offset := -513) (by dsimp only [sp, localSp]; bv_omega) (by decide)
  have writable {off : BitVec 64} {len : Nat}
      (fit : (0-off-(0-25)).toNat + len ≤ 25) : Writable Extracted.programImage m (sp-off) len :=
    scratchWrite.of_offsets (addr_sub sp off) (addr_sub sp 25) fit
  have left : Readable m (sp + 256) 32 :=
    (stackAt (offset := -232) (len := 32) (by dsimp only [sp, localSp]; bv_omega) (by decide)).readable
  have right : Readable m (sp + 136) 32 :=
    (stackAt (offset := -352) (len := 32) (by dsimp only [sp, localSp]; bv_omega) (by decide)).readable
  have outerWrite : StoreOk Extracted.programImage m (sp-8) 8 0x105362 5 :=
    ParseSignature.storeOk_of_codeRange (off := 11) (writable (by decide))
      (fun v hv => Common.fnCode_subset_programImage v (code_l105357 v hv)) (by decide)
  obtain ⟨ca, outerCall, caSp, caSi, caDi, keepOuter⟩ :=
    compareCall (sp := sp) (congrArg (Value.get 64) h.sp) (congrArg (Value.get 64) ptr) outerWrite
  let outer := memStore m (sp-8) (0x105367 : BitVec 64)
  let pushed := memStore outer (sp-16) (ca[0].get 64)
  let compared := memStore pushed (sp-24) (0x10a2b3 : BitVec 64)
  let boxed := memStore compared (sp-24) (0x10a2bd : BitVec 64)
  have outerFrame : RamWriteFrame m outer [scratch] :=
    (RamWriteFrame.refl _ _).memStore _ (within (by decide) (by decide))
  have pushedFrame : RamWriteFrame m pushed [scratch] :=
    outerFrame.memStore _ (within (by decide) (by decide))
  have spSub16 : sp-8-8 = sp-16 := by bv_omega
  have spSub24 : sp-8-16 = sp-24 := by bv_omega
  have pushWrite : StoreOk Extracted.programImage outer (sp-16) 8 0x10a2a0 1 :=
    ParseSignature.storeOk_of_codeRange (off := 0) ((writable (by decide)).of_frame outerFrame)
      (fun v hv => Common.fnCode_subset_programImage v (code_l10a2a0 v hv)) (by decide)
  have innerWrite : StoreOk Extracted.programImage pushed (sp-24) 8 0x10a2ae 5 :=
    ParseSignature.storeOk_of_codeRange (off := 14) ((writable (by decide)).of_frame pushedFrame)
      (fun v hv => Common.fnCode_subset_programImage v (code_l10a2a0 v hv)) (by decide)
  obtain ⟨eqArgs, innerCall, eqSp, eqDi, eqDx, eqSi, eqCx, keepInner⟩ :=
    compareEntry (sp := sp-8) (l := sp+256) (r := sp+136) (m := outer) (congrArg (Value.get 64) caSp) (congrArg (Value.get 64) caSi) caDi
      (by rw [spSub16]; exact pushWrite)
      (by rw [spSub16, spSub24]; exact innerWrite)
  rw [spSub16, spSub24] at innerCall
  rw [spSub24] at eqSp
  have compFrame : RamWriteFrame m compared [scratch] :=
    pushedFrame.memStore _ (within (by decide) (by decide))
  have eqReadable : Readable compared (sp-24) 8 := (writable (by decide)).readable.of_frame compFrame
  have eqReturnWord : memLoad compared (sp-24) 64 = 0x10a2b3 :=
    memLoad_memStore_same pushed (sp-24) (0x10a2b3 : BitVec 64) (by decide) (by decide)
  obtain ⟨result, resultGen, resultTag, resultSp, keepResult, resultMem, resultEq, binary⟩ :=
    compareWords (code := Extracted.programImage) (sp := sp-24) (ret := 0x10a2b3) (left := sp+256) (right := sp+136) eqArgs compared eqSp eqDi eqDx eqSi eqCx eqReadable
      eqReturnWord (by decide)
      (left.of_frame compFrame) (right.of_frame compFrame)
  have resultExec := K256.Proofs.Verify.Transfer.compareExec (dst := .l127f50) rfl resultGen
  let v := result.values[0].get 8
  have resultStack : result.values[4].get 64 = sp-16 :=
    (congrArg (Value.get 64) resultSp).trans (stackAfterChoice sp)
  have spBox : sp-16-8 = sp-24 := BitVec.sub_sub ..
  have boxWrite : StoreOk Extracted.programImage result.store (sp-24) 8 0x10a2b8 5 := by
    rw [resultMem]
    exact ParseSignature.storeOk_of_codeRange (off := 5) ((writable (by decide)).of_frame compFrame)
      (fun w hw => Common.fnCode_subset_programImage w (code_l10a2b3 w hw)) (by decide)
  obtain ⟨boxArgs, choiceCall, boxSp, boxDi, keepBox⟩ :=
    compareChoice (sp := sp-16) resultStack (v := v) rfl binary (by rw [spBox]; exact boxWrite)
  rw [spBox, resultMem] at choiceCall
  rw [spBox] at boxSp
  have boxedFrame : RamWriteFrame m boxed [scratch] :=
    compFrame.memStore _ (within (by decide) (by decide))
  have boxByte : sp-24-1 = sp-25 := BitVec.sub_sub ..
  have byteSlot : Writable Extracted.programImage boxed (sp-24-1) 1 := by
    rw [boxByte]
    exact (writable (by decide)).of_frame boxedFrame
  have boxReturnWord : memLoad boxed (sp-24) 64 = 0x10a2bd :=
    memLoad_memStore_same compared (sp-24) (0x10a2bd : BitVec 64) (by decide) (by decide)
  obtain ⟨chosen, chosenExec, chosenTag, chosenSp, chosenByte, keepChosen, choiceFrame⟩ :=
    choiceExec (sp := sp-24) (ret := 0x10a2bd) (congrArg (Value.get 64) boxSp) boxDi byteSlot
      ((writable (off := 24) (len := 8) (by decide)).readable.of_frame boxedFrame)
      boxReturnWord (by decide)
  have chosenFrame : RamWriteFrame m chosen.store [scratch] := by
    apply boxedFrame.trans choiceFrame
    intro reg hreg
    obtain rfl := List.mem_singleton.mp hreg
    refine ⟨scratch, List.mem_singleton_self _, ?_⟩
    change sp.toNat - 25 ≤ (sp-24-1).toNat ∧ (sp-24-1).toNat + 1 ≤ sp.toNat - 25 + 25
    rw [boxByte, subNat 25 (by decide)]
    change sp.toNat - 25 ≤ sp.toNat - 25 ∧ sp.toNat - 25 + 1 ≤ sp.toNat - 25 + 25
    omega
  have chosenStack : chosen.values[4].get 64 = sp-16 :=
    (congrArg (Value.get 64) chosenSp).trans (stackAfterChoice sp)
  have load {off : BitVec 64} (fit : (0-off-(0-25)).toNat + 8 ≤ 25) :
      LoadOk chosen.store (sp-off) 8 :=
    let rd := (writable fit).readable.of_frame chosenFrame
    ⟨rd.low, rd.present⟩
  have outerAddress : memLoad chosen.store (sp-8) 64 = 0x105367 := by
    have returnApart : Outside [⟨(sp-24-1).toNat, 1⟩] (sp-8) 8 := by
      refine ⟨?_, fun reg hreg => ?_⟩
      · rw [subNat 8 (by decide)]
        change sp.toNat - 8 + 8 ≤ 2^64
        omega
      obtain rfl := List.mem_singleton.mp hreg
      right
      change (sp-24-1).toNat + 1 ≤ (sp-8).toNat
      rw [boxByte, subNat 25 (by decide), subNat 8 (by decide)]
      change sp.toNat - 25 + 1 ≤ sp.toNat - 8
      omega
    rw [choiceFrame.memLoad_eq returnApart]
    dsimp only [boxed, compared, pushed]
    rw [memLoad_memStore_of_rangeApart, memLoad_memStore_of_rangeApart,
      memLoad_memStore_of_rangeApart]
    · exact memLoad_memStore_same m (sp-8) (0x105367 : BitVec 64) (by decide) (by decide)
    · exact RangeApart.of_offsets (addr_sub sp 16) (addr_sub sp 8) (by decide)
    · exact RangeApart.of_offsets (addr_sub sp 24) (addr_sub sp 8) (by decide)
    · exact RangeApart.of_offsets (addr_sub sp 24) (addr_sub sp 8) (by decide)
  obtain ⟨out, returnExec, returnTag, returnSp, returnByte, keepReturn, returnMem⟩ :=
    compareReturn (sp := sp) chosenStack chosenByte binary (load (by decide)) (load (by decide))
      outerAddress (by decide)
  obtain ⟨c, branch, branchSp, keepBranch⟩ :=
    compareBranch (m := out.store) returnByte binary
  have afterScratch {d : BitVec 64} (dsmall : d.toNat ≤ 256) :
      Outside [scratch] (sp+d) 32 := by
    have asNat : (sp+d).toNat = sp.toNat + d.toNat := by
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt (by omega)]
    refine ⟨by rw [asNat]; omega, fun reg hreg => ?_⟩
    obtain rfl := List.mem_singleton.mp hreg
    right
    rw [asNat]
    change sp.toNat - 25 + 25 ≤ _
    omega
  have leftWords := hr.of_frame compFrame (by decide) (afterScratch (d := 256) (by decide))
  have rightWords := hx.of_frame compFrame (by decide) (afterScratch (d := 136) (by decide))
  have resultIff : v = 1 ↔ x = r := by
    refine resultEq.trans ?_
    constructor
    · intro hw
      have vEq : scalarWords r = scalarWords x := by
        apply Vector.ext
        intro i hi
        rw [← leftWords i hi, ← rightWords i hi]
        exact hw i hi
      have rb : r < 2^256 := Nat.lt_trans e.bounds.2.1 (by decide +kernel)
      have natEq := congrArg Generate.Generator.Multiply.Split.scalarValue vEq
      rw [Generate.Generator.Multiply.Split.scalarWords_value _ rb,
        Generate.Generator.Multiply.Split.scalarWords_value _ bound] at natEq
      exact natEq.symm
    · intro eq i hi
      rw [leftWords i hi, rightWords i hi, eq]
  simp only [resultIff] at branch
  let outerResume := comparisonReturn .l105367 0x105367
  let innerResume := comparisonReturn .l10a2b3 0x10a2b3
  let boxResume := comparisonReturn .l10a2bd 0x10a2bd
  have runCompare := ParseSignature.exec_reaches_resume resultExec innerResume [outerResume]
    (by rw [resultTag]; rfl)
  have runChoice := ParseSignature.exec_reaches_resume chosenExec boxResume [outerResume]
    (by rw [chosenTag]; rfl)
  have runReturn := ParseSignature.exec_reaches_resume returnExec outerResume []
    (by rw [returnTag]; rfl)
  simp only [innerResume, boxResume, outerResume, resumeComparison, List.nil_append] at runCompare runChoice runReturn
  rw [resultMem] at runCompare
  have outerStep :
      program.step (dialect Extracted.programImage) ⟨⟨.l105357,b,m⟩,[]⟩ =
        .next ⟨⟨.l10a2a0,ca,outer⟩,[outerResume]⟩ :=
    congrArg (CFG.Transfer.next (dialect Extracted.programImage) []) outerCall
  have innerStep :
      program.step (dialect Extracted.programImage) ⟨⟨.l10a2a0,ca,outer⟩,[outerResume]⟩ =
        .next ⟨⟨.l127f50,eqArgs,compared⟩,[innerResume,outerResume]⟩ :=
    congrArg (CFG.Transfer.next (dialect Extracted.programImage) [outerResume]) innerCall
  have boxStep :
      program.step (dialect Extracted.programImage) ⟨⟨.l10a2b3,result.values,compared⟩,[outerResume]⟩ =
        .next ⟨⟨.l127d50,boxArgs,boxed⟩,[boxResume,outerResume]⟩ :=
    congrArg (CFG.Transfer.next (dialect Extracted.programImage) [outerResume]) choiceCall
  have beforeBranch : Reaches .l105357 b m .l105367 out.values out.store :=
    Star.step outerStep (Star.step innerStep
      (runCompare.trans (Star.step boxStep (runChoice.trans runReturn))))
  have regKeep := keepOuter.trans (keepInner.trans (keepResult.trans
    (keepBox.trans (keepChosen.trans (keepReturn.trans keepBranch)))))
  have localFrame : RamWriteFrame m out.store [scratch] := by
    rw [returnMem]
    exact chosenFrame
  have saved (off : BitVec 64) (fit : off.toNat ≤ 40) :
      memLoad out.store (fr.rsp-off) 64 = memLoad m (fr.rsp-off) 64 := by
    apply localFrame.memLoad_eq
    have natAddr : (fr.rsp-off).toNat = fr.rsp.toNat-off.toNat :=
      BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))
    refine ⟨by rw [natAddr]; omega, fun reg hreg => ?_⟩
    obtain rfl := List.mem_singleton.mp hreg
    right
    rw [natAddr]
    change sp.toNat - 25 + 25 ≤ _
    omega
  refine ⟨c, out.store, beforeBranch.trans branch, ⟨⟨branchSp.trans returnSp,
    (regKeep 3 (by decide)).trans h.dst, (regKeep 5 (by decide)).trans h.rbp,
    (regKeep 22 (by decide)).trans h.df, (regKeep 39 (by decide)).trans h.mxcsr,
    (regKeep 50 (by decide)).trans h.ftw, (regKeep 51 (by decide)).trans h.fcw,
    (saved 40 (by decide)).trans h.rbx, (saved 32 (by decide)).trans h.r12,
    (saved 24 (by decide)).trans h.r13, (saved 16 (by decide)).trans h.r14,
    (saved 8 (by decide)).trans h.r15⟩, h.frame.trans localFrame inside⟩⟩

end K256.Proofs.Verify.Core
