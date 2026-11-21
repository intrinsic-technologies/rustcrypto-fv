import K256.Proofs.ParseSignature.Contract
import K256.Proofs.ParseSignature.Memory
import K256.Proofs.LIR.Fn127d70.Frame
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

namespace K256.Proofs.ParseSignature.Fill

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.LIR

abbrev Registers := Vector Value Reg.count

def keeps (before after : Registers) (which : List Nat) : Prop :=
  ∀ r ∈ which, ∀ h : r < Reg.count, after[r] = before[r]

theorem get64 {a : Value} {x : BitVec 64} (h : a = ⟨64, x⟩) : a.get 64 = x := by
  rw [h]
  rfl

private theorem stackStoreOk {code : CodeMap} {m : Ram} {sp base : BitVec 64}
    {offset instrOff instrLen : Nat} {bytes : List UInt8}
    (hw : Writable code m (sp - 208) 208) (ho : 8 ≤ offset ∧ offset ≤ 208)
    (hc : ∀ x ∈ codeRange base bytes, x ∈ code) (hi : instrOff + instrLen ≤ bytes.length) :
    StoreOk code m (sp - BitVec.ofNat 64 offset) 8 (base + BitVec.ofNat 64 instrOff) instrLen := by
  apply storeOk_of_codeRange (included := hc) (within := hi)
  apply hw.of_offsets (x := sp) (addr_sub _ _) (addr_sub _ _)
  have hoff : (0 - BitVec.ofNat 64 offset - (0 - 208)).toNat = 208 - offset := by
    rw [show (0 : BitVec 64) - BitVec.ofNat 64 offset - (0 - 208) =
      (208 : BitVec 64) - BitVec.ofNat 64 offset by bv_omega]
    change ((208 : BitVec 64) - BitVec.ofNat 64 offset).toNat = 208 - offset
    rw [BitVec.toNat_sub_of_le]
    · change 208 - offset % 2^64 = 208 - offset
      rw [Nat.mod_eq_of_lt (by omega)]
    · change offset % 2^64 ≤ 208
      rw [Nat.mod_eq_of_lt (by omega)]
      exact ho.2
  rw [hoff]
  omega

def saveRegisters (m : Ram) (sp : BitVec 64) (a : Registers) : Ram :=
  let m := memStore m (sp - 8) (a[5].get 64)
  let m := memStore m (sp - 16) (a[15].get 64)
  let m := memStore m (sp - 24) (a[14].get 64)
  let m := memStore m (sp - 32) (a[13].get 64)
  let m := memStore m (sp - 40) (a[12].get 64)
  memStore m (sp - 48) (a[3].get 64)

theorem entryBlock {code : CodeMap} {a : Registers} {m : Ram} {sp : BitVec 64}
    (hcode : ∀ x ∈ fnCode, x ∈ code)
    (hsp : a[4] = ⟨64, sp⟩) (hk : a[1] = ⟨64, 4⟩) (hwid : a[8] = ⟨64, 256⟩)
    (hw : Writable code m (sp - 208) 208) :
    ∃ next : Registers,
      program.runBlock (dialect code) ⟨.l127d70, a, m⟩ =
        .jump ⟨.l127d91, next, saveRegisters m sp a⟩ ∧
      next[4] = ⟨64, sp - 72⟩ ∧ next[14] = ⟨64, a[2].get 64⟩ ∧
      keeps a next [1, 6, 7, 8, 9, 22, 39, 50, 51] := by
  have hc : ∀ x ∈ codeRange 0x127d70 bytes_l127d70, x ∈ code :=
    fun x hx => hcode x (code_l127d70 x hx)
  have h5 : StoreOk code _ (sp - 8) 8 0x127d70 1 :=
    stackStoreOk (offset := 8) (instrOff := 0) hw (by decide) hc (by decide)
  have hw := hw.memStore (sp - 8) (a[5].get 64)
  have h15 : StoreOk code _ (sp - 16) 8 0x127d71 2 :=
    stackStoreOk (offset := 16) (instrOff := 1) hw (by decide) hc (by decide)
  have hw := hw.memStore (sp - 16) (a[15].get 64)
  have h14 : StoreOk code _ (sp - 24) 8 0x127d73 2 :=
    stackStoreOk (offset := 24) (instrOff := 3) hw (by decide) hc (by decide)
  have hw := hw.memStore (sp - 24) (a[14].get 64)
  have h13 : StoreOk code _ (sp - 32) 8 0x127d75 2 :=
    stackStoreOk (offset := 32) (instrOff := 5) hw (by decide) hc (by decide)
  have hw := hw.memStore (sp - 32) (a[13].get 64)
  have h12 : StoreOk code _ (sp - 40) 8 0x127d77 2 :=
    stackStoreOk (offset := 40) (instrOff := 7) hw (by decide) hc (by decide)
  have hw := hw.memStore (sp - 40) (a[12].get 64)
  have h3 : StoreOk code _ (sp - 48) 8 0x127d79 1 :=
    stackStoreOk (offset := 48) (instrOff := 9) hw (by decide) hc (by decide)
  refine ⟨?next, ?eval, ?post⟩
  case eval =>
    cfg_eval
    simp only [get64 hsp, hk, hwid, h5, h15, h14, h13, h12, h3, ite_true]
    rfl
  case post =>
    refine ⟨rfl, rfl, ?_⟩
    intro r hr h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | rfl | exact hk.symm | exact hwid.symm

theorem setupCountBlock {code : CodeMap} {a : Registers} {m : Ram} {sp : BitVec 64}
    (hsp : a[4] = ⟨64, sp - 72⟩)
    (hk : a[1] = ⟨64, 4⟩) (hn : a[6] = ⟨64, 32⟩) (hwid : a[8] = ⟨64, 256⟩)
    (hw : StoreOk code m (sp - 64) 8 0x127d94 5) :
    ∃ next : Registers, program.runBlock (dialect code) ⟨.l127d91, a, m⟩ =
        .jump ⟨.l127dc1, next, memStore m (sp - 64) (4 : BitVec 64)⟩ ∧
      next[3] = ⟨64, 256⟩ ∧ next[13] = ⟨64, 32⟩ ∧
      keeps a next [4, 6, 7, 8, 9, 14, 22, 39, 50, 51] := by
  have haddr : sp - 72 + 8 = sp - 64 := by bv_omega
  refine ⟨?next, ?eval, ?post⟩
  case eval =>
    cfg_eval
    simp only [get64 hsp, hk, hn, hwid, haddr, hw, ite_true]
    rfl
  case post =>
    refine ⟨rfl, rfl, ?_⟩
    intro r hr h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | rfl | exact hn.symm | exact hwid.symm

theorem setupLimbCountBlock {code : CodeMap} {a : Registers} {m : Ram} {sp : BitVec 64}
    (hsp : a[4] = ⟨64, sp - 72⟩) (hn : a[13] = ⟨64, 32⟩)
    (hr : LoadOk m (sp - 64) 8) (hv : memLoad m (sp - 64) 64 = 4) :
    ∃ next : Registers, program.runBlock (dialect code) ⟨.l127dc1, a, m⟩ =
        .jump ⟨.l127dda, next, m⟩ ∧
      next[5] = ⟨64, 4⟩ ∧
      keeps a next [3, 4, 6, 7, 8, 9, 13, 14, 22, 39, 50, 51] := by
  have haddr : sp - 72 + 8 = sp - 64 := by bv_omega
  refine ⟨?next, ?eval, ?post⟩
  case eval =>
    cfg_eval
    simp only [get64 hsp, hn, haddr, hr, hv, ite_true]
    rfl
  case post =>
    refine ⟨rfl, ?_⟩
    intro r hr h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | rfl | exact hn.symm

theorem setupLoopBlock {code : CodeMap} {a : Registers} {m : Ram}
    (hn : a[6] = ⟨64, 32⟩) (hk : a[5] = ⟨64, 4⟩) :
    ∃ next : Registers, program.runBlock (dialect code) ⟨.l127dda, a, m⟩ =
        .jump ⟨.l127e2e, next, m⟩ ∧
      next[5] = ⟨64, 32⟩ ∧ next[12] = ⟨64, a[7].get 64 + 32⟩ ∧ next[15] = ⟨64, 0⟩ ∧
      keeps a next [3, 4, 8, 9, 13, 14, 22, 39, 50, 51] := by
  refine ⟨?next, ?eval, ?post⟩
  case eval =>
    cfg_eval
    simp only [get64 hn, get64 hk]
    rfl
  case post =>
    refine ⟨rfl, rfl, rfl, ?_⟩
    intro r hr h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl


theorem prepareCopyBlock {code : CodeMap} {a : Registers} {m : Ram} {sp n : BitVec 64}
    (hn : 8 ≤ n.toNat) (hsp : a[4] = ⟨64, sp - 72⟩) (hleft : a[13] = ⟨64, n⟩)
    (hw : StoreOk code m (sp - 56) 8 0x127e41 9) :
    ∃ next : Registers, program.runBlock (dialect code) ⟨.l127e2e, a, m⟩ =
        .jump ⟨.l127df0, next, memStore m (sp - 56) (0 : BitVec 64)⟩ ∧
      next[0] = ⟨64, 8⟩ ∧ next[6] = ⟨64, -8⟩ ∧
      keeps a next [3, 4, 5, 8, 9, 12, 13, 14, 15, 22, 39, 50, 51] := by
  have haddr : sp - 72 + 16 = sp - 56 := by bv_omega
  have hcarry : (cmpSpec n 8).CF = false := by
    change decide (n.toNat < 8) = false
    exact decide_eq_false (by omega)
  refine ⟨?next, ?eval, ?post⟩
  case eval =>
    cfg_eval
    simp only [get64 hsp, get64 hleft, haddr, hw, hcarry, Bool.false_eq_true, ite_false, ite_true]
    rfl
  case post =>
    refine ⟨rfl, rfl, ?_⟩
    intro r hr h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem copyCallBlock {code : CodeMap} {a : Registers} {m : Ram} {sp inputEnd : BitVec 64}
    {n : BitVec 64}
    (hsp : a[4] = ⟨64, sp - 72⟩) (h0 : a[0] = ⟨64, 8⟩) (h6 : a[6] = ⟨64, -8⟩)
    (h12 : a[12] = ⟨64, inputEnd⟩) (h13 : a[13] = ⟨64, n⟩)
    (hw : StoreOk code m (sp - 80) 8 0x127e0b 6)
    (hr : LoadOk m 0x203dd0 8) (hv : memLoad m 0x203dd0 64 = 0x12a820) :
    ∃ next : Registers, ∃ cont : StackFrame Value Label signature Reg.count,
      program.runBlock (dialect code) ⟨.l127df0, a, m⟩ =
        .call ⟨.l12a820, next, memStore m (sp - 80) (0x127e11 : BitVec 64)⟩ cont ∧
      cont.target = .l127e11 ∧ cont.guard = some ⟨64, 0x127e11⟩ ∧
      next[1] = ⟨64, n - 8⟩ ∧ next[2] = ⟨64, 8⟩ ∧ next[4] = ⟨64, sp - 80⟩ ∧
      next[6] = ⟨64, inputEnd - 8⟩ ∧ next[7] = ⟨64, sp - 56⟩ ∧
      keeps a next [3, 5, 8, 9, 12, 13, 14, 15, 22, 39, 50, 51] := by
  have getValue (x : BitVec 64) : (⟨64, x⟩ : Value).get 64 = x := rfl
  have hn : n - (n - 8) = 8 := by bv_omega
  have hsrc : -8 + inputEnd = inputEnd - 8 := by bv_omega
  have hret : sp - 72 - 8 = sp - 80 := by bv_omega
  have hdst : sp - 72 + 16 - 8 + 8 = sp - 56 := by bv_omega
  refine ⟨?next, ?cont, ?eval, ?post⟩
  case eval =>
    cfg_eval
    simp only [get64 hsp, h0, h6, h12, h13, getValue, hn, hsrc, hret, hdst, hw, hr, hv,
      and_self, ite_true]
    rfl
  case post =>
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    intro r hr h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | rfl | exact h12.symm | exact h13.symm


theorem swapBlock {code : CodeMap} {a : Registers} {m : Ram} {sp : BitVec 64}
    (hsp : a[4] = ⟨64, sp - 72⟩) (hr : LoadOk m (sp - 56) 8) :
    ∃ next : Registers, program.runBlock (dialect code) ⟨.l127e11, a, m⟩ = .jump ⟨.l127e19, next, m⟩ ∧
      next[0] = ⟨64, bswapSpec (memLoad m (sp - 56) 64)⟩ ∧
      keeps a next [1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 13, 14, 15, 22, 39, 50, 51] := by
  have haddr : sp - 72 + 16 = sp - 56 := by bv_omega
  refine ⟨?next, ?eval, ?post⟩
  case eval =>
    cfg_eval
    simp only [get64 hsp, haddr, hr, ite_true]
    rfl
  case post =>
    refine ⟨rfl, ?_⟩
    intro r hr h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl <;> rfl

theorem storeLimbBlock {code : CodeMap} {a : Registers} {m : Ram}
    {dst offset count inputEnd value : BitVec 64}
    (hval : a[0] = ⟨64, value⟩) (hlimit : a[5] = ⟨64, 32⟩)
    (hsrc : a[12] = ⟨64, inputEnd⟩) (hleft : a[13] = ⟨64, count⟩)
    (hdst : a[14] = ⟨64, dst⟩) (hoff : a[15] = ⟨64, offset⟩)
    (hw : StoreOk code m (dst + offset) 8 0x127e19 4) :
    ∃ next : Registers,
      program.runBlock (dialect code) ⟨.l127e19, a, m⟩ =
        .jump ⟨if offset + 8 = 32 then .l127e50 else .l127e2e, next, memStore m (dst + offset) value⟩ ∧
      next[12] = ⟨64, inputEnd - 8⟩ ∧ next[13] = ⟨64, count - 8⟩ ∧
      next[15] = ⟨64, offset + 8⟩ ∧
      keeps a next [1, 2, 3, 4, 5, 6, 7, 8, 9, 14, 22, 39, 50, 51] := by
  by_cases hexit : offset + 8 = 32
  all_goals
    refine ⟨?_, ?_, ?_⟩
    rotate_left
    · first | rw [ite_eq_left hexit] | rw [ite_eq_right hexit]
      cfg_eval
      simp only [get64 hval, get64 hlimit, get64 hsrc, get64 hleft, get64 hdst,
        get64 hoff, hw, cmpSpec_ZF, beq_iff_eq, eq_comm (a := (32 : BitVec 64)), hexit,
        ite_true, ite_false]
      rfl
    · refine ⟨rfl, rfl, ?_, ?_⟩
      · first | rfl | exact congrArg (fun x : BitVec 64 => (⟨64, x⟩ : Value)) hexit.symm
      intro r hr h
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
        rfl <;> rfl

theorem keeps.widths {a b : Registers} {which : List Nat} (h : keeps a b which)
    (harg : ∀ r ∈ Activation.argumentNumbers, r ∈ which) (hw : ArgumentWidths a) : ArgumentWidths b := by
  intro i hi
  rw [show b[i] = a[i] from h i.val (harg _ hi) i.isLt]
  exact hw i hi

end K256.Proofs.ParseSignature.Fill
