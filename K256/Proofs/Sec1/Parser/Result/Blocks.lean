import K256.Proofs.Sec1.LIR.Program
import K256.Proofs.Sec1.LIR.Generated.Values
import K256.Proofs.ParseSignature.Contract
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Store2

namespace K256.Proofs.Sec1.Parser.Result

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine
open K256.Proofs.Sec1.LIR

variable {code : CodeMap} {args : Values Value Reg.count} {mem : Ram}

structure Preserved (a b : Values Value Reg.count) : Prop where
  reg : ∀ i : Fin Reg.count, i.val ∈ [3, 4, 5, 8, 9, 12, 13, 14, 15, 22, 39, 50, 51] → b[i] = a[i]
  widths : ParseSignature.ArgumentWidths a → ParseSignature.ArgumentWidths b

theorem Preserved.trans {a b c : Values Value Reg.count} (ab : Preserved a b) (bc : Preserved b c) :
    Preserved a c := ⟨fun i hi => (bc.reg i hi).trans (ab.reg i hi), bc.widths ∘ ab.widths⟩

local macro "kept_regs" : tactic => `(tactic|
  (constructor
   · intro ⟨i, _⟩ hi
     simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
     rcases hi with h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst i <;> rfl
   · intro hw ⟨i, hb⟩ hi
     have width := hw ⟨i, hb⟩ hi
     simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at hi
     rcases hi with h | h | h | h | h | h <;> subst i <;> first | rfl | exact width))

theorem copyOutput (sp out : BitVec 64)
    (rsp : args[4].get 64 = sp) (dst : args[7].get 64 = out)
    (saved : args[15].get 64 = out)
    (copy : RepMovsOk code mem (args[22].get 1) (sp + 72) (out + 8) 11 8 0x106556 3) :
    ∃ next : Values Value Reg.count, program.runBlock (dialect code) ⟨.l106548, args, mem⟩ =
      .jump ⟨.l106565, next, memCopy mem (out + 8) (sp + 72) 88⟩ ∧
      next[0] = ⟨64, 0⟩ ∧ next[7] = ⟨64, out⟩ ∧ Preserved args next := by
  refine ⟨?_, ?step, ?post⟩
  case step =>
    cfg_eval [rsp, dst, saved, copy]
    rfl
  case post =>
    refine ⟨?_, ?_, ?_⟩
    · simp
    · rfl
    · kept_regs

theorem stage (sp : BitVec 64) (tag : BitVec 8)
    (rsp : args[4].get 64 = sp) (src : args[3].get 64 = sp + 160)
    (copy : RepMovsOk code mem (args[22].get 1) (sp + 160) (sp + 72) 11 8 0x106501 3)
    (read : LoadOk (memCopy mem (sp + 72) (sp + 160) 88) (sp + 4) 1)
    (value : memLoad (memCopy mem (sp + 72) (sp + 160) 88) (sp + 4) 8 = tag) :
    ∃ next : Values Value Reg.count, program.runBlock (dialect code) ⟨.l1064f4, args, mem⟩ =
      (if 2 ≤ tag.toNat ∧ tag.toNat < 6 then .jump ⟨.l106518, next, memCopy mem (sp + 72) (sp + 160) 88⟩
       else .jump ⟨.l106514, next, memCopy mem (sp + 72) (sp + 160) 88⟩) ∧
      next[0] = ⟨64, tag.setWidth 64⟩ ∧ next[1] = ⟨64, tag.setWidth 64⟩ ∧ Preserved args next := by
  have tagCheck (t : BitVec 8) :
      ((cmpSpec ((t.setWidth 64 - 2).setWidth 32) 4).CF = true) ↔ 2 ≤ t.toNat ∧ t.toNat < 6 := by
    revert t
    decide +kernel
  by_cases h : 2 ≤ tag.toNat ∧ tag.toNat < 6
  all_goals
    simp only [h, ↓reduceIte]
    refine ⟨?_, ?step, ?post⟩
    case step =>
      cfg_eval [rsp, src, copy, read, value]
      simp only [tagCheck, h, or_true, ↓reduceIte]
      rfl
    case post => exact ⟨rfl, rfl, by kept_regs⟩

theorem zeroTag (v : args[1].get 64 = 0) :
    ∃ next : Values Value Reg.count, program.runBlock (dialect code) ⟨.l106514, args, mem⟩ =
      .jump ⟨.l106518, next, mem⟩ ∧ next[0] = args[0] ∧ Preserved args next := by
  refine ⟨?_, ?step, ?post⟩
  case step => cfg_eval [v]; rfl
  case post => exact ⟨rfl, by kept_regs⟩

def selectedByte (tag affine identity : BitVec 8) : BitVec 8 :=
  if tag = 0 then identity else affine &&& 1

theorem select (sp out : BitVec 64) (tag affine identity : BitVec 8)
    (rsp : args[4].get 64 = sp) (dst : args[15].get 64 = out)
    (al : (args[0].get 64).setWidth 8 = tag) (r12 : (args[12].get 64).setWidth 8 = identity)
    (read : LoadOk mem (sp + 248) 1) (aval : memLoad mem (sp + 248) 8 = affine)
    (write : StoreOk code mem (sp + 160) 1 0x10652c 7)
    (checkFlag : LoadOk (memStore mem (sp + 160) (selectedByte tag affine identity)) (sp + 160) 1) :
    ∃ next : Values Value Reg.count, program.runBlock (dialect code) ⟨.l106518, args, mem⟩ =
      (if selectedByte tag affine identity = 0 then .jump ⟨.l106560, next, memStore mem (sp + 160) (selectedByte tag affine identity)⟩
       else .jump ⟨.l106548, next, memStore mem (sp + 160) (selectedByte tag affine identity)⟩) ∧
        next[7] = ⟨64, out⟩ ∧ Preserved args next := by
  have sel :
      (if (testFlags (tag &&& tag)).ZF.getD false = true then (args[12].get 64).setWidth 32
       else (((mergeGPR 8 (affine &&& 1) (affine.setWidth 64)).setWidth 8).setWidth 32)).setWidth 8 =
          selectedByte tag affine identity := by
    simp only [testFlags, BitVec.and_self, Option.getD_some, beq_iff_eq, setWidth_mergeGPR8, selectedByte]
    split
    · exact (BitVec.setWidth_setWidth_of_le _ (by decide)).trans r12
    · exact BitVec.setWidth_setWidth_of_le _ (by decide)
  have zero (t : BitVec 8) : ((cmpSpec t 0).ZF = true) ↔ t = 0 := by
    revert t
    decide +kernel
  have stored := memLoad_memStore_same mem (sp + 160) (selectedByte tag affine identity) (by decide) (by decide)
  by_cases h : selectedByte tag affine identity = 0
  all_goals
    simp only [h, ↓reduceIte]
    refine ⟨?_, ?step, ?post⟩
    case step =>
      cfg_eval [rsp, dst, al, read, aval, write]
      simp only [sel, checkFlag, ↓reduceIte, stored, zero]
      simp only [h, ↓reduceIte]
      rfl
    case post => exact ⟨rfl, by kept_regs⟩

end K256.Proofs.Sec1.Parser.Result
