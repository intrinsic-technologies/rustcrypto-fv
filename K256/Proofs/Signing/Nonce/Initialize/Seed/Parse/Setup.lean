import K256.Proofs.Common.Tactic
import K256.Proofs.Verify.LIR.Generated.Values
import K256.Proofs.Verify.Core.Scalars.State

namespace K256.Proofs.Signing.Nonce.Initialize.DigestParse

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
open Verify.Core CFG Lift Refine Verify.LIR

def resume : StackFrame Value Label signature Reg.count :=
  ⟨.l10106a, #v[], rfl, some ⟨64,0x10106a⟩⟩

def setupWrites (sp : BitVec 64) : List MemoryRegion :=
  [⟨(sp - 8).toNat,168⟩]

theorem setup (a : Registers) (m : Ram) (sp src : BitVec 64)
    (rsp : a[4].get 64 = sp) (size : a[6] = ⟨64,32⟩) (input : a[0].get 64 = src) (bits : a[9].get 64 = 256)
    (stack : Writable Extracted.programImage m (sp - 8) 168) :
    ∃ (b : Registers) (n : Ram),
      program.runBlock (dialect Extracted.programImage) ⟨.l101026,a,m⟩ =
        .call ⟨.l127d70,b,n⟩ resume ∧
      b[4] = ⟨64,sp - 8⟩ ∧ b[6] = ⟨64,32⟩ ∧ b[7] = ⟨64,src⟩ ∧
      b[1] = ⟨64,4⟩ ∧ b[2] = ⟨64,sp + 104⟩ ∧ b[8] = ⟨64,256⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [3,5,9,12,13,14,15,22,39,50,51] → b[i] = a[i]) ∧
      RamWriteFrame m n (setupWrites sp) ∧ memLoad n (sp - 8) 64 = 0x10106a := by
  refine ⟨?b, ?outMem, ?step, ?regs⟩
  case step =>
    cfg_eval [rsp, input, bits]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l101026)
    rfl
  case regs =>
    refine ⟨rfl, size, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
    · intro ⟨i, _⟩ hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · have low := stack.readable.low
      unfold setupWrites
      slot_state region
    · exact memLoad_memStore_same _ _ _ (by decide) (by decide)

theorem branch {mem : Ram} {a : Verify.Core.Registers} (status : a[0].get 8 = 255) (widths : ParseSignature.ArgumentWidths a) :
    ∃ b : Verify.Core.Registers, Verify.Core.Reaches .l10106a a mem .l101072 b mem ∧
      (∀ i : Fin Reg.count, i.val ∈ [3, 4, 5, 12, 13, 14, 15, 22, 39, 50, 51] → b[i] = a[i]) ∧
      ParseSignature.ArgumentWidths b := by
  have low : (a[0].get 64).setWidth 8 = 255 := by
    simpa only [Value.get, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64)] using status
  refine ⟨?next, .single ?step, ?regs, ?w⟩
  case step =>
    change (program.runBlock _ _).next _ [] = _
    cfg_eval [low, cmpSpec_ZF]
    rfl
  case regs =>
    intro ⟨i, hi⟩ h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  case w =>
    intro ⟨i, hi⟩ h
    have hw := widths ⟨i, hi⟩ h
    simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hw

end K256.Proofs.Signing.Nonce.Initialize.DigestParse
