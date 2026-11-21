import K256.Proofs.Common.Tactic
import K256.Proofs.Verify.LIR.Generated.Values
import K256.Proofs.Verify.Core.Scalars.State

namespace K256.Proofs.Verify.Core.DigestFill

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
open CFG Lift Refine Verify.LIR

def resume : StackFrame Value Label signature Reg.count :=
  ⟨.l10513d, #v[], rfl, some ⟨64,0x10513d⟩⟩

def setupWrites (sp : BitVec 64) : List MemoryRegion :=
  [⟨(sp - 8).toNat,176⟩, ⟨(sp + 320).toNat,4⟩]

theorem setup (a : Registers) (m : Ram) (sp src : BitVec 64)
    (rsp : a[4].get 64 = sp) (size : a[13].get 64 = 32) (input : a[12].get 64 = src)
    (stack : Writable Extracted.programImage m (sp - 8) 332) :
    ∃ (b : Registers) (n : Ram),
      program.runBlock (dialect Extracted.programImage) ⟨.l1050c1,a,m⟩ =
        .call ⟨.l127d70,b,n⟩ resume ∧
      b[4] = ⟨64,sp - 8⟩ ∧ b[6] = ⟨64,32⟩ ∧ b[7] = ⟨64,src⟩ ∧
      b[1] = ⟨64,4⟩ ∧ b[2] = ⟨64,sp + 136⟩ ∧ b[8] = ⟨64,256⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [3,5,9,12,13,14,15,22,39,50,51] → b[i] = a[i]) ∧
      RamWriteFrame m n (setupWrites sp) ∧ memLoad n (sp - 8) 64 = 0x10513d := by
  refine ⟨?b, ?outMem, ?step, ?regs⟩
  case step =>
    cfg_eval [rsp, size, input]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l1050c1)
    rfl
  case regs =>
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
    · intro ⟨i, _⟩ hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · have low := stack.readable.low
      unfold setupWrites
      slot_state region
    · exact memLoad_memStore_same _ _ _ (by decide) (by decide)

end K256.Proofs.Verify.Core.DigestFill
