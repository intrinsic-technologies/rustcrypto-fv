import K256.Proofs.Verify.Hash.FinalBlocks.Memory
import K256.Proofs.Verify.LIR.Program
import K256.Proofs.Verify.LIR.Generated.Values
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Store2

namespace K256.Proofs.Verify.Hash.FinalBlocks

open Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Spec.Program
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

def callSite (last : Bool) : Label := if last then .l103289 else .l1031cd

def resumeSite (last : Bool) : Label := if last then .l103306 else .l10324a

def returnAddress (last : Bool) : Word := if last then 0x103306 else 0x10324a

def resumeFrame (last : Bool) : StackFrame Value Label signature Reg.count :=
  ⟨resumeSite last, #v[], rfl, some ⟨64, returnAddress last⟩⟩

def callMemory (last : Bool) (m : Ram) (sp length : Word) : Ram :=
  if last then stage (memStore m (sp + 64) length) sp length (returnAddress true)
  else stage m sp (memLoad m (sp + 64) 64) (returnAddress false)

theorem prepareCall (last : Bool) (a : Values Value Reg.count) (m : Ram) (sp : Word)
    (rsp : a[4].get 64 = sp) (rbx : a[3].get 64 = sp + 72)
    (stack : Writable Extracted.programImage m (sp - 8) 232) :
    ∃ b : Values Value Reg.count,
      program.runBlock (dialect Extracted.programImage) ⟨callSite last, a, m⟩ =
        .call ⟨.l1218e0, b, callMemory last m sp (a[15].get 64)⟩ (resumeFrame last) ∧
      b[4].get 64 = sp - 8 ∧ b[7].get 64 = sp + 72 ∧ b[6].get 64 = sp + 160 ∧
      b[2].get 64 = 1 ∧
      ∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15,22,39,50,51] → b[i] = a[i] := by
  cases last
  · simp only [callSite, callMemory, resumeFrame, resumeSite, returnAddress, Bool.false_eq_true,
      ↓reduceIte]
    refine ⟨?b, ?step, ?rsp, ?dst, ?src, ?count, ?saved⟩
    case step =>
      change program.runBlock (dialect Extracted.programImage) ⟨.l1031cd,a,m⟩ = _
      cfg_eval [rsp, rbx]
      repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l1031cd)
      simp (disch := store_disch) only [stage, memLoad_memStore_of_rangeApart] <;> rfl
    case rsp => rfl
    case dst => rfl
    case src => rfl
    case count => rfl
    case saved =>
      intro ⟨i,_⟩ hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · simp only [callSite, callMemory, resumeFrame, resumeSite, returnAddress, ↓reduceIte]
    refine ⟨?b, ?step, ?rsp, ?dst, ?src, ?count, ?saved⟩
    case step =>
      change program.runBlock (dialect Extracted.programImage) ⟨.l103289,a,m⟩ = _
      cfg_eval [rsp, rbx]
      repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l103289)
      simp (disch := store_disch) only [stage, memLoad_memStore_of_rangeApart] <;> rfl
    case rsp => rfl
    case dst => rfl
    case src => rfl
    case count => rfl
    case saved =>
      intro ⟨i,_⟩ hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

end K256.Proofs.Verify.Hash.FinalBlocks
