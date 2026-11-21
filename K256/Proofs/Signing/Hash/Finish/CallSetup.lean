import K256.Proofs.Verify.Hash.FinalBlocks.Memory
import K256.Proofs.Signing.Hash.Finish.Memory
import K256.Proofs.Signing.Hash.State
import K256.Proofs.Verify.LIR.Program
import K256.Proofs.Verify.LIR.Generated.Values
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Store2

namespace K256.Proofs.Signing.Hash.Finish

open Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Spec.Program
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

def callSite (last : Bool) : Label := if last then .l1056d8 else .l10561c

def resumeSite (last : Bool) : Label := if last then .l105758 else .l105699

def returnAddress (last : Bool) : Word := if last then 0x105758 else 0x105699

def resumeFrame (last : Bool) : StackFrame Value Label signature Reg.count :=
  ⟨resumeSite last, #v[], rfl, some ⟨64, returnAddress last⟩⟩

def callMemory (last : Bool) (m : Ram) (sp length : Word) : Ram :=
  if last then stage (memStore m (sp + 64) length) sp length (returnAddress true)
  else stage m sp (memLoad m (sp + 64) 64) (returnAddress false)

set_option maxHeartbeats 700000 in
theorem prepareCall (last : Bool) (a : Values Value Reg.count) (m : Ram) (sp : Word)
    (rsp : a[4].get 64 = sp) (rbx : a[3].get 64 = sp + 72)
    (r13 : last = false → a[13].width = 64)
    (stack : Writable Extracted.programImage m (sp - 8) 328) :
    ∃ b : Values Value Reg.count,
      program.runBlock (dialect Extracted.programImage) ⟨callSite last, a, m⟩ =
        .call ⟨.l1218e0, b, callMemory last m sp (a[15].get 64)⟩ (resumeFrame last) ∧
      b[4].get 64 = sp - 8 ∧ b[7].get 64 = sp + 72 ∧ b[6].get 64 = sp + 256 ∧
      b[2].get 64 = 1 ∧ b[13].width = 64 ∧ (last = true → b[13] = ⟨64,sp+256⟩) ∧
      ∀ i : Fin Reg.count, i.val ∈ [3,5,12,14,15,22,39,50,51] → b[i] = a[i] := by
  cases last
  · simp only [callSite, callMemory, resumeFrame, resumeSite, returnAddress, Bool.false_eq_true,
      ↓reduceIte]
    refine ⟨?b, ?step, ?rsp, ?dst, ?src, ?count, ?width, ?pointer, ?saved⟩
    case step =>
      change program.runBlock (dialect Extracted.programImage) ⟨.l10561c,a,m⟩ = _
      cfg_eval [rsp, rbx]
      repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l10561c)
      simp (disch := store_disch) only [stage, memLoad_memStore_of_rangeApart] <;> rfl
    case rsp => rfl
    case dst => rfl
    case src => rfl
    case count => rfl
    case width => exact r13 rfl
    case pointer => intro h; contradiction
    case saved =>
      intro ⟨i,_⟩ hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · simp only [callSite, callMemory, resumeFrame, resumeSite, returnAddress, ↓reduceIte]
    refine ⟨#v[⟨64, memLoad m (sp+8) 64⟩, ⟨64, memLoad m (sp+16) 64⟩, ⟨64,1⟩, a[3], ⟨64, sp-8⟩,
      a[5], ⟨64, sp+256⟩, ⟨64, sp+72⟩, a[8], a[9], a[10], a[11],
      a[12], ⟨64, sp+256⟩, a[14], a[15], a[16], a[17], a[18],
      a[19], a[20], a[21], a[22], a[23], a[24], a[25],
      a[26], a[27], a[28], a[29], a[30], a[31], a[32],
      a[33], a[34], a[35], a[36], a[37], a[38], a[39],
      a[40], a[41], a[42], a[43], a[44], a[45], a[46],
      a[47], a[48], a[49], a[50], a[51], a[52]], ?step, ?rsp, ?dst, ?src, ?count, ?width, ?pointer, ?saved⟩
    case step =>
      change program.runBlock (dialect Extracted.programImage) ⟨.l1056d8,a,m⟩ = _
      cfg_eval [rsp, rbx]
      repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l1056d8)
      simp (disch := store_disch) only [stage, memLoad_memStore_of_rangeApart] <;> rfl
    case rsp => rfl
    case dst => rfl
    case src => rfl
    case count => rfl
    case width => rfl
    case pointer => intro _; rfl
    case saved =>
      intro ⟨i,_⟩ hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem clearBlock (a : Values Value Reg.count) (m : Ram) (sp : Word)
    (rsp : a[4].get 64 = sp) (stack : Writable Extracted.programImage m (sp + 8) 56) :
    ∃ b : Values Value Reg.count,
      program.runBlock (dialect Extracted.programImage) ⟨.l105699,a,m⟩ =
        .jump ⟨.l1056d8,b,K256.Proofs.Verify.Hash.FinalBlocks.clearPrefix m sp⟩ ∧
      ∀ i : Fin Reg.count, i.val ∈ [3,4,5,12,14,15,22,39,50,51] → b[i] = a[i] := by
  refine ⟨?b, ?step, ?keep⟩
  case step =>
    cfg_eval [rsp]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using code_l105699)
    rfl
  case keep =>
    intro ⟨j,_⟩ hj
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

end K256.Proofs.Signing.Hash.Finish
