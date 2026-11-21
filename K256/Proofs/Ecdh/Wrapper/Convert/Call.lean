import K256.Proofs.Ecdh.Wrapper.State
import K256.Proofs.Ecdh.Wrapper.Child
import K256.Proofs.Ecdh.Wrapper.AffineMemory
import K256.Proofs.Ecdh.LIR.EcdhDiffieHellman
import K256.Proofs.Common.Lift.Rep

namespace K256.Proofs.Ecdh.Wrapper

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine Ecdh.LIR

set_option maxRecDepth 4096 in
theorem convertCall {s : RamState} {a : Arguments} {m : Ram} (state : Caller s a m)
    (copy : RepMovsOk Extracted.programImage m 0 (localSp s + 344) (localSp s + 4184)
      11 8 0x101849 3)
    (push : StoreOk Extracted.programImage (memCopy m (localSp s + 4184) (localSp s + 344) 88)
      (returnSlot s) 8 0x10185a 5) :
    let sp := localSp s
    let n := memStore (memCopy m (sp + 4184) (sp + 344) 88) (returnSlot s) (0x10185f : BitVec 64)
    ∃ b, program.runBlock (dialect Extracted.programImage) ⟨.l101831,a,m⟩ =
      .call ⟨.l10fa10,b,n⟩ ⟨.l10185f,#v[],rfl,some ⟨64,0x10185f⟩⟩ ∧
      ChildRegisters s b ∧ b[3] = ⟨64,s.regValue .rdi⟩ ∧ b[6] = ⟨64,sp+4184⟩ ∧
      b[7] = ⟨64,sp+344⟩ ∧ b[15] = ⟨64,sp+344⟩ := by
  intro sp n
  have rsp : a[4].get 64 = sp := congrArg (Value.get 64) state.rsp
  have df : a[22].get 1 = 0 := congrArg (Value.get 1) state.df
  refine ⟨?b, ?run, ?regs, ?_⟩
  case run =>
    cfg_eval [rsp, df]
    change (if False ∨ RepMovsOk _ m 0 _ _ 11 8 _ _ then
      if StoreOk _ _ _ _ _ _ then _ else _ else _) = _
    rw [ite_eq_left (Or.inr copy), ite_eq_left (show StoreOk _ _ (sp-8) 8 _ _ by
      simpa only [sp,localSp_sub_eight] using push)]
    rw [show sp-8 = returnSlot s from localSp_sub_eight s]
  case regs =>
    constructor
    · rfl
    · exact state.df
    · intro ⟨i,hi⟩ hm
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
      rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals first
        | rfl
        | exact state.widths 2 (by decide)
        | exact state.widths 3 (by decide)
        | exact state.widths 5 (by decide)
        | exact state.widths 8 (by decide)
        | exact state.widths 9 (by decide)
        | exact state.widths 12 (by decide)
        | exact state.widths 13 (by decide)
        | exact state.widths 14 (by decide)
    · exact state.mxcsr
    · exact state.ftw
    · exact state.fcw
  exact ⟨state.output,rfl,rfl,rfl⟩

end K256.Proofs.Ecdh.Wrapper
