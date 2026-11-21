import K256.Proofs.Ecdh.Wrapper.State
import K256.Proofs.Ecdh.Wrapper.AffineCall
import K256.Proofs.Ecdh.Wrapper.AffineMemory
import K256.Proofs.Ecdh.LIR.Generated.Values

namespace K256.Proofs.Ecdh.Wrapper

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine Ecdh.LIR

theorem decoderValid {s : RamState} {secret peer : ByteArray} {m : Ram} {a : Arguments}
    (call : ValidCall ecdhDiffieHellman s [secret,peer]) (state : Caller s a m)
    (flag : memLoad m (localSp s + 432) 8 = 1) :
    ∃ b, Reaches .l101823 a m .l101831 b m ∧ Caller s b m := by
  have hsp := congrArg (Value.get 64) state.rsp
  change a[4].get 64 = localSp s at hsp
  have rd := ((Common.stackWritable (off := 5720) (len := 1) call
    (by decide) (by decide) (by decide)).of_frame state.frame).readable
  have gd : LoadOk m (localSp s + 432) 1 := by
    rw [show localSp s + 432 = s.regValue .rsp - 5720 from localOffset s 432 (by decide)]
    exact LoadOk.of_region rd (Nat.le_refl _) (Nat.le_refl _)
  suffices blk : ∃ b, program.runBlock (dialect Extracted.programImage) ⟨.l101823,a,m⟩ =
      .jump ⟨.l101831,b,m⟩ ∧ Caller s b m by
    obtain ⟨b,h,c⟩ := blk
    refine ⟨b,.single ?_,c⟩
    change (program.runBlock _ _).next _ _ = _
    rw [h]
    rfl
  refine ⟨?_,?run,?post⟩
  case run =>
    cfg_eval [hsp]
    simp only [gd,flag,↓reduceIte]
    rfl
  case post =>
    refine ⟨state.toMemory,state.rsp,state.output,state.df,?_,state.mxcsr,state.ftw,state.fcw⟩
    rintro ⟨i,hi⟩ h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals exact state.widths ⟨_,hi⟩ (by dsimp only; decide)

end K256.Proofs.Ecdh.Wrapper
