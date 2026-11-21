import K256.Proofs.Signing.Transfer.Generator.Blocks

namespace K256.Proofs.Signing.Transfer

open X86.Machine X86.UserProcess X86Proofs CFG Lift

theorem generator {src : Generate.LIR.Label} {dst : Verify.LIR.Label}
    (entry : (src, dst) ∈ [(.l10ee80, .l10ee80), (.l10fe50, .l10fe50)])
    {code : CodeMap} {a : Values Value Reg.count} {m : Ram} {out : Output Value Ram Reg.count}
    (run : Generate.LIR.program.Exec (dialect code) ⟨⟨src, a, m⟩, []⟩ out) :
    Verify.LIR.program.Exec (dialect code) ⟨⟨dst, a, m⟩, []⟩ out := by
  apply Verify.Transfer.Padding.exec Generator.paddingPrefix
  apply Generate.Serialize.Relabel.exec Generator.blocks run
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at entry
  rcases entry with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> rfl

end K256.Proofs.Signing.Transfer
