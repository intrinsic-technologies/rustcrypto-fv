import K256.Proofs.Sec1.Serialize.Normalize.Blocks

namespace K256.Proofs.Sec1.Serialize.Normalize

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
open K256.Proofs.Refine K256.Proofs.Common.Field Prelude

theorem normalizeExecution {code : CodeMap}
    (c : Ctx) (fr : Activation) (a initialDst : Limbs) (args : Vector Value Reg.count) (mem : Ram)
    (entry : Atom.All code args mem
      (frameAt .l114930 fr ++ core.atoms .entry c fr ⟨c.dst, a, initialDst⟩))
    (frame : RamWriteFrame fr.original mem (fr.region :: [⟨c.dst.toNat, 40⟩])) :
    ∃ o, LIR.program.Exec (Lift.dialect code) ⟨⟨.l114930, args, mem⟩, []⟩ o ∧
      o.tag = some ⟨64, fr.ret⟩ ∧
      Atom.All code o.values o.store (doneAt fr ++ (floatingRegs c ++
        [.gpr 0 c.dst, .words c.src 64 a, .words c.dst 64 (normalize a)])) ∧
      RamWriteFrame fr.original o.store (fr.region :: [⟨c.dst.toNat, 40⟩]) := by
  have rel : layout.Rel code (fr, c) ⟨.entry, #v[c.dst], (a, initialDst)⟩
      ⟨.l114930, args, mem⟩ := ⟨rfl, ⟨⟨c.dst, a, initialDst⟩, rfl, rfl, entry⟩, frame⟩
  obtain ⟨o, run, ret⟩ := (layout.simulation code (fr, c) (blocks code)).exec
    (exec c.dst (a, initialDst)).sem (a := ⟨⟨.l114930, args, mem⟩, []⟩) ⟨(fr, c), rel, rfl⟩
  obtain ⟨⟨r, s⟩, eq, atoms⟩ := ret.result
  have hr : c.dst = r := congrArg (fun out => out.values[0]) eq
  have hs : (a, normalize a) = s := congrArg Output.store eq
  subst r s
  exact ⟨o, Program.Exec.of_sem run, ret.tag, atoms, ret.frame⟩

end K256.Proofs.Sec1.Serialize.Normalize
