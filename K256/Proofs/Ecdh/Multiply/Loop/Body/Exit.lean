import K256.Proofs.Ecdh.Multiply.Loop.Body.State

namespace K256.Proofs.Generate.Generator.Multiply

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR
  Standards.SECG.DomainParameters.Secp256k1

theorem peerWindowRoundExit {fr : Activation} {a : Registers} {m : Ram} {d k : Nat} {peer : Projective}
    (s : PeerRoundState fr d peer k .l11f6a6 a m) (zero : a[14].get 64 = 0) :
    ∃ b, Reaches .l11f6a6 a m .l11d7d0 b m ∧ PeerRoundState fr d peer k .l11d7d0 b m ∧ b[12] = a[12] := by
  have atoms := s.atoms
  simp only [Fn11c880.frameAt, Fn11c880.frameAtG2, Atom.All, Atom.Holds] at atoms
  have rsp : a[4].get 64 = fr.rsp - 0xcb8 := congrArg (Value.get 64) atoms.1
  have stack := atoms.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have limit := s.memory.locals (0x258,66) (by simp)
  change memLoad m (fr.rsp - 0xcb8 + 0x258) 64 = 66 at limit
  rw [show (fr.rsp - 0xcb8 + 0x258) = fr.rsp - 0xa60 by bv_omega] at limit
  refine ⟨?b, ?reach, ?state, ?kept⟩
  case reach =>
    have compare : program.runBlock (dialect Extracted.programImage) ⟨.l11f6a6,a,m⟩ =
        .jump ⟨.l11f6bf,?c,m⟩ := by
      arithmetic_segment using code_l11f6a6 [rsp,zero,limit]
    have jump : program.runBlock (dialect Extracted.programImage) ⟨.l11f6bf,?c,m⟩ =
        .jump ⟨.l11d7d0,?b,m⟩ := by
      arithmetic_segment using code_l11f6bf []
    refine Star.step (b := ⟨⟨.l11f6bf, ?c, m⟩, []⟩) ?_ (Semantics.Reaches.single ?_)
    · change program.step _ _ = _
      simp only [Program.step, compare, Transfer.next]
    · change program.step _ _ = _
      simp only [Program.step, jump, Transfer.next]
  case state =>
    refine ⟨?_, ?_, ?_, s.memory, s.count, s.pointer⟩
    · exact atoms
    · rintro ⟨i, hi⟩ hm
      have w := s.widths ⟨i, hi⟩ hm
      simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> first | rfl | exact w
    · rintro ⟨i, hi⟩ hm
      have w := s.saved ⟨i, hi⟩ hm
      simp only [Activation.calleeSavedNumbers, List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl <;> first | rfl | exact w
  case kept => rfl

end K256.Proofs.Generate.Generator.Multiply
