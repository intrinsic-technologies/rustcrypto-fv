import K256.Proofs.Ecdh.Multiply.Bases.Start.Return

namespace K256.Proofs.Generate.Generator.Multiply.Prepare.Bases

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR
  Standards.SECG.DomainParameters.Secp256k1

theorem peerStart {fr : Activation} {initial a : Registers} {d : Nat} {peer : Projective} {m : Ram}
    (e : PeerCoreEntry fr initial d peer) (s : SplitState fr a m d) :
    ∃ c n, Reaches .l11c9e7 a m .l11ca7f c n ∧ PeerComparedInput fr c n d peer := by
  obtain ⟨b,dispatch,args⟩ := Start.peerDispatch e s
  have frame := Start.peerMemoryFrame e s.frame
  obtain ⟨out,ret⟩ := Start.peerCall e frame args (Start.peerCalleeEntry e frame args)
  exact ⟨out.values,out.store,
    @Sample.reachesAfterSampleCall ⟨.l11c9e7,a,m⟩ ⟨.l10e010,b,Start.memory fr m d⟩
      .l11ca7f 0x11ca7f out dispatch ret.run ret.tag [],
    Start.peerComparedInput e (Start.peerInitialContext e s) args.toScalarRegisters ret⟩

end K256.Proofs.Generate.Generator.Multiply.Prepare.Bases
