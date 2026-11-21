import K256.Proofs.Common.Lift.Footprint
import K256.Proofs.Common.Lift.Rep
import K256.Proofs.Sec1.LIR.Generated.Footprints
import K256.Proofs.Generate.LIR.Generated.Footprints
import X86Proofs.Instructions.Bt.Generated.RR.Triple

namespace K256.Proofs.Ecdh.LIR

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift

open K256.Proofs.Sec1.LIR K256.Proofs.Generate.LIR

theorem btR32R32Effect_footprint (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    EffectFootprint p (btR32R32Effect p len dst src) ([.gpr dst, .gpr src, .flag .CF, .flag .PF, .flag .AF, .flag .ZF, .flag .SF, .flag .OF]) []
      [.flags, .rip] :=
  ⟨.ofLocal btR32R32Effect_local, by lift_reads [btR32R32Effect, btFlags], by lift_closed, by lift_params,
    by lift_components [btR32R32Effect_components]⟩

theorem btR32R32Effect_fresh (p : BitVec 64) (len : Nat) (dst : BitVec 5) (src : BitVec 5) :
    ∀ f ∈ ([.CF] : List StatusFlag),
      FlagFresh [] (btR32R32Effect p len dst src) f := by
  lift_fresh [btR32R32Effect, btFlags]

end K256.Proofs.Ecdh.LIR
