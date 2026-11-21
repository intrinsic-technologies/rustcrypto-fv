import P256.Proofs.Projective.Multiply.Machine.Lookup.State
import P256.Proofs.Projective.Multiply.Machine.Lookup.Scan.Round0
import P256.Proofs.Projective.Multiply.Machine.Lookup.Scan.Round1
import P256.Proofs.Projective.Multiply.Machine.Lookup.Scan.Round2
import P256.Proofs.Projective.Multiply.Machine.Lookup.Scan.Round3
import P256.Proofs.Projective.Multiply.Machine.Lookup.Scan.Round4
import P256.Proofs.Projective.Multiply.Machine.Lookup.Scan.Round5
import P256.Proofs.Projective.Multiply.Machine.Lookup.Scan.Round6
import P256.Proofs.Projective.Multiply.Machine.Lookup.Scan.Round7

set_option autoImplicit false


namespace P256.Proofs.Projective.Multiply.Machine.Lookup

open Program Field ProjectiveLookup P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Scanning

theorem scan [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {table : Fin 8 → Projective} {digit : BitVec 8}
    (pre : CalleePre s boundary 0x1044a0 768 96 496)
    (input : TableAt s (s.regValue .rsi) table) (state : ScanState s t digit) :
    ∃ fuel u, Advances boundary fuel t u ∧ SignState s u table digit := by
  have initial : RoundState s t table digit 0 :=
    ⟨state.toFrameState, state.rip,
      scanPrefix_zero table (digitMagnitude digit) ▸ state.value,
      state.magnitude, fun _ => state.r13, state.rbp, state.r14,
      (by intro h; omega), state.digit, state.output⟩
  obtain ⟨n0,t0,run0,state0⟩ := round0 pre input initial
  obtain ⟨n1,t1,run1,state1⟩ := round1 pre input state0
  obtain ⟨n2,t2,run2,state2⟩ := round2 pre input state1
  obtain ⟨n3,t3,run3,state3⟩ := round3 pre input state2
  obtain ⟨n4,t4,run4,state4⟩ := round4 pre input state3
  obtain ⟨n5,t5,run5,state5⟩ := round5 pre input state4
  obtain ⟨n6,t6,run6,state6⟩ := round6 pre input state5
  obtain ⟨n7,t7,run7,state7⟩ := round7 pre input state6
  refine ⟨n0+n1+n2+n3+n4+n5+n6+n7,t7,(((((((run0.trans run1).trans run2).trans run3).trans run4).trans run5).trans run6).trans run7),state7.toFrameState,state7.rip,?_,state7.r14,state7.digit,state7.output⟩
  exact scanPrefix_eight table (digitMagnitude digit) ▸ state7.value

end P256.Proofs.Projective.Multiply.Machine.Lookup
