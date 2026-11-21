import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Rows.Values
import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Rows.FourthValues

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Montgomery.Rows

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem rows_correct [Bindings] {entry : BitVec 64} {boundary : ReturnBoundary}
    {a b : Vector (BitVec 64) 4} {s : RamState}
    (pre : Pre entry boundary a b s) : ∃ t, Result entry boundary a b s t := by
  obtain ⟨fuel, t, run, ready, loaded, frame, ⟨trace⟩⟩ := execution pre
  have hs := trace_fourthState pre trace
  obtain ⟨input, high, carry, modulus⟩ := fourthRow_values hs.saved hs.digit hs.first
    hs.second hs.low hs.mid hs.high hs.carry trace.e9 trace.e10 trace.e11 trace.e12
  refine ⟨t, ⟨⟨fuel, run⟩, ready, loaded, ?_, pre.memory.of_scratch frame, frame,
    Reduction.scratch_rsp frame, Reduction.scratch_rdi frame, input, modulus, high, carry⟩⟩
  have ip := trace.e12.rip
  change t.RIP = (entry+1040#64)+32#64 at ip
  simpa only [BitVec.add_assoc, show 1040#64+32#64 = 1072#64 by decide +kernel] using ip

end P256.Proofs.Sec1.SquareRoot.Montgomery.Rows
