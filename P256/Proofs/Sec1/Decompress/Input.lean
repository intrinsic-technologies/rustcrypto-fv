import P256.Proofs.Sec1.Decompress.Input.Prefix
import P256.Proofs.Sec1.Decompress.Input.Finish

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decompress

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Standards.SECG.ECC

theorem input_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} {odd : Bool} (pre : Pre s boundary bytes odd) :
    ∃ fuel t, Advances boundary fuel s t ∧ InputState s t (Encoding.octetsToNat bytes) odd := by
  obtain ⟨n1, t1, r1, h1⟩ := Input.prefix_correct pre
  obtain ⟨n2, t2, r2, h2⟩ := Input.conversion_entry pre h1
  obtain ⟨n3, t3, r3, h3⟩ := Input.conversion_result pre h2
  obtain ⟨n4, t4, r4, h4⟩ := Input.choice pre h3
  obtain ⟨n5, t5, r5, h5⟩ := Input.first_select pre h4
  obtain ⟨n6, t6, r6, h6⟩ := Input.finish pre h5
  exact ⟨n1+n2+n3+n4+n5+n6, t6,
    ((((r1.trans r2).trans r3).trans r4).trans r5).trans r6, h6⟩

end P256.Proofs.Sec1.Decompress
