import P256.Proofs.ReadBe.Entry
import P256.Proofs.ReadBe.Loop
import P256.Proofs.ReadBe.Finish

set_option autoImplicit false

namespace P256.Proofs.ReadBe

open P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem read_be_correct [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {input : ByteArray} (pre : Pre s boundary)
    (bytes : (registerRegion s .rdi 32).HasBytes s.external input) :
    ∃ t, Result s t boundary input := by
  obtain ⟨s0, n0, a0, h0⟩ := entry_correct pre bytes
  obtain ⟨s1, n1, a1, h1⟩ := loop_step pre h0 (by decide)
  obtain ⟨s2, n2, a2, h2⟩ := loop_step pre h1 (by decide)
  obtain ⟨s3, n3, a3, h3⟩ := loop_step pre h2 (by decide)
  obtain ⟨s4, n4, a4, h4⟩ := loop_step pre h3 (by decide)
  exact finish_correct pre h4 ⟨_, (((a0.trans a1).trans a2).trans a3).trans a4⟩

end P256.Proofs.ReadBe
