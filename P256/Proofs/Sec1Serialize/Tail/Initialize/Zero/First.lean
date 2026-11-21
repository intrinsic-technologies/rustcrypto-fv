import P256.Proofs.Sec1Serialize.Tail.Initialize.Zero.First.Store

set_option autoImplicit false

namespace P256.Proofs.Sec1Serialize

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

variable [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} {infinity : Bool}

theorem prepare_zero_first (pre : CalleePre s boundary 0x110d70 72 65 328)
    (entry : EncodedEntry s t boundary bytes infinity) :
    ∃ u, Preparing s u boundary bytes infinity ∧ u.RIP = 0x111134 := by
  have h : Zeroing s t boundary bytes infinity 119 :=
    ⟨entry.state, entry.execution, entry.destination, entry.source,
      entry.savedInput, entry.inputFlag,
      fun k hk hle => by omega⟩
  obtain ⟨t0, h0, r0⟩ := h.zero8 pre 0x110cc 120 (.sib 4 none 0 (.d32 192))
    (by decide) rfl rfl (by decide) (by decide)
    (by intro; rfl) (by decide) (by decide +kernel) entry.rip
  obtain ⟨t1, h1, r1⟩ := h0.zero64 pre 0x110d4 128 (.sib 4 none 0 (.d32 184))
    (by decide) rfl rfl (by decide) (by decide) (by decide)
    (by intro; rfl) (by decide) (by decide +kernel) r0
  obtain ⟨t2, h2, r2⟩ := h1.zero64 pre 0x110e0 136 (.sib 4 none 0 (.d32 176))
    (by decide) rfl rfl (by decide) (by decide) (by decide)
    (by intro; rfl) (by decide) (by decide +kernel) r1
  obtain ⟨t3, h3, r3⟩ := h2.zero64 pre 0x110ec 144 (.sib 4 none 0 (.d32 168))
    (by decide) rfl rfl (by decide) (by decide) (by decide)
    (by intro; rfl) (by decide) (by decide +kernel) r2
  obtain ⟨t4, h4, r4⟩ := h3.zero64 pre 0x110f8 152 (.sib 4 none 0 (.d32 160))
    (by decide) rfl rfl (by decide) (by decide) (by decide)
    (by intro; rfl) (by decide) (by decide +kernel) r3
  obtain ⟨t5, h5, r5⟩ := h4.zero64 pre 0x11104 160 (.sib 4 none 0 (.d32 152))
    (by decide) rfl rfl (by decide) (by decide) (by decide)
    (by intro; rfl) (by decide) (by decide +kernel) r4
  obtain ⟨t6, h6, r6⟩ := h5.zero64 pre 0x11110 168 (.sib 4 none 0 (.d32 144))
    (by decide) rfl rfl (by decide) (by decide) (by decide)
    (by intro; rfl) (by decide) (by decide +kernel) r5
  obtain ⟨t7, h7, r7⟩ := h6.zero64 pre 0x1111c 176 (.sib 4 none 0 (.d32 136))
    (by decide) rfl rfl (by decide) (by decide) (by decide)
    (by intro; rfl) (by decide) (by decide +kernel) r6
  obtain ⟨t8, h8, r8⟩ := h7.zero64 pre 0x11128 184 (.sib 4 none 0 (.d32 128))
    (by decide) rfl rfl (by decide) (by decide) (by decide)
    (by intro; rfl) (by decide) (by decide +kernel) r7
  exact ⟨t8, h8.finish, r8⟩

end P256.Proofs.Sec1Serialize
