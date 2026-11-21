import P256.Proofs.Sec1Serialize.Tail.Initialize.Zero.Second.Store
import P256.Proofs.Sec1Serialize.Tail.Initialize.Zero.Second.Index

set_option autoImplicit false

namespace P256.Proofs.Sec1Serialize

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

variable [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} {infinity : Bool}

theorem prepare_zero_second (pre : CalleePre s boundary 0x110d70 72 65 328)
    (h : Preparing s t boundary bytes infinity) (rip : t.RIP = 0x111141) :
    ∃ u, Preparing s u boundary bytes infinity ∧ u.RIP = 0x11118e ∧
      u.regValue .rax = t.regValue .rax := by
  obtain ⟨t0, h0, r0, a0⟩ := h.second_zero8 pre 0x11141 232 (.sib 4 none 0 (.d8 80))
    (by decide) rfl rfl (by decide) (by decide)
    (by intro; rfl) (by decide) (by decide +kernel) rip
  obtain ⟨t1, h1, r1, a1⟩ := h0.second_zero64 pre 0x11146 240 (.sib 4 none 0 (.d8 72))
    (by decide) rfl rfl (by decide) (by decide) (by decide)
    (by intro; rfl) (by decide) (by decide +kernel) r0
  obtain ⟨t2, h2, r2, a2⟩ := h1.second_zero64 pre 0x1114f 248 (.sib 4 none 0 (.d8 64))
    (by decide) rfl rfl (by decide) (by decide) (by decide)
    (by intro; rfl) (by decide) (by decide +kernel) r1
  obtain ⟨t3, h3, r3, a3⟩ := h2.second_zero64 pre 0x11158 256 (.sib 4 none 0 (.d8 56))
    (by decide) rfl rfl (by decide) (by decide) (by decide)
    (by intro; rfl) (by decide) (by decide +kernel) r2
  obtain ⟨t4, h4, r4, a4⟩ := h3.second_zero64 pre 0x11161 264 (.sib 4 none 0 (.d8 48))
    (by decide) rfl rfl (by decide) (by decide) (by decide)
    (by intro; rfl) (by decide) (by decide +kernel) r3
  obtain ⟨t5, h5, r5, a5⟩ := h4.second_zero64 pre 0x1116a 272 (.sib 4 none 0 (.d8 40))
    (by decide) rfl rfl (by decide) (by decide) (by decide)
    (by intro; rfl) (by decide) (by decide +kernel) r4
  obtain ⟨t6, h6, r6, a6⟩ := h5.second_zero64 pre 0x11173 280 (.sib 4 none 0 (.d8 32))
    (by decide) rfl rfl (by decide) (by decide) (by decide)
    (by intro; rfl) (by decide) (by decide +kernel) r5
  obtain ⟨t7, h7, r7, a7⟩ := h6.second_zero64 pre 0x1117c 288 (.sib 4 none 0 (.d8 24))
    (by decide) rfl rfl (by decide) (by decide) (by decide)
    (by intro; rfl) (by decide) (by decide +kernel) r6
  obtain ⟨t8, h8, r8, a8⟩ := h7.second_zero64 pre 0x11185 296 (.sib 4 none 0 (.d8 16))
    (by decide) rfl rfl (by decide) (by decide) (by decide)
    (by intro; rfl) (by decide) (by decide +kernel) r7
  exact ⟨t8, h8, r8, a8.trans (a7.trans (a6.trans (a5.trans (a4.trans (a3.trans (a2.trans (a1.trans a0)))))))⟩

theorem prepare_zero_second_index (pre : CalleePre s boundary 0x110d70 72 65 328)
    (h : Preparing s t boundary bytes infinity) (rip : t.RIP = 0x111141)
    (rax : t.regValue .rax = if infinity then 1 else 0) :
    ∃ u, SelectionEntry s u boundary bytes infinity := by
  obtain ⟨u, hu, ip, a⟩ := prepare_zero_second pre h rip
  exact prepare_index pre hu ip (a.trans rax)

end P256.Proofs.Sec1Serialize
