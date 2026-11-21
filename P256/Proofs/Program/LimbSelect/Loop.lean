import P256.Proofs.Program.LimbSelect.Loop.Iteration

set_option autoImplicit false

namespace P256.Proofs.Program.LimbSelect

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem loop [Bindings] {s t : RamState} {boundary : ReturnBoundary} {select : Bool}
    (hp : Pre s boundary) (h : LoopState s t select 0) (hrip : t.RIP = 0x1191f0) :
    ∃ u, (∃ fuel, Advances boundary fuel t u) ∧ LoopState s u select 4 ∧
      u.RIP = 0x11920a := by
  obtain ⟨a, ha, hsa, hia⟩ := iteration hp h (by decide) hrip
  obtain ⟨b, hb, hsb, hib⟩ := iteration hp hsa (by decide) hia
  obtain ⟨c, hc, hsc, hic⟩ := iteration hp hsb (by decide) hib
  obtain ⟨d, hd, hsd, hid⟩ := iteration hp hsc (by decide) hic
  exact ⟨d, ⟨32, ((ha.trans hb).trans hc).trans hd⟩, hsd, hid⟩

end P256.Proofs.Program.LimbSelect
