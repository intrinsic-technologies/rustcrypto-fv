import P256.Proofs.Program.Fill.Memory
import P256.Proofs.Program.LeafReturn

set_option autoImplicit false

namespace P256.Proofs.Program.Fill

open P256.Proofs.Common.Memory.Fill
open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem finish [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {n reserve fuel : Nat} (hp : CalleePre s boundary 0x11c810 0 n reserve)
    (h : FillState s t n) (hrip : t.RIP = 0x11c854) (hexec : Advances boundary fuel s t) :
    ∃ final, CalleeResult s final boundary n reserve ∧
      (∀ i < n, final.external[s.regValue .rdi + BitVec.ofNat 64 i]? = some 0) ∧
      AgreesExcept (fillComponents s n ++ [.reg 4, .rip]) s final := by
  have ag : AgreesExcept (leafComponents (s.regValue .rdi) n [0,1,2,6,8,7]) s t :=
    h.agrees.mono (by simp [fillComponents, registerComponents, leafComponents])
  obtain ⟨u, result, mem, _, finalAg⟩ := leaf_return [0,1,2,6,8,7]
    (by decide) (by decide) hp hexec h.ready (codeOffset := 0x1c854)
    hrip (by decide) (by decide +kernel) ag
  refine ⟨u, result, ?_, finalAg.mono ?_⟩
  · intro i hi
    rw [mem]
    exact h.fill i hi
  · simp [leafComponents, fillComponents, registerComponents]

end P256.Proofs.Program.Fill
