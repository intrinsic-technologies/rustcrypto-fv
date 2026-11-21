import Md5.Proofs.Block.Execution

namespace Md5.Proofs.Streaming

open X86 X86.Machine X86.UserProcess X86Proofs

theorem advances_loop [Bindings] {boundary : ReturnBoundary}
    {invariant : Nat → RamState → Prop} {start finish : Nat}
    (hbound : start ≤ finish)
    (hstep : ∀ i, start ≤ i → i < finish → ∀ s, invariant i s →
      ∃ fuel t, Advances boundary fuel s t ∧ invariant (i + 1) t)
    {s : RamState} (hs : invariant start s) :
    ∃ fuel t, Advances boundary fuel s t ∧ invariant finish t := by
  have loop (count : Nat) (hcount : start + count ≤ finish) :
      ∃ fuel t, Advances boundary fuel s t ∧ invariant (start + count) t := by
    induction count with
    | zero => exact ⟨0, s, (advances_zero boundary s s).mpr rfl, hs⟩
    | succ count ih =>
      obtain ⟨fuel, t, hrun, ht⟩ := ih (by omega)
      obtain ⟨steps, u, hrun', hu⟩ := hstep (start + count) (by omega) (by omega) t ht
      exact ⟨fuel + steps, u, hrun.trans hrun', hu⟩
  simpa only [Nat.add_sub_of_le hbound] using loop (finish - start) (by omega)

end Md5.Proofs.Streaming
