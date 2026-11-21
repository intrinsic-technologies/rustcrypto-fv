import Sha1.Proofs.Streaming.Invariant

namespace Sha1.Proofs.Entry.UpdateFinalize

open Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha1.Proofs.Buffered Sha1.Proofs.Streaming.UpdateFinalize

theorem readOnly_frame [Bindings] {initial s t : RamState} (h : Frame initial s)
    (hr : ReadyToStep t) (hc : CodeIn Extracted.programImage t) (hd : DirectionFlagUnset t)
    (hsp : stackPtr t = stackPtr s) (hm : t.external = s.external)
    (hf : fixedPart t = fixedPart s) : Frame initial t := by
  have word (k : Nat) : stackWord t k = stackWord s k := by
    simp only [stackWord, hsp, Operand.read, hm]
  exact ⟨hr, hc, hd, hsp.trans h.stack, (word _).trans h.output, (word _).trans h.pointers,
    (word _).trans h.lengths, (word _).trans h.savedRbx, (word _).trans h.savedR12,
    (word _).trans h.savedR13, (word _).trans h.savedR14, (word _).trans h.savedR15,
    (word _).trans h.savedRbp, (word _).trans h.returnSlot,
    fun a ha ↦ by rw [hm]; exact h.memory a ha,
    fun a ha ↦ by rw [hm]; exact h.grows a ha, hf.trans h.fixed⟩

theorem readOnly_absorbed {s t : RamState} {base : BitVec 64} {message : ByteArray}
    (h : Absorbed base message s) (hm : t.external = s.external) : Absorbed base message t := by
  exact ⟨hm ▸ h.state, hm ▸ h.tail, by simpa only [Operand.read, hm] using h.position,
    by simpa only [Operand.read, hm] using h.blocks⟩

end Sha1.Proofs.Entry.UpdateFinalize
