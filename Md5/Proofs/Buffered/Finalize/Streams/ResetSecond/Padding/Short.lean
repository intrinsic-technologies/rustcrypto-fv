import Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Padding.Branch

namespace Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Padding

open Md5.Spec Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem short [Bindings] {variant : Variant} {boundary : ReturnBoundary} {message : ByteArray} {s : RamState}
    (hOutside : ¬ InProgram boundary.rip) (h : Prepared message s variant)
    (hshort : message.size % 64 < 56) :
    ∃ t, Transition boundary s t variant ∧ Padded message t variant := by
  obtain ⟨t, ht, hready, hcode, hrip, hframe⟩ := branch h.ready h.code
    hOutside h.rip (by omega : message.size % 64 < 64) h.remaining
  have hsp : stackPtr t = stackPtr s := hframe.read (n := 64) (r := 4) (by simp)
  have hmem : t.external = s.external := hframe.external (by simp [Component.Covers])
  have hlocal : AgreesExcept (variant.toKind.changes s) s t :=
    hframe.mono (by simp [Kind.changes])
  refine ⟨t, ⟨⟨2, ht⟩, hlocal⟩, h.toStorage.of_agrees hframe hsp,
    hready, hcode, ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [ite_eq_left hshort] using hrip
  · intro i hi
    rw [hsp, hmem]
    simpa only [ite_eq_left hshort] using h.first i (by omega)
  · simpa only [hsp, hmem, paddedBuffer, ite_eq_left hshort] using h.buffer
  · exact (hframe.read (by simp)).trans h.blocks
  · exact (hframe.read (by simp)).trans h.position

end Md5.Proofs.Buffered.Finalize.Streams.ResetSecond.Padding
