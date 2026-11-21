import Md5.Proofs.Buffered.FinalizeReset.Pad.Long
import Md5.Proofs.Buffered.FinalizeReset.Finish

namespace Md5.Proofs.Buffered.FinalizeReset

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem finish {variant : Variant} [Bindings] {boundary : ReturnBoundary} {message : ByteArray}
    {s : RamState} (h : Padded message s variant) (hout : ¬ InProgram boundary.rip) :
    ∃ t, Post boundary message s t variant := by
  obtain ⟨nlength, u, hlength, hready, hcode, hl⟩ :=
    Length.run h.ready h.code h.toStorage hout h.rip
  have hlf := Length.effect_agrees hl
  have hsu := agrees_storage h.toStorage hlf
  obtain ⟨ncopy, v, hcopy, hc⟩ := Copy.run .finalBlock hready hcode hsu hout hl.rip
  obtain ⟨t, ht⟩ := compress_export (finalBlock_of_copy h hl hc) hout
  exact ⟨t, (ht.prepend hsu hcopy (Copy.agrees_reset hc.agrees)).prepend
    h.toStorage hlength hlf⟩

theorem run {variant : Variant} [Bindings] {boundary : ReturnBoundary} {message : ByteArray}
    {s : RamState} (h : Pre boundary message s variant) : ∃ t, Post boundary message s t variant := by
  obtain ⟨p, hp⟩ := Prepare.run h
  have hpad : ∃ fuel u, Advances boundary fuel s u ∧ Padded message u variant ∧
      AgreesExcept (changes s) s u := by
    by_cases hs : message.size % 64 < 56
    · exact pad_short h hp hs
    · exact pad_long h hp (by omega)
  obtain ⟨fuel, u, hu, hpadded, hframe⟩ := hpad
  obtain ⟨t, ht⟩ := finish hpadded h.boundaryOutside
  exact ⟨t, ht.prepend h.toStorage hu hframe⟩

end Md5.Proofs.Buffered.FinalizeReset
