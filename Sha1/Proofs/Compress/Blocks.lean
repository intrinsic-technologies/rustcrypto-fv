import Sha1.Proofs.Compress.ProducerStubs

namespace Sha1.Proofs.Compress

open X86.Machine X86.UserProcess Machine

theorem block_correct : Machine.BlockCorrect := by
  apply Machine.blockCorrect_of_segment
  intro _ boundary hOutside
  have h0 := (segment000 boundary hOutside).seq (segment001 boundary hOutside)
  have h1 := h0.seq (segment002 boundary hOutside)
  have h2 := h1.seq (segment003 boundary hOutside)
  have h3 := h2.seq (segment004 boundary hOutside)
  have hgroup0 := h3.seq (segments005_014 boundary hOutside)
  have hgroup1 := hgroup0.seq (segments015_026 boundary hOutside)
  have hgroup2 := hgroup1.seq (segments027_038 boundary hOutside)
  have hgroup3 := hgroup2.seq (segments039_050 boundary hOutside)
  have hgroup4 := hgroup3.seq (segments051_060 boundary hOutside)
  have hgroup5 := hgroup4.seq (segments061_071 boundary hOutside)
  have hgroup6 := hgroup5.seq (segments072_082 boundary hOutside)
  exact hgroup6

end Sha1.Proofs.Compress
