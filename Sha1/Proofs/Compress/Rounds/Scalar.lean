import Sha1.Proofs.Compress.Rounds.State

namespace Sha1.Proofs.Compress.Rounds

open Standards.NIST.SHA1

attribute [local irreducible] workingAfter messageSchedule

theorem workingAfter_step_a_values (M : Vector (BitVec 32) 16) (H : Vector (BitVec 32) 5)
    (n : Nat) (hn : n + 4 < 80) :
    (workingAfter M H (n + 5)).a =
      ((workingAfter M H (n + 4)).a).rotateLeft 5 +
      f ⟨n + 4, hn⟩ (workingAfter M H (n + 3)).a
        (((workingAfter M H (n + 2)).a).rotateLeft 30)
        (((workingAfter M H (n + 1)).a).rotateLeft 30) +
      ((workingAfter M H n).a).rotateLeft 30 + K ⟨n + 4, hn⟩ +
      scheduleWord M ⟨n + 4, hn⟩ := by
  rw [workingAfter_step M H (n + 4) hn]
  change ROTL 5 (workingAfter M H (n + 4)).a +
    f ⟨n + 4, hn⟩ (workingAfter M H (n + 4)).b
      (workingAfter M H (n + 4)).c (workingAfter M H (n + 4)).d +
    (workingAfter M H (n + 4)).e + K ⟨n + 4, hn⟩ +
    scheduleWord M ⟨n + 4, hn⟩ = _
  rw [workingAfter_step_b M H (n + 3) (by omega),
    workingAfter_step_c M H (n + 3) (by omega),
    workingAfter_step_b M H (n + 2) (by omega),
    workingAfter_step_d M H (n + 3) (by omega),
    workingAfter_step_c M H (n + 2) (by omega),
    workingAfter_step_b M H (n + 1) (by omega),
    workingAfter_step_e M H (n + 3) (by omega),
    workingAfter_step_d M H (n + 2) (by omega),
    workingAfter_step_c M H (n + 1) (by omega),
    workingAfter_step_b M H n (by omega)]
  simp only [sha1Rotl_eq_rotateLeft 5 _ (by decide),
    sha1Rotl_eq_rotateLeft 30 _ (by decide)]


theorem compress_eq_a_values (M : Vector (BitVec 32) 16) (H : Vector (BitVec 32) 5) :
    compress H M = #v[
      H[0] + (workingAfter M H 80).a,
      H[1] + (workingAfter M H 79).a,
      H[2] + ((workingAfter M H 78).a).rotateLeft 30,
      H[3] + ((workingAfter M H 77).a).rotateLeft 30,
      H[4] + ((workingAfter M H 76).a).rotateLeft 30] := by
  have hb : (workingAfter M H 80).b = (workingAfter M H 79).a :=
    workingAfter_step_b M H 79 (by decide)
  have hc : (workingAfter M H 80).c = ((workingAfter M H 78).a).rotateLeft 30 := by
    rw [workingAfter_step_c M H 79 (by decide),
      workingAfter_step_b M H 78 (by decide), sha1Rotl_eq_rotateLeft 30 _ (by decide)]
  have hd : (workingAfter M H 80).d = ((workingAfter M H 77).a).rotateLeft 30 := by
    rw [workingAfter_step_d M H 79 (by decide), workingAfter_step_c M H 78 (by decide),
      workingAfter_step_b M H 77 (by decide), sha1Rotl_eq_rotateLeft 30 _ (by decide)]
  have he : (workingAfter M H 80).e = ((workingAfter M H 76).a).rotateLeft 30 := by
    rw [workingAfter_step_e M H 79 (by decide), workingAfter_step_d M H 78 (by decide),
      workingAfter_step_c M H 77 (by decide), workingAfter_step_b M H 76 (by decide),
      sha1Rotl_eq_rotateLeft 30 _ (by decide)]
  rw [compress_eq_add_workingAfter, hb, hc, hd, he]

end Sha1.Proofs.Compress.Rounds
