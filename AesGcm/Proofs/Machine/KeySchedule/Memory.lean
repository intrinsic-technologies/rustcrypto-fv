import AesGcm.Proofs.AES16.Layout

namespace AesGcm.Proofs.Machine.KeySchedule
open Standards.NIST.AES Prelude X86 X86.Machine X86Proofs X86Proofs.Refine

def narrowScheduleWords (v : Variant) (key : Vector UInt8 v.keyBytes) :
    Vector (BitVec 16) (8 * (v.Nr + 1)) :=
  Vector.ofFn fun i ↦ AES16.expectedKey v key ⟨i.val / 8, by omega⟩ ⟨i.val % 8, by omega⟩

theorem narrowScheduleWords_in {v : Variant} {key : Vector UInt8 v.keyBytes}
    {base : BitVec 64} {mem : Ram} (h : AES16.ScheduleIn v key base mem) :
    WordsAt mem base 16 (narrowScheduleWords v key) := by
  intro i hi
  simp only [wordAddr, Nat.reduceDiv, narrowScheduleWords, Vector.getElem_ofFn]
  have he : 2 * i = 16 * (i / 8) + 2 * (i % 8) := by omega
  rw [he]
  exact h ⟨i / 8, by omega⟩ ⟨i % 8, by omega⟩

theorem widenedScheduleWords_in {v : Variant} {key : Vector UInt8 v.keyBytes}
    {base : BitVec 64} {mem : Ram}
    (h : WordsAt mem base 64 ((narrowScheduleWords v key).map Fixslice16.widenWord))
    (r : Fin (v.Nr + 1)) (p : Fin 8) :
    memLoad mem (base + BitVec.ofNat 64 (64 * r.val + 8 * p.val)) 64 =
      expectedKey v key r p := by
  have he := h (8 * r.val + p.val) (by have := r.isLt; have := p.isLt; omega)
  simp only [wordAddr, Nat.reduceDiv, Vector.getElem_map, narrowScheduleWords,
    Vector.getElem_ofFn] at he
  have hr : (8 * r.val + p.val) / 8 = r.val := by omega
  have hp : (8 * r.val + p.val) % 8 = p.val := by omega
  simp only [hr, hp] at he
  have ha : 8 * (8 * r.val + p.val) = 64 * r.val + 8 * p.val := by omega
  rw [ha] at he
  rw [← widenPlanes_expectedKey v key r]
  exact he

end AesGcm.Proofs.Machine.KeySchedule
