import ChaCha20Poly1305.Proofs.Encrypt.Prefix.Allocate.CopyCall
import ChaCha20Poly1305.Proofs.Encrypt.Prefix.Allocate.CopyPost

namespace ChaCha20Poly1305.Proofs.Encrypt.Prefix

open ChaCha20Poly1305.Spec ChaCha20Poly1305.Spec.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs Wrapper

theorem outside_memcpy {a : BitVec 64} (h : ¬ InProgram a) :
    a.toNat < 0x102dc0 ∨ 0x102def ≤ a.toNat := by
  apply Classical.byContradiction
  intro hn
  have hlo : 0x102dc0 ≤ a.toNat := by omega
  have hhi : a.toNat < 0x102def := by omega
  apply h
  have hs : Extracted.textBytes.size = 11759 := by decide
  have hp := MemoryRoutines.Machine.text_address_in_program (a.toNat - 0x100000) (by omega)
  have he : Extracted.textAddress + BitVec.ofNat 64 (a.toNat - 0x100000) = a := by
    apply BitVec.eq_of_toNat_eq
    have h0 : Extracted.textAddress.toNat = 0x100000 := rfl
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, h0]
    have := a.isLt
    omega
  rwa [he] at hp

theorem copy_setup_word {initial s t : RamState} {k : Nat} {v : BitVec 64}
    (st : EntryStack initial) (hk : 8 ≤ k) (hk' : k ≤ 168)
    (he : AgreesExcept (copySetupChanges (stackPtr initial)) s t)
    (hw : (localWord initial k).Word64At s.external v) :
    (localWord initial k).Word64At t.external v := by
  have room := st.room
  have top := st.top
  apply word_preserved (by change _ - k + 8 < 2^32; omega) hw
  intro a ha
  apply he.byte
  intro c hc hac
  simp only [copySetupChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact hac.elim
  obtain ⟨i, hi, rfl⟩ := hac
  change _ - k ≤ _ ∧ _ < _ - k + 8 at ha
  rw [slot_toNat (by omega) st.top (by omega)] at ha
  omega

end ChaCha20Poly1305.Proofs.Encrypt.Prefix
