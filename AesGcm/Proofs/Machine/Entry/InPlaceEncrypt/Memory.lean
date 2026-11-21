import AesGcm.Proofs.Machine.Entry.InPlaceEncrypt.Append
import AesGcm.Proofs.Machine.Runtime.TagCopy

namespace AesGcm.Proofs.Machine.Entry.InPlaceEncrypt

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

def tailMemory (args : Values Value Reg.count) (mem : Ram) : Ram :=
  let sp := args[4].get 64
  let copied := copyTagWords mem (sp + 32) (sp + 16)
  if (args[3].get 64).toNat + 16 ≤ (args[5].get 64).toNat then
    copyTagWords copied (args[14].get 64 + args[3].get 64) (sp + 32)
  else copied

def tailFootprint (args : Values Value Reg.count) : List MemoryRegion :=
  span (args[4].get 64 + 32) 16 ::
    if (args[3].get 64).toNat + 16 ≤ (args[5].get 64).toNat then
      [span (args[14].get 64 + args[3].get 64) 16] else []

theorem tailMemory_eq (args : Values Value Reg.count) (mem : Ram) :
    tailMemory args mem =
      (if (args[3].get 64).toNat + 16 ≤ (args[5].get 64).toNat then
        appendMemory args (tagScratchMemory args mem) else tagScratchMemory args mem) := by
  simp only [tailMemory, appendMemory, tagScratchMemory, copyTagWords,
    BitVec.add_assoc, BitVec.reduceAdd]
  rfl

theorem tailMemory_frame (args : Values Value Reg.count) (mem : Ram)
    (hstack : (args[4].get 64 + 32).toNat + 16 ≤ 2^64)
    (hbuffer : (args[3].get 64).toNat + 16 ≤ (args[5].get 64).toNat →
      (args[14].get 64 + args[3].get 64).toNat + 16 ≤ 2^64) :
    RamWriteFrame mem (tailMemory args mem) (tailFootprint args) := by
  have hs := copyTagWords_frame mem (args[4].get 64 + 32) (args[4].get 64 + 16) hstack
  have hs' : RamWriteFrame mem
      (copyTagWords mem (args[4].get 64 + 32) (args[4].get 64 + 16))
      (tailFootprint args) := by
    apply (RamWriteFrame.refl mem (tailFootprint args)).trans hs
    intro r hr
    rcases List.mem_singleton.mp hr with rfl
    exact ⟨_, List.mem_cons_self, Nat.le_refl _, Nat.le_refl _⟩
  unfold tailMemory
  split
  · rename_i hfit
    apply hs'.trans (copyTagWords_frame _ _ _ (hbuffer hfit))
    intro r hr
    rcases List.mem_singleton.mp hr with rfl
    refine ⟨_, ?_, Nat.le_refl _, Nat.le_refl _⟩
    simp [tailFootprint, hfit]
  · exact hs'

theorem tailMemory_tag (args : Values Value Reg.count) (mem : Ram) (tag : ByteArray)
    (hbytes : (span (args[4].get 64 + 16) 16).HasBytes mem tag)
    (hfit : (args[3].get 64).toNat + 16 ≤ (args[5].get 64).toNat) :
    (span (args[14].get 64 + args[3].get 64) 16).HasBytes (tailMemory args mem) tag := by
  simp only [tailMemory, hfit, ↓reduceIte]
  apply copyTagWords_hasBytes
  exact copyTagWords_hasBytes _ _ _ _ hbytes

theorem tailFootprint_outside (args : Values Value Reg.count)
    (hbuffer : (args[14].get 64).toNat + (args[3].get 64).toNat < 2^64)
    (hstack : (args[14].get 64).toNat + (args[3].get 64).toNat ≤
        (args[4].get 64 + 32).toNat ∨
      (args[4].get 64 + 32).toNat + 16 ≤ (args[14].get 64).toNat) :
    Outside (tailFootprint args) (args[14].get 64) (args[3].get 64).toNat := by
  refine ⟨by omega, ?_⟩
  intro region hregion
  simp only [tailFootprint, List.mem_cons] at hregion
  rcases hregion with rfl | hregion
  · exact hstack
  · split at hregion
    next =>
      rcases List.mem_singleton.mp hregion with rfl
      left
      change (args[14].get 64).toNat + (args[3].get 64).toNat ≤
        (args[14].get 64 + args[3].get 64).toNat
      rw [BitVec.toNat_add, Nat.mod_eq_of_lt hbuffer]
      exact Nat.le_refl _
    next => simp only [List.not_mem_nil] at hregion

end AesGcm.Proofs.Machine.Entry.InPlaceEncrypt
