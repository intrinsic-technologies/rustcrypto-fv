import Hkdf.Proofs.NewExpand.Extract.Update.Bulk
import Hkdf.Proofs.NewExpand.Extract.Update.CopyTail
import Hkdf.Proofs.NewExpand.Extract.Update.Dispatch

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Extract

open Hkdf.Spec Hkdf.Spec.Program Hkdf.Proofs.Common Hkdf.Proofs.Common.Machine
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Update

theorem update [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {salt : Option ByteArray} {ikm : ByteArray} (pre : ExtractPre initial boundary salt ikm) (state : Initialized initial s boundary salt) :
    ∃ t, Updated initial t boundary salt ikm := by
  obtain ⟨u, run, ready, rip, branch⟩ := dispatch (supportedMachine_readyToStep state.machine)
    (programText_slice (programLoaded_codeIn state.loaded) 0xfc63 branchBytes (by decide) (by decide +kernel))
    state.rip (boundary_ne_program pre.call.outerBoundary (inProgram_of_textOffset 0xfc67 (by decide)))
    (boundary_ne_program pre.call.outerBoundary (inProgram_of_textOffset 0xfc69 (by decide)))
    (boundary_ne_program pre.call.outerBoundary (inProgram_of_textOffset 0xfc84 (by decide)))
  have noMem : ∀ c ∈ [Component.flags,.rip], ∀ a, ¬ c.Covers a := by simp [Component.Covers]
  have frame := registerFrame pre state.toFrame run ready branch noMem (by decide) (by decide) (by decide) (by decide)
  have hmac := state.hmac.of_copy (dest := base initial + 120) (t := u)
    (fun _ _ => by rw [branch.external noMem])
  have ptr : u.regValue .r15 = initial.regValue .rcx := (branch.read (n := 64) (r := 15) (by decide)).trans state.ikmPtr
  have len : u.regValue .r14 = initial.regValue .r8 := (branch.read (n := 64) (r := 14) (by decide)).trans state.ikmLen
  rw [state.ikmLen, pre.ikmLength] at rip
  by_cases small : ikm.size < 64
  · simp only [small, ↓reduceIte] at rip
    have src : u.regValue CopyPath.short.source =
        initial.regValue .rcx + BitVec.ofNat 64 (64 * (ikm.size / 64)) := by
      simpa only [CopyPath.source, Nat.div_eq_of_lt small, Nat.mul_zero, BitVec.ofNat_eq_ofNat,
        BitVec.add_zero] using ptr
    have count : u.regValue .r14 = BitVec.ofNat 64 (ikm.size % 64) := by
      rw [Nat.mod_eq_of_lt small, ← pre.ikmLength, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      exact len
    obtain ⟨v, frameV, ripV, lenV, fields, tail, _⟩ := copyTail pre frame .short rip src count
      (HashFields.short hmac small)
    obtain ⟨t, frameT, ripT, byte, write⟩ := storeLength pre frameV .short ripV
      (Nat.mod_lt _ (by decide)) lenV
    have finished := (fields.preserved (fun i lo hi => afterStore write i (by omega) hi)).hmac
      (tailAfterStore write tail) (by rw [BitVec.add_assoc]; exact byte)
    exact shortJump pre frameT ripT finished
  · simp only [small, ↓reduceIte] at rip
    obtain ⟨v, frameV, ripV, ptrV, lenV, fields⟩ := Update.bulk pre frame rip ptr len
      ((branch.read (n := 64) (r := 0) (by decide)).trans state.hashPtr) hmac
    obtain ⟨w, frameW, ripW, byte, write⟩ := storeLength pre frameV .residual ripV
      (Nat.mod_lt _ (by decide)) lenV
    obtain ⟨t, frameT, ripT, _, fieldsT, tail, same⟩ := copyTail pre frameW .residual ripW
      ((write.read (n := 64) (r := 12) (by simp)).trans ptrV)
      ((write.read (n := 64) (r := 14) (by simp)).trans lenV)
      (fields.preserved (fun i lo hi => afterStore write i (by omega) hi))
    exact ⟨t, frameT, ripT, fieldsT.hmac tail (by
      rw [BitVec.add_assoc]; exact same.trans byte)⟩

end Hkdf.Proofs.NewExpand.Extract
