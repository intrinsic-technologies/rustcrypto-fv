import Sha2.Proofs.Digest.Absorb.Short
import Sha2.Proofs.Digest.Absorb.Large

set_option autoImplicit false

namespace Sha2.Proofs.Digest.Absorb

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine
  X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Wrapper512 Sha2.Proofs.Common.SHA512

theorem correct [Bindings] (body : Compression.BlockCorrect)
    {v : Variant} {initial s : RamState} {data : ByteArray}
    (ctx : Context v initial #[⟨initial.regValue .rdi, data⟩] .digest)
    (input : Buffered v initial s ByteArray.empty .digest)
    (rip : s.RIP = v.pc 0xca .digest)
    (source : s.regValue .rsi = initial.regValue .rdi)
    (length : s.regValue .r14 = BitVec.ofNat 64 data.size) :
    ∃ t, Buffered v initial t data .digest ∧ t.RIP = v.pc 0x143 .digest := by
  obtain ⟨b,bufferedB,selected⟩ := select ctx input rip
  have frame : AgreesExcept [.flags,.rip] s b := selected.agrees
  have sourceB := (frame.read (n := 64) (r := 6) (by simp)).trans source
  have lengthB := (frame.read (n := 64) (r := 14) (by simp)).trans length
  have bounded := (ctx.inputInMemory (⟨0,by simp⟩ : Fin (#[⟨initial.regValue .rdi,data⟩] : Array Input).size)).2.1
  change (initial.regValue .rdi).toNat + data.size < 2^32 at bounded
  have lengthNat : (s.regValue .r14).toNat = data.size := by
    rw [length, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  by_cases small : data.size < 128
  · apply short ctx bufferedB ?_ small sourceB lengthB
    have target := selected.rip
    simp only [selectEffect, lengthNat, ite_eq_left (show data.size ≤ 127 by omega)] at target
    exact target.trans (Variant.pc_add v 0xca 6 .digest)
  · apply large body ctx bufferedB ?_ (by omega) sourceB lengthB
    have target := selected.rip
    simp only [selectEffect, lengthNat, ite_eq_right (show ¬ data.size ≤ 127 by omega)] at target
    exact target.trans (Variant.pc_add v 0xca 33 .digest)

end Sha2.Proofs.Digest.Absorb
