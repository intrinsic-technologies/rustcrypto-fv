import P256.Proofs.Signing.Core.Initialize.CallState
import P256.Proofs.Signing.Core.Initialize.Memory
import P256.Proofs.Nonce.Mathematics
import P256.Proofs.SecretKeyFromBytes.Encoding

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Initialize

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open Standards.SECG.ECC.Encoding P256.Proofs.SecretKeyFromBytes.Encoding

variable [Bindings] {s t u : RamState} {boundary : ReturnBoundary} {secret : Nat}

theorem nonce_key (input : CallInput s t secret) (entered : Entered s t u) :
    (registerRegion u .rsi 32).HasBytes u.external
      (Standards.RFC.DeterministicSigning.Nonce.intToOctets Operations.domain.n secret) := by
  have ptr : u.regValue .rsi = frameBase s + 528 :=
    (entered.registers .rsi (by decide)).trans input.rsi
  rw [Nonce.intToOctets_eq]
  refine ⟨natToOctets_size _ _, ?_⟩
  intro i
  have hi : i.val < 32 := by simpa only [natToOctets_size] using i.isLt
  have copy := entered.bytes (528+i.val) (by omega)
  rw [BitVec.ofNat_add, ← BitVec.add_assoc] at copy
  have byte := copy.trans (input.bytes i.val hi)
  change u.external[BitVec.ofNat 64 ((u.regValue .rsi).toNat+i.val)]? = _
  rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, ptr]
  simp only [ByteArray.getElem_eq_getElem_data, natToOctets_getElem 32 secret i.val hi]
  exact byte

theorem nonce_digest {digest : ByteArray} (pre : SignPre s boundary)
    (input : CallInput s t secret) (entered : Entered s t u)
    (hash : (registerRegion s .rdx 32).HasBytes s.external digest) :
    (registerRegion u .rcx 32).HasBytes u.external digest := by
  have ptr : u.regValue .rcx = s.regValue .rdx :=
    (entered.registers .rcx (by decide)).trans input.rcx
  have region : registerRegion u .rcx 32 = registerRegion s .rdx 32 := by simp only [registerRegion, ptr]
  rw [region]
  refine ⟨hash.1, fun i => ?_⟩
  have addr : BitVec.ofNat 64 ((s.regValue .rdx).toNat+i.val) = s.regValue .rdx + BitVec.ofNat 64 i.val := by
    simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have inside := memoryRegion_contains_add pre.digestBounded (len := 32)
    (Nat.le_refl _) (Nat.le_refl _) (show i.val < 32 by have hi := i.isLt; have hs : digest.size = 32 := hash.1; omega)
  change u.external[BitVec.ofNat 64 ((s.regValue .rdx).toNat+i.val)]? = _
  rw [addr, entered.frame.frame _]
  · have h := hash.2 i
    change s.external[BitVec.ofNat 64 ((s.regValue .rdx).toNat+i.val)]? = _ at h
    rwa [addr] at h
  · intro region hr hin
    have cases : region = registerRegion s .rdi 65 ∨ region = Stack.region s 4584 := by simpa using hr
    rcases cases with rfl | rfl
    · exact pre.digestOutput _ inside hin
    · exact pre.digestStack _ inside hin

end P256.Proofs.Signing.Core.Initialize
