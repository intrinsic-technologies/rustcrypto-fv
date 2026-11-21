import ChaCha20Poly1305.Proofs.Encrypt.Prefix.Initial
import ChaCha20Poly1305.Proofs.Encrypt.Prefix.Allocate
import ChaCha20Poly1305.Proofs.Encrypt.Prefix.Setup
import ChaCha20Poly1305.Proofs.Encrypt.Prefix.CorePre

namespace ChaCha20Poly1305.Proofs.Encrypt

open ChaCha20Poly1305.Spec ChaCha20Poly1305.Spec.Program
open Standards.RFC.ChaCha20Poly1305 Prelude X86 X86.Machine X86.UserProcess X86Proofs
open CoreContract

theorem entry_to_core [bindings : Bindings] {initial : RamState}
    {key : Vector UInt8 32} {nonce : Vector UInt8 12} {associatedData plaintext : ByteArray}
    (hb : MachineRamUnitStrideDecodable bindings initial)
    (hm : SupportedIntegerMachineState bindings.processor initial)
    (hc : ValidCall encrypt initial [key, nonce, associatedData, plaintext]) :
    ∃ fuel s, Advances (returnBoundary initial) fuel initial s ∧
      CorePre s key nonce associatedData plaintext (initial.regValue .r8) (initial.regValue .r8) ∧
      AtCore initial s plaintext.size := by
  obtain ⟨n, s, h1, hs⟩ := Prefix.initial_to_alloc hb hm hc
  obtain ⟨m, t, h2, ht⟩ := Prefix.alloc_to_setup hb hm hc hs
  obtain ⟨k, u, h3, hu⟩ := Prefix.setup_to_core hb hm hc ht
  exact ⟨_, u, (h1.trans h2).trans h3, Prefix.core_pre hb hm hc hu, hu.atCore⟩

end ChaCha20Poly1305.Proofs.Encrypt
