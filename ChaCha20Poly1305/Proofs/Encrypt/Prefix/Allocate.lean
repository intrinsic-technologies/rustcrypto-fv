import ChaCha20Poly1305.Proofs.Encrypt.Prefix.Allocate.Reserve
import ChaCha20Poly1305.Proofs.Encrypt.Prefix.Allocate.Finish

namespace ChaCha20Poly1305.Proofs.Encrypt.Prefix

open ChaCha20Poly1305.Spec ChaCha20Poly1305.Spec.Program
open Standards.RFC.ChaCha20Poly1305 Prelude X86 X86.Machine X86.UserProcess X86Proofs
open CoreContract

theorem alloc_to_setup [bindings : Bindings] {initial : RamState}
    {key : Vector UInt8 32} {nonce : Vector UInt8 12} {associatedData plaintext : ByteArray}
    (hb : MachineRamUnitStrideDecodable bindings initial)
    (hm : SupportedIntegerMachineState bindings.processor initial)
    (hc : ValidCall encrypt initial [key, nonce, associatedData, plaintext]) {s : RamState}
    (hs : BeforeAlloc initial s key plaintext.size) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧
      BeforeCoreSetup initial t key plaintext := by
  have st := Suffix.entry_stack hc
  have outside : ¬ InProgram (returnBoundary initial).rip := by
    obtain ⟨addr, hw, -, ha⟩ := hc.returnAddress
    have he := Wrapper.word64At_memLoad hw
    simp only [Stack.returnSlot, BitVec.ofNat_toNat, BitVec.setWidth_eq] at he
    have he' : (returnBoundary initial).rip = addr := he
    rw [he']
    exact ha
  have bound : plaintext.size < 2^32 := by
    have h := (allocation_bounds hc).1
    omega
  obtain ⟨n, u, au, hu⟩ := alloc_to_header hb hm hc hs
  obtain ⟨v, av, hv⟩ := header_to_dispatch hu st outside bound
  obtain ⟨m, t, adv, ht⟩ := dispatch_to_setup hb hc st outside hv
  exact ⟨n + (8 + m), t, au.trans (av.trans adv), ht⟩

end ChaCha20Poly1305.Proofs.Encrypt.Prefix
