import ChaCha20Poly1305.Proofs.Wrapper

namespace ChaCha20Poly1305.Proofs.Encrypt.Prefix

open ChaCha20Poly1305.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Wrapper

set_option maxRecDepth 10000 in
theorem initial_stack {initial : RamState}
    {key : Vector UInt8 32} {nonce : Vector UInt8 12} {associatedData plaintext : ByteArray}
    (hCall : ValidCall encrypt initial [key, nonce, associatedData, plaintext]) :
    EntryStack initial := by
  have hv : Stack.Valid initial 1168 := hCall.stackAvailable
  obtain ⟨hb, ha, hn, -⟩ := hv
  have hav := hCall.separation.2.2 (Stack.region initial 1168) (by simp [writtenRegions, encrypt])
  simp only [Stack.region, MemoryRegion.Bounded, userAddressLimit, MemoryRegion.Allocated,
    MemoryRegion.Contains, Stack.NoUnderflow, Stack.returnAddressBytes] at hb ha hn
  simp only [MemoryRegion.Avoids, Stack.region, MemoryRegion.Contains, pageTables,
    Stack.returnAddressBytes] at hav
  have hsp : initial.regValue .rsp = stackPtr initial := rfl
  rw [hsp] at hb ha hn hav
  refine ⟨by omega, by omega, ?_, ?_, ?_⟩
  · intro a h1 h2
    obtain ⟨b, hb⟩ := ha a ⟨by omega, by change _ < _ + (_ + 8 - _); omega⟩
    simp [hb]
  · intro a h1 h2 hp
    exact hav a ⟨by omega, by change _ < _ + (_ + 8 - _); omega⟩ (.inl hp)
  · refine Classical.byContradiction fun hc => ?_
    let x : Nat := max ((stackPtr initial).toNat - 1104) 0x1000
    have hx : x < 2 ^ 64 := by omega
    apply hav (BitVec.ofNat 64 x)
    · rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx]
      constructor <;> omega
    · right
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hx]
      constructor <;> omega


end ChaCha20Poly1305.Proofs.Encrypt.Prefix
