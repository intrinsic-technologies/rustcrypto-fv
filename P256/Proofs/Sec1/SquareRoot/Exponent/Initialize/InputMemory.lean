import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.Prologue
import P256.Proofs.Program.Frame

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.ExponentInitialize

open P256.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem input_address_bounds [Bindings] {s : RamState} {boundary : ReturnBoundary} {x : Nat}
    (ctx : ExponentPre s boundary x) {offset : Nat} (bound : offset + 8 ≤ 144) :
    (s.regValue .rsi + BitVec.ofNat 64 offset).toNat = (s.regValue .rsi).toNat + offset := by
  have hb : (s.regValue .rsi).toNat + 144 < 2^32 := ctx.inputBounded
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega),
    Nat.mod_eq_of_lt (by omega)]

theorem input_readable [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x : Nat}
    (ctx : ExponentPre s boundary x) (hf : Frame s t)
    {offset : Nat} (bound : offset + 8 ≤ 144) :
    MemReadable t (s.regValue .rsi + BitVec.ofNat 64 offset) 8 := by
  apply readable_of_grow (s := s) _ hf.allocated
  apply memoryRegion_memReadable ctx.inputBounded ctx.inputAllocated
  · rw [input_address_bounds ctx bound]
    change (s.regValue .rsi).toNat ≤ _
    omega
  · rw [input_address_bounds ctx bound]
    change _ ≤ (s.regValue .rsi).toNat + 144
    omega

theorem input_memLoad_of_frame [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x : Nat}
    (ctx : ExponentPre s boundary x) (hf : Frame s t)
    {offset : Nat} (bound : offset + 8 ≤ 144) :
    memLoad t.external (s.regValue .rsi + BitVec.ofNat 64 offset) 64 =
      memLoad s.external (s.regValue .rsi + BitVec.ofNat 64 offset) 64 := by
  apply frame_memLoad hf.frame (region := registerRegion s .rsi 144) _ ctx.inputBounded
  · rw [input_address_bounds ctx bound]
    change (s.regValue .rsi).toNat ≤ _
    omega
  · rw [input_address_bounds ctx bound]
    change _ ≤ (s.regValue .rsi).toNat + 144
    omega
  · intro region hr
    have cases : region = registerRegion s .rdi 32 ∨ region = Stack.region s 1584 := by
      simpa using hr
    rcases cases with rfl | rfl
    · exact ctx.separation (0 : Fin 3) (1 : Fin 3) (by decide)
    · exact ctx.separation (0 : Fin 3) (2 : Fin 3) (by decide)

end P256.Proofs.Sec1.SquareRoot.ExponentInitialize
