import P256.Proofs.Sec1.SquareRoot.Square.Reduction.Entry
import P256.Proofs.Program.Frame

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Square.Reduction

open P256.Spec.Program.Routines P256.Proofs.Program
open P256.Proofs.SecretKeyFromBytes.Scalar
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem wide_limb {s : RamState} {address : BitVec 64} {v : Nat}
    (input : Bytes s.external address 64 (fun i => UInt8.ofNat (v / 256^i % 256)))
    (j : Nat) (hj : j < 8) :
    memLoad s.external (address + BitVec.ofNat 64 (8*j)) 64 =
      BitVec.ofNat 64 (v / 2^(64*j)) := by
  refine Bytes.memLoad (n := 64) ?_ (by decide) (by decide)
  intro i hi
  rw [P256.Proofs.ReadBe.storedByte_ofNat64 _ _ hi, BitVec.add_assoc, ← BitVec.ofNat_add]
  have hp : 256 ^ (8*j+i) = 2^(64*j) * 256^i := by
    rw [Nat.pow_add]
    congr 1
    rw [show (256 : Nat) = 2^8 by decide, ← Nat.pow_mul]
    congr 1
    omega
  simpa only [hp, Nat.div_div_eq_div_mul] using input (8*j+i) (by omega)

theorem input_limb [Bindings] {s t : RamState} {boundary : ReturnBoundary} {v : Nat}
    (pre : ReductionPre s boundary) (state : ScalarFrame.FrameState s t 32 112 112)
    (input : Bytes s.external (s.regValue .rsi) 64
      (fun i => UInt8.ofNat (v / 256^i % 256))) (j : Nat) (hj : j < 8) :
    memLoad t.external (s.regValue .rsi + BitVec.ofNat 64 (8*j)) 64 =
      BitVec.ofNat 64 (v / 2^(64*j)) := by
  apply wide_limb (j := j) (hj := hj)
  intro i hi
  rw [state.frame _]
  · exact input i hi
  · intro r hr ha
    have here := memoryRegion_contains_add pre.inputBounded (len := 64)
      (Nat.le_refl _) (Nat.le_refl _) hi
    have casesR : r = registerRegion s .rdi 32 ∨ r = Stack.region s 112 := by simpa using hr
    rcases casesR with rfl | rfl
    · exact pre.separation (0 : Fin 3) (1 : Fin 3) (by decide) _ here ha
    · exact pre.separation (0 : Fin 3) (2 : Fin 3) (by decide) _ here ha

theorem modulus_limb [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : ReductionPre s boundary) (state : ScalarFrame.FrameState s t 32 112 112)
    (j : Nat) (hj : j < 4) :
    memLoad t.external (s.regValue .rdx + BitVec.ofNat 64 (8*j)) 64 =
      BitVec.ofNat 64 (P256.Spec.Operations.domain.p / 2^(64*j)) := by
  have modulus : Nat256At t (s.regValue .rdx) P256.Spec.Operations.domain.p := by
    refine ⟨pre.modulus.1, ?_⟩
    intro i hi
    rw [state.frame _]
    · exact pre.modulus.2 i hi
    · intro r hr ha
      have here := memoryRegion_contains_add pre.modulusBounded (len := 32)
        (Nat.le_refl _) (Nat.le_refl _) hi
      have casesR : r = registerRegion s .rdi 32 ∨ r = Stack.region s 112 := by simpa using hr
      rcases casesR with rfl | rfl
      · exact pre.modulusOutput _ here ha
      · exact pre.modulusStack _ here ha
  exact modulus.memLoad_limb j hj

end P256.Proofs.Sec1.SquareRoot.Square.Reduction
