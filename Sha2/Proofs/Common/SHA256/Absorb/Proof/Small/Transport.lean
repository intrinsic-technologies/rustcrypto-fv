import Sha2.Proofs.Common.SHA256.Absorb.Proof.Calls
import Sha2.Proofs.Common.SHA256.Absorb.Proof.Memory
import Sha2.Proofs.Wrapper.Absorb.ByteAdd
import Sha2.Proofs.Wrapper.Absorb.Memory

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Absorb

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

theorem byte_of_memLoad8 {s : RamState} {address : BitVec 64} {value : BitVec 8}
    (readable : MemReadable s address 1) (load : memLoad s.external address 8 = value) :
    s.external[address]? = some (UInt8.ofNat value.toNat) := by
  have byte := Bytes.of_memLoad (n := 8) readable.mem 0 (by decide)
  have stored := byte.trans (congrArg (fun word : BitVec 8 => some (storedByte word 0)) load)
  simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, storedByte,
    Nat.mul_zero, Nat.shiftRight_zero] using stored

theorem nonvolatile_extended {r : BitVec 4}
    (member : r ∈ ([3, 5, 12, 13, 14, 15] : List (BitVec 4))) :
    r.setWidth 5 ∉ ([0, 1, 2, 6, 7, 8, 9, 10, 11] : List (BitVec 5)) := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide

theorem smallSetup_register {l : Layout} {sp : BitVec 64} {s t : RamState}
    (effect : (Stage.smallSetup.effect l sp s).Holds s t) {r : BitVec 4}
    (member : r ∈ ([3, 5, 12, 13, 14, 15] : List (BitVec 4))) :
    Blocks.readReg t r = Blocks.readReg s r := by
  apply effect.agrees.read
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [Stage.effect, Effect.components, Write.component, Operand.component]

end Sha2.Proofs.Common.SHA256.Absorb
