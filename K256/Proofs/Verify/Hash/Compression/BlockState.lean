import K256.Proofs.Verify.Hash.Compression.Interface
import K256.Proofs.Verify.Hash.Compression.Values.Complete
import K256.Proofs.Verify.Hash.Compression.Groups
import K256.Proofs.Verify.Hash.Compression.SpillFrame

namespace K256.Proofs.Verify.Hash.Compression
open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
open Values

def blockValues (args : CFG.Values Value Reg.count) (m : Ram) (base : BitVec 64) : Compression.Values :=
  ⟨fun r => (args[r.toNat]'(Nat.lt_trans r.isLt (by decide : 2^5 < Reg.count))).get 64,
    fun off => memLoad m (base + BitVec.ofNat 64 off) 32⟩

theorem blockRegisters (args : CFG.Values Value Reg.count) (m : Ram) (base : BitVec 64) :
    registersAgree args (blockValues args m base) initialRegisters := by
  repeat' first | apply And.intro | rfl | exact True.intro

theorem blockHash {args : CFG.Values Value Reg.count} {m : Ram} {base : BitVec 64} {hash : Array UInt32}
    (words : ∀ i : Fin 8, args[hashRegisters[i]].get 32 = hash[i.val]!.toBitVec) :
    hashState (blockValues args m base) = BitVecState.ofState (State.ofArray hash) := by
  have getLow (v : Value) : (v.get 64).setWidth 32 = v.get 32 :=
    BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64)
  unfold hashState BitVecState.ofState State.ofArray
  congr 1 <;> first
    | exact (getLow _).trans (words 0)
    | exact (getLow _).trans (words 1)
    | exact (getLow _).trans (words 2)
    | exact (getLow _).trans (words 3)
    | exact (getLow _).trans (words 4)
    | exact (getLow _).trans (words 5)
    | exact (getLow _).trans (words 6)
    | exact (getLow _).trans (words 7)

theorem registersOfHash {s : Compression.Values} {hash : Array UInt32}
    (result : hashState s = BitVecState.ofState (State.ofArray hash)) (i : Fin 8) :
    (s.regs (BitVec.ofNat 5 hashRegisters[i].val)).setWidth 32 = hash[i.val]!.toBitVec := by
  have cases8 : ∀ j : Fin 8, j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by decide
  rcases cases8 i with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> first
    | exact congrArg BitVecState.a result
    | exact congrArg BitVecState.b result
    | exact congrArg BitVecState.c result
    | exact congrArg BitVecState.d result
    | exact congrArg BitVecState.e result
    | exact congrArg BitVecState.f result
    | exact congrArg BitVecState.g result
    | exact congrArg BitVecState.h result

end K256.Proofs.Verify.Hash.Compression
