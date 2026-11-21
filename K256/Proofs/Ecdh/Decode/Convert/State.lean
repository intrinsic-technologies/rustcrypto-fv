import K256.Proofs.ParseSignature.Call
import K256.Proofs.ParseSignature.Contract

namespace K256.Proofs.Ecdh.Decode.Convert

open X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Refine K256.Proofs.Lift
open K256.Spec.Program

def inputWord (fr : Activation) (i : Nat) : BitVec 64 :=
  memLoad fr.original (wordAddr fr.rsi 64 i) 64

def inputFlag (fr : Activation) : BitVec 8 := memLoad fr.original (fr.rsi + 80) 8

def coordinates (fr : Activation) (a : Values Value Reg.count) (m : Ram) : Prop :=
  a[13] = ⟨64, inputWord fr 0⟩ ∧ a[5] = ⟨64, inputWord fr 1⟩ ∧
  a[14] = ⟨64, inputWord fr 2⟩ ∧ a[15] = ⟨64, inputWord fr 3⟩ ∧
  a[12] = ⟨64, inputWord fr 4⟩ ∧
  ∀ i < 5, memLoad m (wordAddr (fr.rsp - 88) 64 i) 64 = inputWord fr (5 + i)

def outputWord (fr : Activation) (i : Nat) : BitVec 64 :=
  if inputFlag fr = 1 then (if i = 5 then 1 else 0)
  else if i < 10 then inputWord fr i else if i = 10 then 1 else 0

end K256.Proofs.Ecdh.Decode.Convert
