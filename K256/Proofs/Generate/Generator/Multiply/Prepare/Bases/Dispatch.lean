import K256.Proofs.Generate.Generator.Multiply.Prepare.State
import K256.Proofs.Generate.Generator.Multiply.Prepare.HighBit
import K256.Proofs.Generate.Generator.Multiply.Prepare.Bases.Endomorphism
import K256.Proofs.Generate.Generator.Multiply.Prepare.Bases.ScalarNeg
import K256.Proofs.Generate.Generator.Multiply.Lookup.Choice
import K256.Proofs.Generate.Generator.Multiply.Lookup.Select
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Generate.Generator.Multiply

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR
  Standards.SECG.DomainParameters.Secp256k1

namespace Prepare

def stageEndomorphism (m : Ram) (t : BitVec 64) (v : Vector (BitVec 64) 4) : Ram :=
  let m := memStore m (t + 0x208) v[3]
  let m := memStore m (t + 0x200) v[2]
  let m := memStore m (t + 0x1f8) v[1]
  let m := memStore m (t + 0x1f0) v[0]
  let m := memStore m (t + 0x40) v[1]
  let m := memStore m (t + 0x10) v[2]
  let m := memStore m (t + 0x28) v[3]
  memStore m (t - 8) (0x11ca7f : BitVec 64)

set_option maxHeartbeats 2400000 in
set_option maxRecDepth 4096 in
theorem dispatchEndomorphism {a : Registers} {m : Ram} {t input : BitVec 64}
    {u v : Vector (BitVec 64) 4} (rsp : a[4].get 64 = t)
    (window : Writable Extracted.programImage m (t - 8) 0x440)
    (first : WordsAt m (t + 0x1d0) 64 u) (second : WordsAt m (t + 0x418) 64 v)
    (pair : memLoad m (t + 0x38) 64 = input) :
    ∃ b : Registers, program.runBlock (dialect Extracted.programImage) ⟨.l11c9e7,a,m⟩ =
        .call ⟨.l10e010,b,stageEndomorphism m t v⟩ (callFrame .l11ca7f 0x11ca7f) ∧
      b[4] = ⟨64,t-8⟩ ∧ b[6] = ⟨64,input⟩ ∧ b[7] = ⟨64,t+0x2b0⟩ ∧
      b[5] = ⟨64,u[0]⟩ ∧ b[3] = ⟨64,u[1]⟩ ∧ b[13] = ⟨64,u[2]⟩ ∧
      b[12] = ⟨64,u[3]⟩ ∧ b[14] = ⟨64,v[0]⟩ ∧
      b[1] = ⟨64,v[1]⟩ ∧ b[2] = ⟨64,t+0x1f0⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [8,9,15,22,39,50,51] → b[i] = a[i]) := by
  have hu0 : memLoad m (t + 464) 64 = u[0] := by
    simpa only [wordAddr, Nat.reduceDiv, Nat.reduceMul, BitVec.ofNat_eq_ofNat, Lift.reduceAddOffset,
      BitVec.reduceAdd, BitVec.add_zero] using first 0 (by decide)
  have hu1 : memLoad m (t + 472) 64 = u[1] := by
    simpa only [wordAddr, Nat.reduceDiv, Nat.reduceMul, BitVec.ofNat_eq_ofNat, Lift.reduceAddOffset,
      BitVec.reduceAdd, BitVec.add_zero] using first 1 (by decide)
  have hu2 : memLoad m (t + 480) 64 = u[2] := by
    simpa only [wordAddr, Nat.reduceDiv, Nat.reduceMul, BitVec.ofNat_eq_ofNat, Lift.reduceAddOffset,
      BitVec.reduceAdd, BitVec.add_zero] using first 2 (by decide)
  have hu3 : memLoad m (t + 488) 64 = u[3] := by
    simpa only [wordAddr, Nat.reduceDiv, Nat.reduceMul, BitVec.ofNat_eq_ofNat, Lift.reduceAddOffset,
      BitVec.reduceAdd, BitVec.add_zero] using first 3 (by decide)
  have hv0 : memLoad m (t + 1048) 64 = v[0] := by
    simpa only [wordAddr, Nat.reduceDiv, Nat.reduceMul, BitVec.ofNat_eq_ofNat, Lift.reduceAddOffset,
      BitVec.reduceAdd, BitVec.add_zero] using second 0 (by decide)
  have hv1 : memLoad m (t + 1056) 64 = v[1] := by
    simpa only [wordAddr, Nat.reduceDiv, Nat.reduceMul, BitVec.ofNat_eq_ofNat, Lift.reduceAddOffset,
      BitVec.reduceAdd, BitVec.add_zero] using second 1 (by decide)
  have hv2 : memLoad m (t + 1064) 64 = v[2] := by
    simpa only [wordAddr, Nat.reduceDiv, Nat.reduceMul, BitVec.ofNat_eq_ofNat, Lift.reduceAddOffset,
      BitVec.reduceAdd, BitVec.add_zero] using second 2 (by decide)
  have hv3 : memLoad m (t + 1072) 64 = v[3] := by
    simpa only [wordAddr, Nat.reduceDiv, Nat.reduceMul, BitVec.ofNat_eq_ofNat, Lift.reduceAddOffset,
      BitVec.reduceAdd, BitVec.add_zero] using second 3 (by decide)
  refine ⟨?_, ?run, ?rest⟩
  case run =>
    arithmetic_segment using code_l11c9e7 [rsp,pair,hu0,hu1,hu2,hu3,hv0,hv1,hv2,hv3,stageEndomorphism]
  case rest =>
    refine ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,?_⟩
    rintro ⟨i,hi⟩ hm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hm
    rcases hm with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

end Prepare

end K256.Proofs.Generate.Generator.Multiply
