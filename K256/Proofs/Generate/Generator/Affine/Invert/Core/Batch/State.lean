import K256.Proofs.Generate.Generator.Affine.Invert.Core.State
import K256.Proofs.Generate.Generator.Affine.Invert.SafeGcd.Batch

namespace K256.Proofs.Generate.Generator.Affine.Invert.Core.Batch

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Generate.LIR
open SafeGcd.Batch (Words)

def count (j : Nat) := min 62 (591 - roundsBefore j)

def work (sp : Word) : List MemoryRegion :=
  [⟨(base sp + 8).toNat, 104⟩]

def setupWrites (sp : Word) : List MemoryRegion :=
  work sp ++ [⟨(base sp + 116).toNat, 4⟩, ⟨(base sp + 352).toNat, 8⟩]

structure Inner (b : Registers) (m : Ram) (sp : Word) (s : Words) (left : Nat) : Prop where
  rsp : b[4] = ⟨64, base sp⟩
  delta : b[5] = ⟨64, s.delta⟩
  f : b[0] = ⟨64, s.f⟩
  g : b[1] = ⟨64, s.g⟩
  u : b[7] = ⟨64, s.u⟩
  v : b[6] = ⟨64, s.v⟩
  q : memLoad m (base sp + 8) 64 = s.q
  r : b[12] = ⟨64, s.r⟩
  counter : b[9] = ⟨64, BitVec.ofNat 64 left⟩

structure Rows (b : Registers) (m : Ram) (sp : Word) (s : Words) : Prop where
  rsp : b[4] = ⟨64, base sp⟩
  scratch : b[14] = ⟨64, base sp + 16⟩
  delta : b[5] = ⟨64, s.delta⟩
  u : b[15] = ⟨64, s.u⟩
  v : b[3] = ⟨64, s.v⟩
  q : memLoad m (base sp + 8) 64 = s.q
  r : b[12] = ⟨64, s.r⟩

def Controls (b c : Registers) :=
  ∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → c[i] = b[i]

theorem count_spec {j : Nat} (hj : j < 10) :
    0 < count j ∧ count j ≤ 62 ∧ roundsBefore j + count j = roundsBefore (j+1) := by
  simp only [count, roundsBefore, Nat.mul_add, Nat.mul_one]
  omega

end K256.Proofs.Generate.Generator.Affine.Invert.Core.Batch
