import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Info.Prepare
import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Info.Short.Footprint
import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Info.Compression.Frame

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Expand.Info

open Hkdf.Spec.Program Hkdf.Proofs.Program Hkdf.Proofs.Common
open Hkdf.Proofs.Common.CallFrame Hkdf.Proofs.Common.Machine
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def regions (sp : BitVec 64) : Vector MemoryRegion 3 :=
  #v[⟨(sp + 272).toNat,104⟩, ⟨sp.toNat - 344,344⟩, ⟨(sp + 432).toNat,8⟩]

theorem shortFootprint {s t : RamState} {previous count : Nat}
    (bounds : 344 ≤ (stackPtr s).toNat ∧ (stackPtr s).toNat + 544 < 2^32)
    (short : previous + count < 64) (frame : MemoryWriteFrame s t
      (Short.footprint (stackPtr s) previous count)) : MemoryWriteFrame s t (longRegions s) := by
  let sp := stackPtr s
  change 344 ≤ sp.toNat ∧ sp.toNat + 544 < 2^32 at bounds
  apply frame_mono frame
  intro r hr a ha
  have parts : r = ⟨(sp + 272 + BitVec.ofNat 64 previous).toNat, count⟩ ∨
      r = ⟨(sp - 8).toNat, 8⟩ ∨ r = ⟨(sp + 335).toNat, 1⟩ := by
    simpa only [Short.footprint, Vector.mem_mk, List.mem_toArray,
      List.mem_cons, List.not_mem_nil, or_false] using hr
  rcases parts with rfl | rfl | rfl
  · refine ⟨⟨(sp + 272).toNat,104⟩, by simp [longRegions,localRegions,sp], ?_⟩
    simp only [MemoryRegion.Contains, BitVec.toNat_add, BitVec.reduceToNat, BitVec.toNat_ofNat] at ha ⊢
    omega
  · refine ⟨⟨sp.toNat - 344,344⟩, by simp [longRegions,localRegions,sp], ?_⟩
    simp only [MemoryRegion.Contains, BitVec.toNat_sub, BitVec.reduceToNat] at ha ⊢
    omega
  · refine ⟨⟨(sp + 272).toNat,104⟩, by simp [longRegions,localRegions,sp], ?_⟩
    simp only [MemoryRegion.Contains, BitVec.toNat_add, BitVec.reduceToNat] at ha ⊢
    omega

theorem spanFrame {s h u v t : RamState}
    (bounds : (stackPtr s).toNat + 544 < 2^32) (head : AgreesExcept (headComponents s) s h)
    (decoded : u.external = h.external) (sp : stackPtr u = stackPtr s)
    (frame : MemoryWriteFrame u v (longRegions u)) (exitMem : t.external = v.external) :
    MemoryWriteFrame s t (regions (stackPtr s)) := by
  have headFrame : MemoryWriteFrame s h (regions (stackPtr s)) := by
    apply head.memoryWriteFrame
    intro c member a cover
    obtain ⟨r, hr, ha⟩ := headWrites s c member a cover
    rcases List.mem_singleton.mp hr with rfl
    obtain ⟨i, hi, rfl⟩ := ha
    refine ⟨⟨(stackPtr s + 432).toNat,8⟩, by simp [regions], ?_⟩
    change i < 8 at hi
    change (stackPtr s + 432).toNat ≤ _ ∧ _ < (stackPtr s + 432).toNat + 8
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat] at *
    omega
  have coreFrame : MemoryWriteFrame u v (regions (stackPtr s)) := by
    apply frame_mono frame
    intro r hr a ha
    change r ∈ localRegions (stackPtr u) 272 104 344 at hr
    rw [sp] at hr
    refine ⟨r, ?_, ha⟩
    simp only [localRegions, Vector.mem_mk, List.mem_toArray, List.mem_cons,
      List.not_mem_nil, or_false] at hr
    simp only [regions, Vector.mem_mk, List.mem_toArray, List.mem_cons,
      List.not_mem_nil, or_false]
    exact hr.imp_right Or.inl
  intro a outside
  rw [exitMem, coreFrame a outside, decoded, headFrame a outside]

end Hkdf.Proofs.NewExpand.Expand.Info
