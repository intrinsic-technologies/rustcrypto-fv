import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Finalize.Result
import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Finalize.InnerPrefix.Frame
import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Finalize.Inner.Frame
import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Finalize.Outer.Frame

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Expand.Finalize

open Hkdf.Spec.Program Hkdf.Proofs.Common.CallFrame Prelude X86 X86.Machine X86Proofs

private theorem work_contains {p a off len : Nat} (lo : 16 ≤ off) (hi : off + len ≤ 216)
    (inside : (⟨p + off,len⟩ : MemoryRegion).Contains a) :
    (⟨p + 16,200⟩ : MemoryRegion).Contains a := by
  change p + off ≤ a ∧ a < p + off + len at inside
  change p + 16 ≤ a ∧ a < p + 16 + 200
  omega

private theorem work_subset (p : BitVec 64) {off len a : Nat} (lo : 16 ≤ off) (hi : off + len ≤ 216)
    (inside : (⟨p.toNat + off,len⟩ : MemoryRegion).Contains a) :
    ∃ r ∈ writes p, r.Contains a :=
  ⟨_, by simp [writes], work_contains lo hi inside⟩

theorem prefix_frame {s t : RamState} {p : BitVec 64} (frame : MemoryWriteFrame s t (InnerPrefix.writes p)) :
    MemoryWriteFrame s t (writes p) := by
  apply frame_mono frame
  intro r hr a ha
  simp only [InnerPrefix.writes, Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨_, by simp [writes], ha⟩
  · exact work_subset p (off := 16) (len := 160) (by decide) (by decide) ha

theorem inner_frame {s t : RamState} {p : BitVec 64} (high : p.toNat + 544 < 2^32)
    (frame : MemoryWriteFrame s t (Inner.writes p)) : MemoryWriteFrame s t (writes p) := by
  apply frame_mono frame
  intro r hr a ha
  have addr (offset : Nat) (le : offset ≤ 544) := InnerPrefix.add_toNat high offset le
  simp only [Inner.writes, Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl
  · change (⟨(p + BitVec.ofNat 64 16).toNat,64⟩ : MemoryRegion).Contains a at ha
    rw [addr 16 (by decide)] at ha
    exact work_subset p (off := 16) (len := 64) (by decide) (by decide) ha
  · change (⟨(p + BitVec.ofNat 64 136).toNat,40⟩ : MemoryRegion).Contains a at ha
    rw [addr 136 (by decide)] at ha
    exact work_subset p (off := 136) (len := 40) (by decide) (by decide) ha
  · change (⟨(p + BitVec.ofNat 64 256).toNat,8⟩ : MemoryRegion).Contains a at ha
    rw [addr 256 (by decide)] at ha
    exact ⟨_, by simp [writes], ha⟩
  · exact ⟨_, by simp [writes], ha⟩

theorem outer_frame {s t : RamState} {p : BitVec 64} (frame : MemoryWriteFrame s t (Outer.writeRegions p)) :
    MemoryWriteFrame s t (writes p) := by
  apply frame_mono frame
  intro r hr a ha
  simp only [Outer.writeRegions, Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl
  · exact ⟨_, by simp [writes], ha⟩
  · exact work_subset p (off := 16) (len := 128) (by decide) (by decide) ha
  · exact work_subset p (off := 184) (len := 32) (by decide) (by decide) ha

end Hkdf.Proofs.NewExpand.Expand.Finalize
