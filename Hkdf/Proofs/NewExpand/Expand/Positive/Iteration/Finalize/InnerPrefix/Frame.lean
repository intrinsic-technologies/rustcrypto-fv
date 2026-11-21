import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Finalize.Mark
import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Finalize.Extra
import Hkdf.Proofs.NewExpand.Expand.Frame
import Hkdf.Proofs.Common.Memory.Bytes

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Expand.Finalize.InnerPrefix

open Hkdf.Spec.Program Hkdf.Proofs.Program Hkdf.Proofs.Common Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.CallFrame Hkdf.Proofs.Common.SHA256 Hkdf.Proofs.Common.StreamPadding
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def writes (p : BitVec 64) : Vector MemoryRegion 2 :=
  #v[⟨p.toNat - 344, 344⟩, ⟨p.toNat + 16, 160⟩]

def prefixHash (message : ByteArray) : Array UInt32 :=
  let hash := compressBlocks Hkdf.Proofs.NIST.SHA256.initialHash message
  if message.size % 64 < 56 then hash
  else Hkdf.Proofs.NIST.SHA256.compress hash
    (Hkdf.Proofs.NIST.Encoding.octetsToBits (tailFirst message))

structure Result [Bindings] {n : Nat} (entry s t : RamState) (boundary : ReturnBoundary)
    (regions : Vector MemoryRegion n) (message : ByteArray) : Prop where
  execution : ∃ fuel, Advances boundary fuel s t
  running : Running entry boundary regions t
  rip : t.RIP = 0x10f320
  sp : stackPtr t = stackPtr s
  blocks : t.regValue .r13 = BitVec.ofNat 64 (message.size / 64)
  remainder : t.regValue .r15 = BitVec.ofNat 64 (message.size % 64)
  r12 : t.regValue .r12 = s.regValue .r12
  r14 : t.regValue .r14 = s.regValue .r14
  rbp : t.regValue .rbp = s.regValue .rbp
  mxcsr : t.MXCSR = s.MXCSR
  fcw : t.FP87_Control = s.FP87_Control
  frame : MemoryWriteFrame s t (writes (stackPtr s))
  hash : HashStateAt t (stackPtr t + 144) (prefixHash message)
  bytes : (⟨(stackPtr t + 80).toNat, 56⟩ : MemoryRegion).HasBytes t.external (finalPrefix message)

theorem stack_geometry {entry s : RamState} (stack : Stack.Valid entry 2264)
    (sp : stackPtr s = stackPtr entry - 536) :
    (stackPtr s).toNat = (stackPtr entry).toNat - 536 ∧
      344 ≤ (stackPtr s).toNat ∧ (stackPtr s).toNat + 544 < 2^32 := by
  have base : (stackPtr s).toNat = (stackPtr entry).toNat - 536 := by
    rw [sp]
    exact stack_sub_toNat stack (by decide)
  obtain ⟨low, high⟩ := stack_bounds stack
  exact ⟨base, by omega, by omega⟩

theorem add_toNat {p : BitVec 64} (high : p.toNat + 544 < 2^32)
    (offset : Nat) (bound : offset ≤ 544) :
    (p + BitVec.ofNat 64 offset).toNat = p.toNat + offset := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : offset < 2^64), Nat.mod_eq_of_lt (by omega)]

theorem within_stack {entry s : RamState} (stack : Stack.Valid entry 2264)
    (sp : stackPtr s = stackPtr entry - 536) :
    ∀ r ∈ writes (stackPtr s), ∀ a, r.Contains a → (Stack.region entry 2264).Contains a := by
  obtain ⟨base, low, high⟩ := stack_geometry stack sp
  have hstack := (stack_bounds stack).1
  intro r member a contains
  have cases : r = ⟨(stackPtr s).toNat - 344, 344⟩ ∨ r = ⟨(stackPtr s).toNat + 16, 160⟩ := by
    simpa [writes] using member
  change (Stack.region entry 2264).start ≤ a ∧
    a < (Stack.region entry 2264).start + (Stack.region entry 2264).size
  rw [stack_region_end]
  change (stackPtr entry).toNat - 2264 ≤ a ∧ a < (stackPtr entry).toNat + 8
  clear stack sp high member
  rcases cases with rfl | rfl
  · change (stackPtr s).toNat - 344 ≤ a ∧ a < (stackPtr s).toNat - 344 + 344 at contains
    rw [Nat.sub_add_cancel low] at contains
    have lower : (stackPtr entry).toNat - 2264 ≤ (stackPtr s).toNat - 344 := by
      rw [base, Nat.sub_sub]
      exact Nat.sub_le_sub_left (by decide : 880 ≤ 2264) _
    exact ⟨Nat.le_trans lower contains.1, Nat.lt_of_lt_of_le contains.2 (by omega)⟩
  · change (stackPtr s).toNat + 16 ≤ a ∧ a < (stackPtr s).toNat + 16 + 160 at contains
    omega

theorem include_above {p : BitVec 64} {off len a : Nat} (high : p.toNat + 544 < 2^32)
    (low : 16 ≤ off) (fit : off + len ≤ 176)
    (contains : (⟨(p + BitVec.ofNat 64 off).toNat, len⟩ : MemoryRegion).Contains a) :
    ∃ r ∈ writes p, r.Contains a := by
  refine ⟨⟨p.toNat + 16, 160⟩, by simp [writes], ?_⟩
  change (p + BitVec.ofNat 64 off).toNat ≤ a ∧ a < (p + BitVec.ofNat 64 off).toNat + len at contains
  rw [add_toNat high off (by omega)] at contains
  change p.toNat + 16 ≤ a ∧ a < p.toNat + 16 + 160
  omega

theorem mark_frame {s t : RamState} (low : 344 ≤ (stackPtr s).toNat)
    (high : (stackPtr s).toNat + 544 < 2^32)
    (frame : MemoryWriteFrame s t (InnerPadding.writes (stackPtr s))) :
    MemoryWriteFrame s t (writes (stackPtr s)) := by
  apply frame_mono frame
  intro r member a contains
  have cases : r = ⟨(stackPtr s + 80).toNat, 64⟩ ∨ r = ⟨(stackPtr s - 8).toNat, 8⟩ := by
    simpa [InnerPadding.writes] using member
  rcases cases with rfl | rfl
  · exact include_above high (off := 80) (by decide) (by decide) contains
  · refine ⟨⟨(stackPtr s).toNat - 344, 344⟩, by simp [writes], ?_⟩
    have ret : (stackPtr s - 8).toNat = (stackPtr s).toNat - 8 := by
      apply BitVec.toNat_sub_of_le
      simp only [BitVec.le_def, BitVec.reduceToNat]
      omega
    change (stackPtr s - 8).toNat ≤ a ∧ a < (stackPtr s - 8).toNat + 8 at contains
    rw [ret] at contains
    change (stackPtr s).toNat - 344 ≤ a ∧ a < (stackPtr s).toNat - 344 + 344
    omega

theorem step_frame [Bindings] {entry s t : RamState} {boundary : ReturnBoundary} {n fuel : Nat}
    {regions : Vector MemoryRegion n} {components : List Component} {off len : Nat}
    (stack : Stack.Valid entry 2264) (sp : stackPtr s = stackPtr entry - 536)
    (running : Running entry boundary regions s) (inStack : Stack.region entry 2264 ∈ regions)
    (avoids : ∀ r ∈ regions, r.Avoids InProgram) (run : Advances boundary fuel s t) (ready : ReadyToStep t)
    (agree : AgreesExcept components s t) (df : .df ∉ components)
    (low : 16 ≤ off) (fit : off + len ≤ 176)
    (covers : ∀ c ∈ components, ∀ a, c.Covers a →
      (Component.mem (stackPtr s + BitVec.ofNat 64 off) len).Covers a) :
    Running entry boundary regions t ∧
      MemoryWriteFrame s t #v[⟨(stackPtr s + BitVec.ofNat 64 off).toNat, len⟩] := by
  have high := (stack_geometry stack sp).2.2
  have localWrites : WritesWithin components #v[⟨(stackPtr s + BitVec.ofNat 64 off).toNat, len⟩] := by
    intro c hc a ha
    obtain ⟨i, hi, rfl⟩ := covers c hc a ha
    refine ⟨⟨(stackPtr s + BitVec.ofNat 64 off).toNat, len⟩, Vector.mem_singleton_self _,
      memoryRegion_contains_add ?_ (Nat.le_refl _) (Nat.le_refl _) hi⟩
    change (stackPtr s + BitVec.ofNat 64 off).toNat + len < 2^32
    rw [add_toNat high off (by omega)]
    omega
  refine ⟨running.of_agrees run ready agree ?_ avoids df, agree.memoryWriteFrame localWrites⟩
  intro c hc a ha
  obtain ⟨r, hr, contains⟩ := localWrites c hc a ha
  obtain rfl := Vector.mem_singleton.mp hr
  obtain ⟨w, hw, inside⟩ := include_above high low fit contains
  exact ⟨_, inStack, within_stack stack sp w hw a.toNat inside⟩

theorem step_widen {s t : RamState} {off len : Nat} (high : (stackPtr s).toNat + 544 < 2^32)
    (low : 16 ≤ off) (fit : off + len ≤ 176)
    (frame : MemoryWriteFrame s t #v[⟨(stackPtr s + BitVec.ofNat 64 off).toNat, len⟩]) :
    MemoryWriteFrame s t (writes (stackPtr s)) := by
  apply frame_mono frame
  intro r member a contains
  obtain rfl := Vector.mem_singleton.mp member
  exact include_above high low fit contains

theorem append_running [Bindings] {entry s t : RamState} {boundary : ReturnBoundary} {n : Nat}
    {regions : Vector MemoryRegion n} (stack : Stack.Valid entry 2264)
    (sp : stackPtr s = stackPtr entry - 536) (inStack : Stack.region entry 2264 ∈ regions)
    (before : Running entry boundary regions s) (after : Running s boundary (writes (stackPtr s)) t) :
    Running entry boundary regions t := by
  obtain ⟨fuel₁, run₁⟩ := before.execution
  obtain ⟨fuel₂, run₂⟩ := after.execution
  have frame := frame_mono after.frame (large := regions) (by
    intro r hr a ha
    exact ⟨_, inStack, within_stack stack sp r hr a ha⟩)
  exact ⟨⟨_, run₁.trans run₂⟩, after.machine, after.loaded, fun a ha => after.allocated a (before.allocated a ha),
    after.directionFlag, memoryWriteFrame_trans before.frame frame⟩

end Hkdf.Proofs.NewExpand.Expand.Finalize.InnerPrefix
