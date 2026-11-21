import Hkdf.Proofs.NewExpand.Extract.Initialize.Pads.Compression

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Extract.Initialize.Pads

open Hkdf.Spec.Program Hkdf.Proofs.Program Hkdf.Proofs.Common
open Hkdf.Proofs.Common.CallFrame Hkdf.Proofs.Common.Machine Hkdf.Proofs.Common.SHA256
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

abbrev setupComponents (initial : RamState) (outer : Bool) : List Component :=
  [.reg 2, .reg 3, .reg 5, .reg 6, .reg 7, .reg 12, .reg 13,
    .mem (base initial + if outer then 40 else 0) 40, .rip]

abbrev chainingRegions (initial : RamState) (outer : Bool) : Vector MemoryRegion 2 :=
  #v[slotRegion initial (hashOffset outer) 40, slotRegion initial 800 344]

theorem hashAddress (initial : RamState) (outer : Bool) :
    base initial + (if outer then 40 else 0) = slot initial (hashOffset outer) := by
  cases outer
  · exact BitVec.add_zero _
  · exact base_add initial (offset := 40) (by decide)

private theorem setup_writesWithin {initial : RamState} (stack : Stack.Valid initial 2264)
    (outer : Bool) : WritesWithin (setupComponents initial outer)
      #v[slotRegion initial (hashOffset outer) 40] := by
  intro c hc a ha
  simp only [setupComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  rw [hashAddress initial outer] at ha
  obtain ⟨i, hi, rfl⟩ := ha
  refine ⟨slotRegion initial (hashOffset outer) 40, by simp, ?_⟩
  have bound : hashOffset outer ≤ 2264 := by cases outer <;> decide
  have nat := CallFrame.stack_sub_toNat stack bound
  apply memoryRegion_contains_add (len := 40) ?_ (Nat.le_refl _) (Nat.le_refl _) hi
  change (slot initial (hashOffset outer)).toNat + 40 < 2^32
  rw [nat]
  have bounds := CallFrame.stack_bounds stack
  cases outer <;> simp only [hashOffset, Bool.false_eq_true, ite_false, ite_true] <;> omega

theorem chaining [Bindings] (outer : Bool) {initial s u : RamState} {boundary : ReturnBoundary}
    {salt : Option ByteArray} {ikm block : ByteArray} {fuel : Nat}
    (pre : ExtractPre initial boundary salt ikm) (state : Frame initial s boundary)
    (bytes : (slotRegion initial 336 64).HasBytes s.external block)
    (run : Advances boundary fuel s u) (ready : ReadyToStep u)
    (rip : u.RIP = if outer then 0x10fbba else 0x10fb5f)
    (agrees : AgreesExcept (setupComponents initial outer) s u)
    (destination : u.regValue .rdi = base initial + if outer then 40 else 0)
    (source : u.regValue .rsi = base initial + 120)
    (count : u.regValue .rdx = 1)
    (words : HashStateAt u (base initial + if outer then 40 else 0) initialHash)
    (blocks : loadBytes u.external ((base initial + if outer then 40 else 0) + 32) 8 = .ok 1) :
    ∃ t, Frame initial t boundary ∧ t.RIP = (if outer then 0x10fbbf else 0x10fb64) ∧
      PreservesABI u t ∧ MemoryWriteFrame s t (chainingRegions initial outer) ∧
      (slotRegion initial 336 64).HasBytes t.external block ∧
      HashStateAt t (slot initial (hashOffset outer)) (compressBlocks initialHash block) ∧
      loadBytes t.external (slot initial (hashOffset outer - 32)) 8 = .ok 1 := by
  have stack := pre.call.stack
  have low : hashOffset outer ≤ 2264 := by cases outer <;> decide
  have address : base initial + 120 = slot initial 336 :=
    base_add initial (offset := 120) (by decide)
  have output : base initial + 80 = slot initial 376 :=
    base_add initial (offset := 80) (by decide)
  have prepWrites := setup_writesWithin stack outer
  have setupMemory := agrees.memoryWriteFrame prepWrites
  have running := state.toRunning.of_agrees run ready agrees (by
    intro c hc a ha
    obtain ⟨r, hr, inside⟩ := prepWrites c hc a ha
    have same : r = slotRegion initial (hashOffset outer) 40 := by
      simpa only [Vector.mem_singleton] using hr
    exact ⟨_, by simp, slotRegion_within stack low (by cases outer <;> decide) (same ▸ inside)⟩)
    (stack_avoids pre) (by simp [setupComponents])
  have frameU := state.of_frame stack running setupMemory
    (agrees.read (n := 64) (r := 4) (by simp [setupComponents]))
    (agrees.mxcsr (by simp [setupComponents])) (agrees.fcw (by simp [setupComponents])) (by
      intro r member
      have eq : r = slotRegion initial (hashOffset outer) 40 := by
        simpa only [Vector.mem_singleton] using member
      rw [eq, output]
      exact ⟨slotRegion_disjoint stack (by decide) low (.inl (by cases outer <;> decide)),
        slotRegion_disjoint stack (by decide) low (.inl (by cases outer <;> decide))⟩)
  have stored := frame_hasBytes setupMemory (stored := bytes) (by
    intro r hr
    have eq : r = slotRegion initial (hashOffset outer) 40 := by
      simpa only [Vector.mem_singleton] using hr
    rw [eq]
    exact slotRegion_disjoint stack (by decide) low (.inl (by cases outer <;> decide)))
    (slotBound stack (offset := 336) (size := 64) (by decide) (by decide))
  obtain ⟨t, frameT, ripT, abi, compressionMemory, hash⟩ := compress outer pre frameU rip
    (destination.trans (hashAddress initial outer)) (source.trans address)
    count ((hashAddress initial outer) ▸ words) stored
  have total : MemoryWriteFrame s t (chainingRegions initial outer) := by
    apply memoryWriteFrame_trans
    · apply frame_mono setupMemory
      intro r hr a ha
      have eq : r = slotRegion initial (hashOffset outer) 40 := by
        simpa only [Vector.mem_singleton] using hr
      subst r
      exact ⟨_, by simp [chainingRegions], ha⟩
    · apply frame_mono compressionMemory
      intro r hr a ha
      have choices : r = slotRegion initial (hashOffset outer) 32 ∨
          r = slotRegion initial 800 344 := by
        simpa only [compressionRegions, Vector.mem_mk, List.mem_toArray, List.mem_cons,
          List.not_mem_nil, or_false] using hr
      rcases choices with rfl | rfl
      · refine ⟨slotRegion initial (hashOffset outer) 40, by simp [chainingRegions], ha.1, ?_⟩
        change a < (slot initial (hashOffset outer)).toNat + 40
        have h := ha.2
        change a < (slot initial (hashOffset outer)).toNat + 32 at h
        omega
      · exact ⟨_, by simp [chainingRegions], ha⟩
  have padT := frame_hasBytes total (stored := bytes) (by
    intro r hr
    have choices : r = slotRegion initial (hashOffset outer) 40 ∨ r = slotRegion initial 800 344 := by
      simpa only [chainingRegions, Vector.mem_mk, List.mem_toArray, List.mem_cons,
        List.not_mem_nil, or_false] using hr
    rcases choices with rfl | rfl
    · exact slotRegion_disjoint stack (by decide) low (.inl (by cases outer <;> decide))
    · exact slotRegion_disjoint stack (by decide) (by decide) (.inl (by decide)))
    (slotBound stack (offset := 336) (size := 64) (by decide) (by decide))
  refine ⟨t, frameT, ripT, abi, total, padT, hash, ?_⟩
  have same := slot_agrees stack compressionMemory (offset := hashOffset outer - 32) (size := 8)
    (by cases outer <;> decide) (by cases outer <;> decide) (by
      intro r hr
      have choices : r = slotRegion initial (hashOffset outer) 32 ∨
          r = slotRegion initial 800 344 := by
        simpa only [compressionRegions, Vector.mem_mk, List.mem_toArray, List.mem_cons,
          List.not_mem_nil, or_false] using hr
      rcases choices with rfl | rfl
      · exact slotRegion_disjoint stack (by cases outer <;> decide) low
          (.inl (by cases outer <;> decide))
      · exact slotRegion_disjoint stack (by cases outer <;> decide) (by decide)
          (.inl (by cases outer <;> decide)))
  have countAddress : (base initial + (if outer then 40 else 0)) + 32 =
      slot initial (hashOffset outer - 32) := by
    rw [hashAddress initial outer]
    exact slot_add initial (by cases outer <;> decide)
  rw [agrees_loadBytes same, ← countAddress]
  exact blocks

end Hkdf.Proofs.NewExpand.Extract.Initialize.Pads
