import Sha2.Proofs.Common.SHA256.Absorb.TraversalProof.Transport
import Sha2.Proofs.Common.Machine.FrameMemory
import Sha2.Proofs.Common.SHA256.Absorb.DirectProof.Code

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Absorb.Table

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

variable {l : Layout} {initial : RamState} {reserve : Nat}

theorem footprint_subset_stack (wf : WellFormed l reserve) (stack : Stack.Valid initial reserve) :
    ∀ region ∈ footprint l (l.chunk.sp initial), ∀ a, region.Contains a →
      (Stack.region initial reserve).Contains a := by
  intro region member a ha
  simp only [footprint, Vector.mem_mk, List.mem_toArray, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact stack_frame_region_subset stack (by have := wf.chunk.capacity; omega)
      wf.chunk.bufferFits ha
  · exact stack_frame_region_subset stack (by have := wf.chunk.capacity; omega)
      wf.storedFits ha
  · have address : l.chunk.sp initial - 344 =
        stackPtr initial - BitVec.ofNat 64 (l.chunk.frameBytes + 344) := by
      simp only [Absorb.Layout.sp, BitVec.ofNat_add, BitVec.sub_sub, BitVec.ofNat_eq_ofNat]
    rw [address] at ha
    exact stack_sub_region_subset stack wf.chunk.capacity (by omega) ha

theorem local_regions_apart (stack : Stack.Valid initial reserve)
    {frame first second firstSize secondSize : Nat}
    (capacity : frame ≤ reserve) (firstFits : first + firstSize ≤ frame)
    (secondFits : second + secondSize ≤ frame)
    (apart : OffsetsApart (BitVec.ofNat 64 first) firstSize
      (BitVec.ofNat 64 second) secondSize) :
    (⟨(stackPtr initial - BitVec.ofNat 64 frame + BitVec.ofNat 64 first).toNat,
      firstSize⟩ : MemoryRegion).Disjoint
      ⟨(stackPtr initial - BitVec.ofNat 64 frame + BitVec.ofNat 64 second).toNat,
        secondSize⟩ := by
  intro a ha hb
  change _ ≤ a ∧ a < _ at ha hb
  dsimp only at ha hb
  rw [stack_frame_toNat stack capacity (by omega)] at ha
  rw [stack_frame_toNat stack capacity (by omega)] at hb
  have bounds := stack_valid_bounds stack
  have firstSmall : first < 2^64 := by omega
  have secondSmall : second < 2^64 := by omega
  simp only [OffsetsApart, BitVec.toNat_sub, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt firstSmall, Nat.mod_eq_of_lt secondSmall] at apart
  omega

theorem slot_apart_footprint (wf : WellFormed l reserve) (stack : Stack.Valid initial reserve)
    {slot : Nat} (fits : slot + 8 ≤ l.chunk.frameBytes)
    (active : OffsetsApart slot 8 l.chunk.bufferOffset 104)
    (stored : OffsetsApart slot 8 l.storedOffset 104) :
    ∀ region ∈ footprint l (l.chunk.sp initial),
      (⟨(l.chunk.sp initial + BitVec.ofNat 64 slot).toNat, 8⟩ : MemoryRegion).Disjoint region := by
  intro region member
  simp only [footprint, Vector.mem_mk, List.mem_toArray, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact local_regions_apart stack (by have := wf.chunk.capacity; omega)
      fits wf.chunk.bufferFits active
  · exact local_regions_apart stack (by have := wf.chunk.capacity; omega)
      fits wf.storedFits stored
  · intro a ha hb
    change _ ≤ a ∧ a < _ at ha hb
    dsimp only [Absorb.Layout.sp] at ha hb
    rw [stack_frame_toNat stack (by have := wf.chunk.capacity; omega) (by omega)] at ha
    have address : l.chunk.sp initial - 344 =
        stackPtr initial - BitVec.ofNat 64 (l.chunk.frameBytes + 344) := by
      simp only [Absorb.Layout.sp, BitVec.ofNat_add, BitVec.sub_sub, BitVec.ofNat_eq_ofNat]
    dsimp only [Absorb.Layout.sp] at address
    rw [address, stack_valid_sub_toNat stack wf.chunk.capacity] at hb
    have bounds := stack_valid_bounds stack
    have capacity := wf.chunk.capacity
    omega

theorem chunk_frame {s t : RamState}
    (frame : MemoryWriteFrame s t (Absorb.footprint l.chunk (l.chunk.sp initial))) :
    MemoryWriteFrame s t (footprint l (l.chunk.sp initial)) := by
  intro address outside
  apply frame address
  intro region member contains
  apply outside region ?_ contains
  simp only [Absorb.footprint, Vector.mem_mk, List.mem_toArray, List.mem_cons,
    List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl <;> simp [footprint]

theorem singleton_frame {s t : RamState} {region : MemoryRegion}
    (member : region ∈ footprint l (l.chunk.sp initial))
    (frame : MemoryWriteFrame s t #v[region]) :
    MemoryWriteFrame s t (footprint l (l.chunk.sp initial)) := by
  intro address outside
  apply frame address
  intro written hw contains
  have same : written = region := by simpa using hw
  subst written
  exact outside region member contains

theorem CodeFacts.sequence {s : RamState} (code : CodeFacts l) (sites : List Blocks.Site)
    (subset : ∀ site ∈ sites,
      site ∈ l.load ++ l.cloneIn ++ l.cloneOut ++ l.nextSmall ++ l.nextLarge)
    (loaded : ProgramLoaded s) : CodeIn (sites.flatMap Blocks.Site.code) s := by
  intro byte member
  obtain ⟨site, hs, hb⟩ := List.mem_flatMap.mp member
  exact code.loaded site (subset site hs) s loaded byte hb

theorem local_codeApart {s : RamState} (wf : WellFormed l reserve)
    (stack : Stack.Valid initial reserve)
    (avoids : (Stack.region initial reserve).Avoids InProgram)
    (code : CodeFacts l) (loaded : ProgramLoaded s)
    {offset len : Nat} (fits : offset + len ≤ l.chunk.frameBytes)
    {site : Blocks.Site}
    (member : site ∈ l.load ++ l.cloneIn ++ l.cloneOut ++ l.nextSmall ++ l.nextLarge) :
    RangeApart (l.chunk.sp initial + BitVec.ofNat 64 offset) len
      site.pc (Blocks.bytes site.block).length := by
  apply stack_frame_codeApart stack (by have := wf.chunk.capacity; omega) avoids fits
  intro j hj
  exact Direct.loaded_code_inProgram loaded (code.loaded site member)
    (mem_codeRange site.pc (Blocks.bytes site.block) j hj)

theorem clone_separate (wf : WellFormed l reserve) (stack : Stack.Valid initial reserve) :
    l.stored (l.chunk.sp initial) = l.chunk.buffer (l.chunk.sp initial) ∨
      RangeApart (l.stored (l.chunk.sp initial)) 104 (l.chunk.buffer (l.chunk.sp initial)) 104 := by
  rcases wf.copyApart with equal | before | after
  · left
    simp only [Layout.stored, Absorb.Layout.buffer, equal]
  all_goals right
  all_goals intro i hi j hj same
  all_goals have numeric := congrArg BitVec.toNat same
  all_goals change (l.chunk.sp initial + BitVec.ofNat 64 l.storedOffset + BitVec.ofNat 64 i).toNat =
    (l.chunk.sp initial + BitVec.ofNat 64 l.chunk.bufferOffset + BitVec.ofNat 64 j).toNat at numeric
  all_goals rw [BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.add_assoc, ← BitVec.ofNat_add] at numeric
  all_goals dsimp only [Absorb.Layout.sp] at numeric
  all_goals rw [stack_frame_toNat stack (by have := wf.chunk.capacity; omega) (by have := wf.storedFits; omega),
    stack_frame_toNat stack (by have := wf.chunk.capacity; omega) (by have := wf.chunk.bufferFits; omega)] at numeric
  all_goals omega

theorem next_site_member {large : Bool} {site : Blocks.Site}
    (member : site ∈ (if large then l.nextLarge else l.nextSmall) ++ l.cloneOut) :
    site ∈ l.load ++ l.cloneIn ++ l.cloneOut ++ l.nextSmall ++ l.nextLarge := by
  simp only [List.mem_append]
  rcases List.mem_append.mp member with branch | clone
  · by_cases chosen : large = true
    · rw [ite_eq_left chosen] at branch
      exact Or.inr branch
    · rw [ite_eq_right chosen] at branch
      exact Or.inl (Or.inr branch)
  · exact Or.inl (Or.inl (Or.inr clone))

end Sha2.Proofs.Common.SHA256.Absorb.Table
