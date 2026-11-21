import P256.Proofs.Nonce.Update.Absorb.Seeded.Context

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Absorb.Seeded

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

def InnerWrites (initial : RamState) (components : List Component) : Prop :=
  ∀ c ∈ components, ∀ a, c.Covers a →
    (.mem (scratch initial + 152) 104 : Component).Covers a

theorem inner_bytes {initial s t : RamState} {components : List Component}
    (agrees : AgreesExcept components s t) (writes : InnerWrites initial components)
    {offset len : Nat} (bound : offset + len < 2^64) (apart : offset + len ≤ 152 ∨ 256 ≤ offset) :
    ∀ i < len, t.external[scratch initial + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      s.external[scratch initial + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  intro i hi
  apply agrees.byte
  intro c hc cover
  obtain ⟨j,hj,eq⟩ := writes c hc _ cover
  bv_omega

theorem Context.after_inner [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
    {state : State} {components : List Component}
    (pre : DrbgCalleePre initial boundary 0x109f30 1856 state)
    (input : Context initial s state) (ready : ReadyToStep t)
    (agrees : AgreesExcept components s t) (rsp : .reg 4 ∉ components)
    (rbp : .reg 5 ∉ components) (writes : InnerWrites initial components)
    (hdf : Component.df ∉ components := by component_not_mem)
    (hmxcsr : Component.mxcsr ∉ components := by component_not_mem)
    (hfcw : Component.fcw ∉ components := by component_not_mem) : Context initial t state := by
  have work : ∀ c ∈ components, ∀ a, c.Covers a → (ScalarFrame.workRegion initial 1856).Contains a.toNat := by
    intro c hc a cover
    exact Prepare.work_contains_scratch pre (by decide : 152 + 104 ≤ 632) (writes c hc a cover)
  apply input.after (frame_after pre input.toFrameState ready agrees rsp work)
  · intro i hi
    apply agrees.byte
    intro c hc cover
    exact pre.separation _ (memoryRegion_contains_add pre.stateBounded (Nat.le_refl _) (Nat.le_refl _) hi)
      (Prepare.work_substack pre (work c hc _ cover))
  · exact agrees.read (n := 64) (r := 5) rbp
  · intro off member i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    · exact inner_bytes (offset := 64) (len := 8) agrees writes (by decide) (by decide) i hi
    · exact inner_bytes (offset := 72) (len := 8) agrees writes (by decide) (by decide) i hi
    · exact inner_bytes (offset := 80) (len := 8) agrees writes (by decide) (by decide) i hi
    · exact inner_bytes (offset := 424) (len := 8) agrees writes (by decide) (by decide) i hi

theorem scratch_byte_of_load [Bindings] {initial s : RamState} {boundary : ReturnBoundary} {state : State}
    (pre : DrbgCalleePre initial boundary 0x109f30 1856 state) (frame : FrameState initial s)
    (offset : Nat) (bound : offset ≤ 680) (value : BitVec 8)
    (loaded : memLoad s.external (scratch initial + BitVec.ofNat 64 offset) 8 = value) :
    s.external[scratch initial + BitVec.ofNat 64 offset]? = some (UInt8.ofBitVec value) := by
  have readable : MemReadable s (stackPtr s + BitVec.ofNat 64 offset) 1 := by
    rw [ScalarFrame.scalar_stack_address (frameOffset := 680) frame.rsp (by decide) bound]
    exact readable_of_grow (stack_sub_readable pre.stack (by omega) (by omega)) frame.allocated
  rw [frame.rsp] at readable
  have bytes := Bytes.of_memLoad (n := 8) readable.mem
  change Bytes s.external (scratch initial + BitVec.ofNat 64 offset) 1
    (storedByte (memLoad s.external (scratch initial + BitVec.ofNat 64 offset) 8)) at bytes
  rw [loaded] at bytes
  have h := bytes 0 (by decide)
  simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_zero,storedByte_eq_extract,Nat.mul_zero,
    BitVec.extractLsb'_eq_self] using h

theorem copy_scratch_byte [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
    {ret address : BitVec 64} {state : State} {count destinationOffset offset len : Nat}
    (pre : DrbgCalleePre initial boundary 0x109f30 1856 state)
    (result : SeedCopyResult initial s t boundary count destinationOffset ret address)
    (destinationBound : destinationOffset ≤ 1856) (bound : offset ≤ 680) (span : offset + len ≤ 688)
    (apart : destinationOffset + len ≤ 680 - offset ∨ 680 - offset + count ≤ destinationOffset)
    {i : Nat} (hi : i < len) :
    t.external[scratch initial + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      s.external[scratch initial + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  have addressEq : scratch initial + BitVec.ofNat 64 offset =
      stackPtr initial - BitVec.ofNat 64 (680-offset) := by
    simp only [scratch]
    bv_omega
  rw [addressEq]
  exact result.stack_byte pre destinationBound (by omega) (by omega) apart hi

end P256.Proofs.Nonce.Update.Absorb.Seeded
