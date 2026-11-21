import P256.Proofs.Nonce.Initialize.Reduce.Blocks.Interface
import P256.Proofs.HMAC.State

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Seed

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem copied_of_offsets {s t : RamState} {components : List Component}
    {writeOffset writeLen offset count : Nat}
    (agrees : AgreesExcept components s t)
    (writes : ∀ c ∈ components, ∀ a, c.Covers a →
      (Component.mem (stackPtr s + BitVec.ofNat 64 writeOffset) writeLen).Covers a)
    (writeBound : writeOffset + writeLen < 2^64)
    (readBound : offset + count < 2^64)
    (apart : writeOffset + writeLen ≤ offset ∨ offset + count ≤ writeOffset) :
    ∀ i < count, t.external[stackPtr s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      s.external[stackPtr s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  intro i hi
  apply agrees.memory
  intro c hc ha
  obtain ⟨j, hj, he⟩ := writes c hc _ ha
  exact RangeApart.offsets (stackPtr s) (by omega) (by omega) apart j hj i hi he.symm

theorem word_of_copied {s t : RamState} {address : BitVec 64}
    (copied : ∀ i < 8, t.external[address + BitVec.ofNat 64 i]? =
      s.external[address + BitVec.ofNat 64 i]?) :
    memLoad t.external address 64 = memLoad s.external address 64 := by
  apply memLoad_congr
  intro i hi
  exact congrArg (fun x : Option UInt8 => x.getD 0) (copied i hi)

theorem component_subrange {base : BitVec 64} {offset len start count : Nat}
    (low : start ≤ offset) (high : offset + len ≤ start + count)
    {a : BitVec 64} (covered : (Component.mem (base + BitVec.ofNat 64 offset) len).Covers a) :
    (Component.mem (base + BitVec.ofNat 64 start) count).Covers a := by
  obtain ⟨i, hi, rfl⟩ := covered
  refine ⟨offset - start + i, by omega, ?_⟩
  simp only [BitVec.add_assoc, ← BitVec.ofNat_add]
  congr 2
  omega

theorem entropy_readable [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} (pre : Nonce.InitializePre initial boundary orderAddress)
    (stage : Stage initial s boundary) : MemReadable s (stackPtr s + 288) 8 := by
  have addr : stackPtr s + 288 = initial.regValue .rsp + 8 := by
    rw [stage.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, stackPtr]
    rfl
  rw [addr]
  apply Program.readable_of_grow _ stage.allocated
  exact memoryRegion_memReadable pre.argumentsBounded pre.argumentsAllocated
    (Nat.le_refl _) (by change (initial.regValue .rsp + 8).toNat + 8 ≤ (initial.regValue .rsp + 8).toNat + 16; omega)

theorem entropy_length [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} (pre : Nonce.InitializePre initial boundary orderAddress)
    (stage : Stage initial s boundary) : memLoad s.external (stackPtr s + 288) 64 = 0 := by
  have bounds := Program.stack_bounds pre.stack
  have start : (initial.regValue .rsp + 8).toNat = (stackPtr initial).toNat + 8 := by
    rw [BitVec.toNat_add]
    change (((stackPtr initial).toNat + 8) % 2^64) = _
    exact Nat.mod_eq_of_lt (by omega)
  have apart : ∀ region ∈ #v[registerRegion initial .rdi 72, Stack.region initial 2144],
      (MemoryRegion.mk (initial.regValue .rsp + 8).toNat 16).Disjoint region := by
    intro region hr
    have cases : region = registerRegion initial .rdi 72 ∨ region = Stack.region initial 2144 := by
      simpa using hr
    rcases cases with rfl | rfl
    · exact pre.argumentsOutput
    · intro a ha hs
      have low : (initial.regValue .rsp + 8).toNat ≤ a := ha.1
      have high : a < (stackPtr initial).toNat + 8 := by
        simpa only [stack_region_end] using hs.2
      rw [start] at low
      omega
  have copied : ∀ i < 16, s.external[initial.regValue .rsp + 8 + BitVec.ofNat 64 i]? =
      initial.external[initial.regValue .rsp + 8 + BitVec.ofNat 64 i]? := by
    intro i hi
    exact frame_read stage.frame apart
      (memoryRegion_contains_add pre.argumentsBounded (Nat.le_refl _) (Nat.le_refl _) hi)
  have addr : stackPtr s + 288 = initial.regValue .rsp + 8 := by
    rw [stage.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, stackPtr]
    rfl
  have load := Program.loadBytes_ok_copy (fun i hi => copied i (by omega)) pre.entropyLength
  have readable := entropy_readable pre stage
  rw [addr] at readable ⊢
  exact Except.ok.inj ((Bytes.of_memLoad (n := 64) readable.mem).loadBytes64.symm.trans load)

end P256.Proofs.Nonce.Initialize.Seed
