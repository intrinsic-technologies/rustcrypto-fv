import Hkdf.Proofs.Standard.Finalize.Suffix.State
import Hkdf.Proofs.Common.Instructions.CrossPageStore

set_option autoImplicit false

namespace Hkdf.Proofs.Standard.Finalize.Suffix.Outer.Prepare

open Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common Hkdf.Proofs.Common.CallFrame Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.StreamPadding.Execution
open Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.SHA256

variable [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}

private theorem address (state : Suffix.State initial boundary s) (offset : Nat)
    (high : offset ≤ 408) :
    stackPtr s + BitVec.ofNat 64 offset =
      stackPtr initial - BitVec.ofNat 64 (408 - offset) := by
  rw [state.rsp]
  have sum : (408 : BitVec 64) =
      BitVec.ofNat 64 (408 - offset) + BitVec.ofNat 64 offset := by
    rw [← BitVec.ofNat_add, Nat.sub_add_cancel high]
    rfl
  rw [sum, ← BitVec.sub_sub, BitVec.sub_add_cancel]

theorem readable (pre : CalleePre initial boundary 0x10dd90 144 176 1264)
    (state : Suffix.State initial boundary s) (offset len : Nat)
    (high : offset + len ≤ 416) :
    MemReadable s (stackPtr s + BitVec.ofNat 64 offset) len :=
  local_readable .hmac pre state.running state.rsp offset len high

theorem writable (pre : CalleePre initial boundary 0x10dd90 144 176 1264)
    (state : Suffix.State initial boundary s) (offset len : Nat)
    (positive : 0 < len) (high : offset + len ≤ 408) :
    Hkdf.Proofs.Common.Instructions.CrossPageStore.Writable s
      (stackPtr s + BitVec.ofNat 64 offset) len := by
  have read := readable pre state offset len (by omega)
  refine ⟨read, tables_of_not_reserved positive read.low ?_⟩
  intro i hi reserved
  apply pre.avoids (Stack.region initial 1264) (by simp) _ ?_ (.inr reserved)
  rw [address state offset (by omega)]
  exact Hkdf.Proofs.Common.Machine.stackRegion_contains_sub pre.stack.2.2.1
    (offset := 408 - offset) (by omega) (by omega) ⟨i, hi, rfl⟩

omit [Bindings] in
theorem code_span (ip len : Nat) (low : 0x100000 ≤ ip)
    (high : ip + len ≤ 0x100000 + 115149) :
    ∀ i < len, InProgram (BitVec.ofNat 64 ip + BitVec.ofNat 64 i) := by
  have start : BitVec.ofNat 64 ip =
      Extracted.textAddress + BitVec.ofNat 64 (ip - 0x100000) := by
    change BitVec.ofNat 64 ip = BitVec.ofNat 64 0x100000 + _
    rw [← BitVec.ofNat_add, Nat.add_sub_cancel' low]
  intro i hi
  rw [start, BitVec.add_assoc, ← BitVec.ofNat_add]
  exact inProgram_of_textOffset _ (by omega)

theorem codeApart (pre : CalleePre initial boundary 0x10dd90 144 176 1264)
    (state : Suffix.State initial boundary s) (offset len ip codeLen : Nat)
    (high : offset + len ≤ 416) (codeLow : 0x100000 ≤ ip)
    (codeHigh : ip + codeLen ≤ 0x100000 + 115149) :
    RangeApart (stackPtr s + BitVec.ofNat 64 offset) len
      (BitVec.ofNat 64 ip) codeLen :=
  local_codeApart .hmac pre state.rsp offset len _ codeLen high
    (code_span ip codeLen codeLow codeHigh)

omit [Bindings] in
def writes (initial : RamState) : Vector MemoryRegion 1 :=
  #v[⟨(stackPtr initial - 400).toNat, 128⟩]

theorem writes_component (pre : CalleePre initial boundary 0x10dd90 144 176 1264)
    (state : Suffix.State initial boundary s) (offset len : Nat)
    (low : 8 ≤ offset) (high : offset + len ≤ 136) :
    ∀ a, (Component.mem (stackPtr s + BitVec.ofNat 64 offset) len).Covers a →
      ∃ region ∈ writes initial, region.Contains a.toNat := by
  have bound := (local_bounds .hmac pre state.rsp).2
  simp only [StreamPadding.Variant.frame] at bound
  intro a covered
  refine ⟨⟨(stackPtr initial - 400).toNat, 128⟩, by simp [writes], ?_⟩
  have contains := offset_component (stackPtr s) offset len 8 128 (by omega)
    low high a covered
  have base : stackPtr s + BitVec.ofNat 64 8 = stackPtr initial - 400 := by
    simpa only [Nat.reduceSub, BitVec.ofNat_eq_ofNat] using address state 8 (by decide)
  rwa [base] at contains

theorem writes_within (pre : CalleePre initial boundary 0x10dd90 144 176 1264) :
    ∀ region ∈ writes initial, ∀ a, region.Contains a →
      ∃ outer ∈ #v[registerRegion initial .rdi 176, Stack.region initial 1264],
        outer.Contains a := by
  intro region member a contains
  have eq : region = ⟨(stackPtr initial - 400).toNat, 128⟩ := by
    simpa only [writes, Vector.mem_mk, List.mem_toArray, List.mem_cons,
      List.not_mem_nil, or_false] using member
  subst region
  refine ⟨Stack.region initial 1264, by simp, ?_⟩
  have low : 1264 ≤ (stackPtr initial).toNat := pre.stack.2.2.1
  have ptr : (stackPtr initial - 400).toNat = (stackPtr initial).toNat - 400 := by
    simpa only [BitVec.ofNat_eq_ofNat] using
      stack_sub_toNat pre.stack (offset := 400) (by decide)
  change (stackPtr initial - 400).toNat ≤ a ∧
    a < (stackPtr initial - 400).toNat + 128 at contains
  rw [ptr] at contains
  change (stackPtr initial).toNat - 1264 ≤ a ∧
    a < (Stack.region initial 1264).start + (Stack.region initial 1264).size
  rw [Hkdf.Proofs.Common.Machine.stack_region_end]
  constructor <;> omega

theorem agrees_above (pre : CalleePre initial boundary 0x10dd90 144 176 1264)
    (frame : MemoryWriteFrame s t (writes initial)) (offset len : Nat)
    (low : offset ≤ 272) (high : len ≤ offset + 8) :
    (Component.mem (stackPtr initial - BitVec.ofNat 64 offset) len).Agrees s t := by
  have bounds := stack_bounds pre.stack
  have pointer := stack_sub_toNat pre.stack (offset := offset) (by omega)
  apply frame_agrees_of_disjoint frame
  · rw [pointer]
    omega
  · intro region member a contains written
    have eq : region = ⟨(stackPtr initial - 400).toNat, 128⟩ := by
      simpa only [writes, Vector.mem_mk, List.mem_toArray, List.mem_cons,
        List.not_mem_nil, or_false] using member
    subst region
    change (stackPtr initial - BitVec.ofNat 64 offset).toNat ≤ a ∧
      a < (stackPtr initial - BitVec.ofNat 64 offset).toNat + len at contains
    change (stackPtr initial - 400).toNat ≤ a ∧
      a < (stackPtr initial - 400).toNat + 128 at written
    rw [pointer] at contains
    have ptr : (stackPtr initial - 400).toNat = (stackPtr initial).toNat - 400 := by
      simpa only [BitVec.ofNat_eq_ofNat] using
        stack_sub_toNat pre.stack (offset := 400) (by decide)
    rw [ptr] at written
    omega

theorem state_of_local (pre : CalleePre initial boundary 0x10dd90 144 176 1264)
    (state : Suffix.State initial boundary s) {fuel : Nat} {components : List Component}
    (run : Advances boundary fuel s t) (ready : ReadyToStep t)
    (agrees : AgreesExcept components s t)
    (footprint : WritesWithin components (writes initial))
    (kept : ∀ c ∈ ([.reg 4, .reg 3, .reg 5, .mxcsr, .fcw, .df] : List Component),
      c ∉ components) : Suffix.State initial boundary t := by
  apply state.of_agrees pre run ready agrees ?_ kept
    (agrees_above pre (agrees.memoryWriteFrame footprint) 40 48 (by decide) (by decide))
  intro c member a covered
  obtain ⟨region, hr, contains⟩ := footprint c member a covered
  exact writes_within pre region hr a.toNat contains

theorem hash_of_frame (pre : CalleePre initial boundary 0x10dd90 144 176 1264)
    (frame : MemoryWriteFrame s t (writes initial)) {hash : Array UInt32}
    (words : HashStateAt s (stackPtr initial - 232) hash) :
    HashStateAt t (stackPtr initial - 232) hash :=
  Hkdf.Proofs.Common.hashState_of_bytes words
    (agrees_above pre frame 232 32 (by decide) (by decide))

end Hkdf.Proofs.Standard.Finalize.Suffix.Outer.Prepare
