import P256.Proofs.Verifying.Combination.Naf.Serialize.Reverse.Interface
import P256.Proofs.Common.Curve.LinearCombination.NafReverse.Load
import P256.Proofs.Verifying.Combination.Naf.Serialize.Reverse.Rotate
import P256.Proofs.Common.Curve.LinearCombination.NafReverse.Store
import P256.Proofs.Common.Encoding.Serialize.Tail.ByteOps.Store
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Program.Code

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Serialize.Reverse

open P256.Proofs.Common.Curve.LinearCombination.NafReverse

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs
open P256.Proofs.Common.Instructions
open P256.Proofs.Common.Instructions.CrossPageStore (Writable)

theorem Pre.slot {s : RamState} {entry : BitVec 64} (pre : Pre s entry)
    (offset len : Nat) (lo : 8 ≤ offset) (hi : offset + len ≤ 40) :
    Writable s (stackPtr s + BitVec.ofNat 64 offset) len := by
  have h := pre.writable.add (offset-8) (len := len) (by omega)
  change Writable s (stackPtr s + BitVec.ofNat 64 8 + BitVec.ofNat 64 (offset-8)) len at h
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_of_le lo] at h
  exact h

theorem Pre.code {s : RamState} {entry : BitVec 64} (pre : Pre s entry)
    (offset len codeOffset codeLen : Nat) (lo : 8 ≤ offset) (hi : offset + len ≤ 40)
    (bound : codeOffset + codeLen ≤ 264) :
    RangeApart (stackPtr s + BitVec.ofNat 64 offset) len
      (0x10b1cf + BitVec.ofNat 64 codeOffset) codeLen := by
  have h := RangeApart.add_left (h := pre.apart) (offset-8) (len := len) (by omega)
  change RangeApart (stackPtr s + BitVec.ofNat 64 8 + BitVec.ofNat 64 (offset-8)) len 0x10b1cf 264 at h
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_sub_of_le lo] at h
  intro i hi j hj
  simpa only [BitVec.add_assoc, ← BitVec.ofNat_add] using h i hi (codeOffset+j) (by omega)

theorem Pre.byte_writable {s : RamState} {entry : BitVec 64} (pre : Pre s entry)
    (offset : Nat) (lo : 8 ≤ offset) (hi : offset < 40) :
    MemWritable s (stackPtr s + BitVec.ofNat 64 offset) 1 := by
  have hw := pre.slot offset 1 lo (by omega)
  exact ⟨hw.low, hw.mem, hw.tables⟩

theorem frame_of_effect {e : Effect} {s t : RamState} (h : e.Holds s t)
    (registers : ∀ c ∈ e.components, c.isMem = false → c ∈ footprint s)
    (memory : ∀ c ∈ e.components, ∀ a, c.Covers a →
      (Component.mem (stackPtr s + 8) 32).Covers a) :
    AgreesExcept (footprint s) s t := by
  refine ⟨?_, ?_, h.agrees.rest, h.agrees.grow⟩
  · intro c hc hm
    exact h.agrees.agree c (fun hmem => hc (registers c hmem hm)) hm
  · intro a ha
    exact h.agrees.memory a (fun c hc covered =>
      ha _ (by simp [footprint]) (memory c hc a covered))

theorem Pre.after {s t : RamState} {entry next : BitVec 64} (pre : Pre s entry)
    (agrees : AgreesExcept (footprint s) s t) (rip : t.RIP = next) : Pre t next := by
  have rsp : stackPtr t = stackPtr s := agrees.read (n := 64) (r := 4) (by simp [footprint])
  refine ⟨rip, ?_, ?_⟩
  · rw [rsp]
    exact ⟨⟨pre.writable.low, fun i hi => agrees.grow _ (pre.writable.mem i hi)⟩, pre.writable.tables⟩
  · rw [rsp]
    exact pre.apart

theorem footprint_trans {s t u : RamState}
    (left : AgreesExcept (footprint s) s t) (right : AgreesExcept (footprint t) t u) :
    AgreesExcept (footprint s) s u := by
  have rsp : stackPtr t = stackPtr s := left.read (n := 64) (r := 4) (by simp [footprint])
  have hf : footprint t = footprint s := by simp only [footprint, rsp]
  rw [hf] at right
  exact (left.trans right).mono (by simp)

theorem storedByte_rotate16 (v : BitVec 16) (i : Nat) (hi : i < 2) :
    storedByte (v.rotateLeft 8) i = storedByte v (1-i) := by
  rw [storedByte_eq_extract, storedByte_eq_extract]
  congr 1
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [BitVec.getLsbD_extractLsb', hk, decide_true, Bool.true_and,
    BitVec.getLsbD_rotateLeft]
  simp only [Nat.reduceMod]
  split
  · congr 1
    omega
  · rw [show decide (8*i+k < 16) = true from decide_eq_true (by omega), Bool.true_and]
    congr 1
    omega

theorem rotated_load_byte {s t : RamState} {a b : BitVec 64}
    (h : memLoad t.external a 16 = (memLoad s.external b 16).rotateLeft 8)
    (i : Nat) (hi : i < 2) :
    memByte t.external (a + BitVec.ofNat 64 i) =
      memByte s.external (b + BitVec.ofNat 64 (1-i)) := by
  rw [← storedByte_memLoad t.external a (n := 16) i hi, h, storedByte_rotate16 _ i hi,
    storedByte_memLoad s.external b (n := 16) (1-i) (by omega)]

theorem mergeGPR_low16 (v : BitVec 16) (old : BitVec 64) :
    (mergeGPR 16 v old).setWidth 16 = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  simp only [mergeGPR, show ¬ (16 : Nat) = 32 by decide, ite_false, BitVec.getLsbD_setWidth,
    getLsbD_setSlice _ _ _ _ _ (by omega : k < 64)]
  simp [hk]

attribute [x86_compose] mergeGPR_low16

@[x86_local] theorem byteStore_local (p : BitVec 64) (len : Nat) (am : AddrMode) (src : BitVec 5) :
    Effect.Local (storeEffect p len (storeAddrAt p am len)
      (fun s => (Operand.reg src : Operand 8).read s)) := by
  apply P256.Proofs.Common.EffectCompose.Effect.Local.of_eq
  · intro s t h
    simp only [storeEffect, storeAddrAt, AddrMode.addr_obs h, h.read_reg]
  · intro s
    simp [storeEffect, Write.Full, Operand.Full]

def segmentIndex (lo hi i : Nat) : Nat :=
  if (lo ≤ i ∧ i < hi) ∨ (32-hi ≤ i ∧ i < 32-lo) then 31-i else i

theorem segmentIndex_lt (lo hi : Nat) {i : Nat} (bound : i < 32) :
    segmentIndex lo hi i < 32 := by
  unfold segmentIndex
  split <;> omega

structure SegmentPost (s t : RamState) (next : BitVec 64) (lo hi : Nat) : Prop where
  rip : t.RIP = next
  agrees : AgreesExcept (footprint s) s t
  bytes : Bytes t.external (stackPtr s + 8) 32
    (fun i => memByte s.external (stackPtr s + 8 + BitVec.ofNat 64 (segmentIndex lo hi i)))

theorem SegmentPost.map_bytes {s t : RamState} {next : BitVec 64} {lo hi : Nat}
    (post : SegmentPost s t next lo hi) {f : Nat → UInt8}
    (bytes : Bytes s.external (stackPtr s+8) 32 f) :
    Bytes t.external (stackPtr s+8) 32 (fun i => f (segmentIndex lo hi i)) := by
  apply post.bytes.congr
  intro i hi'
  change (s.external[stackPtr s+8+BitVec.ofNat 64 (segmentIndex lo hi i)]?).getD 0 = _
  rw [bytes _ (segmentIndex_lt lo hi hi')]
  rfl

end P256.Proofs.Verifying.Combination.Naf.Serialize.Reverse
