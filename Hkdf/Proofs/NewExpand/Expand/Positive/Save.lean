import Hkdf.Proofs.NewExpand.Expand.Positive.Save.Execution
import Hkdf.Proofs.NewExpand.Expand.Positive.Branch
import Hkdf.Proofs.NewExpand.Expand.LoopState
import Hkdf.Proofs.Common.Machine.StackRegion

namespace Hkdf.Proofs.NewExpand.Expand

open Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Machine

private theorem saves_in_digest {s : RamState} {c : Component} {a : BitVec 64}
    (member : c ∈ (saveEffect s).components) (covers : c.Covers a) :
    ∃ j < 32, a = rspOf s + 456 + BitVec.ofNat 64 j := by
  simp only [saveEffect, Effect.components, List.map_cons, List.map_nil,
    Write.component, Operand.component, Nat.reduceDiv, List.cons_append, List.nil_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact covers.elim
  all_goals obtain ⟨i, hi, rfl⟩ := covers
  · exact ⟨i, by omega, rfl⟩
  · exact ⟨8+i, by omega, by rw [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.add_assoc (rspOf s) 456]; rfl⟩
  · exact ⟨16+i, by omega, by rw [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.add_assoc (rspOf s) 456]; rfl⟩
  · exact ⟨24+i, by omega, by rw [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.add_assoc (rspOf s) 456]; rfl⟩

private theorem save_digest {s t : RamState} {bytes : ByteArray}
    (eff : (saveEffect s).Holds s t)
    (source : (⟨(rspOf s + 16).toNat, 32⟩ : MemoryRegion).HasBytes s.external bytes)
    (allocated : ∀ j < 32, (t.external[rspOf s + 456 + BitVec.ofNat 64 j]?).isSome) :
    (⟨(rspOf s + 456).toNat, 32⟩ : MemoryRegion).HasBytes t.external bytes := by
  have size : bytes.size = 32 := source.1
  obtain ⟨_, _, _, _, _, w0, w1, w2, w3⟩ := eff.writes
  have words (j : Nat) (hj : j < 4) :
      memLoad t.external (rspOf s + 456 + BitVec.ofNat 64 (8 * j)) 64 =
        memLoad s.external (rspOf s + 16 + BitVec.ofNat 64 (8 * j)) 64 := by
    rcases (by omega : j=0 ∨ j=1 ∨ j=2 ∨ j=3) with rfl | rfl | rfl | rfl
    all_goals simp only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc,
      BitVec.reduceAdd, BitVec.add_zero]
    · exact w0
    · exact w1
    · exact w2
    · exact w3
  have input (i : Nat) (hi : i < 32) :
      s.external[rspOf s + 16 + BitVec.ofNat 64 i]? = some (bytes[i]'(by omega)) := by
    simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using source.2 ⟨i, by omega⟩
  refine ⟨size, fun i => ?_⟩
  have hi : i.val < 32 := by omega
  have dest := Bytes.of_memLoad (n := 64) (a := rspOf s + 456 + BitVec.ofNat 64 (8*(i.val/8)))
    (m := t.external) (by
      intro j hj
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact allocated _ (by omega))
  have src := Bytes.of_memLoad (n := 64) (a := rspOf s + 16 + BitVec.ofNat 64 (8*(i.val/8)))
    (m := s.external) (by
      intro j hj
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, input _ (by omega)]
      trivial)
  have equal := dest (i.val % 8) (by omega)
  rw [words _ (by omega), ← src (i.val % 8) (by omega)] at equal
  rw [BitVec.add_assoc (rspOf s + 456), BitVec.add_assoc (rspOf s + 16), ← BitVec.ofNat_add,
    show 8*(i.val/8)+i.val%8=i.val by omega, input i.val hi] at equal
  simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using equal

theorem finishRound [Bindings] {entry old s : RamState} {boundary : ReturnBoundary}
    {key info : ByteArray} {ptr : BitVec 64} {length n : Nat}
    (pre : ExpandPre entry boundary key info ptr length)
    (head : LoopState entry old boundary key info length n)
    (saved : SavedFrame entry s boundary length) (pc : s.RIP = 0x10f548)
    (more : 32*n < length) (bound : length ≤ 8160)
    (locals : ∀ i ∈ ([232, 240, 248, 416, 424, 440] : List (BitVec 64)), slot s i = slot old i)
    (copyPtr : s.regValue .r12 = 0x10dd60)
    (counter : slot s 256 = BitVec.ofNat 64 (n+1))
    (remaining : slot s 8 = BitVec.ofNat 64 (length - 32*(n+1)))
    (nextPtr : s.regValue .rbp = entry.regValue .rcx + BitVec.ofNat 64 (min (32*(n+1)) length))
    (digest : (⟨(rspOf s + 16).toNat, 32⟩ : MemoryRegion).HasBytes s.external
      (blocks .sha256 key info (n+1)).2)
    (output : (registerRegion entry .rcx (min (32*(n+1)) length)).HasBytes s.external
      ((blocks .sha256 key info (n+1)).1.extract 0 length)) :
    ∃ t, LoopState entry t boundary key info length (n+1) := by
  obtain ⟨fuel, u, saveRun, readyU, effect⟩ := saveRound pre saved pc
  obtain ⟨alU, _, _, r15U, rbpU, _⟩ := effect.writes
  have remainingU : u.regValue .rbp = BitVec.ofNat 64 (length - 32*(n+1)) := rbpU.trans remaining
  have spS : rspOf s = stackPtr entry - 536 := saved.sp
  have endBase : rspOf s + 456 = stackPtr entry - 80 := by rw [spS]; bv_omega
  have inStack (a : BitVec 64) (j : Nat) (hj : j < 32)
      (eq : a = rspOf s + 456 + BitVec.ofNat 64 j) : (Stack.region entry 2264).Contains a.toNat :=
    stackRegion_contains_sub pre.call.stack.2.2.1 (offset := 80) (len := 32)
      (by decide) (by decide) ⟨j, hj, by rwa [endBase] at eq⟩
  have footprint : WritesWithin (saveEffect s).components #v[Stack.region entry 2264] := by
    intro c hc a cover
    obtain ⟨j, hj, ha⟩ := saves_in_digest hc cover
    exact ⟨_, by simp, inStack a j hj ha⟩
  have avoids : ∀ region ∈ #v[registerRegion entry .rcx (writtenLength length),
      Stack.region entry 2264], region.Avoids InProgram := by
    have sep := (pre.separation (by omega) bound).2
    simp only [writtenLength, bound, ↓reduceIte]
    exact fun r hr a ha hin => (sep r hr).2 a ha (.inl hin)
  have runningU := saved.toRunning.of_agrees saveRun readyU effect.agrees (by
    intro c hc a cover
    obtain ⟨j, hj, ha⟩ := saves_in_digest hc cover
    exact ⟨Stack.region entry 2264, by simp, inStack a j hj ha⟩) avoids
    (by simp [saveEffect, Effect.components])
  obtain ⟨t, branch, readyT, pcT, branchFrame⟩ := roundBranch readyU runningU.loaded
    pre.call.outerBoundary effect.rip remainingU (by omega)
  have runningT := runningU.of_agrees branch readyT branchFrame (by
    intro c hc a cover
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl <;> exact cover.elim) avoids (by decide)
  have memory := branchFrame.external (by simp [Component.Covers])
  have ag := effect.agrees.trans branchFrame
  have sp : t.regValue .rsp = s.regValue .rsp := ag.read (n := 64) (r := 4)
    (by simp [saveEffect, Effect.components])
  have same (off len : Nat) (hi : off + len ≤ 544) (apart : off+len ≤ 456 ∨ 488 ≤ off) :
      (Component.mem (rspOf s + BitVec.ofNat 64 off) len).Agrees s t := by
    intro i hi'
    rw [memory]
    apply effect.agrees.byte
    intro c hc cover
    obtain ⟨j, hj, eq⟩ := saves_in_digest hc cover
    exact (RangeApart.offsets (rspOf s) (a := off) (len := len) (b := 456) (count := 32)
      (by omega) (by decide) apart) i hi' j hj eq
  have fixed (off : Nat) (hi : off + 8 ≤ 456) : slot t (BitVec.ofNat 64 off) = slot s (BitVec.ofNat 64 off) := by
    change memLoad t.external (t.regValue .rsp + _) 64 = _
    rw [sp]
    exact Common.CallFrame.agrees_memLoad (same off 8 (by omega) (Or.inl hi))
  have savedT := saved.of_agreement runningT sp (same 488 56 (by decide) (by decide))
    (fixed 224 (by decide)) (ag.mxcsr (by simp [saveEffect, Effect.components]))
    (ag.fcw (by simp [saveEffect, Effect.components]))
  have data := save_digest effect digest (by
    intro j hj
    rw [endBase]
    exact (Common.CallFrame.stack_readable pre.call.stack runningU.allocated
      (offset := 80) (len := 32) (by decide) (by decide)).mem j hj)
  have previous : (⟨(t.regValue .rsp + 456).toNat, (blocks .sha256 key info (n+1)).2.size⟩ :
      MemoryRegion).HasBytes t.external (blocks .sha256 key info (n+1)).2 := by
    rw [sp, blocks_sha256_previous_size key info (Nat.zero_lt_succ n), memory]
    exact data
  have outputDisjoint := (pre.separation (by omega) bound).1 0 1 (by decide)
  have outputBound := (pre.output (by omega) bound).1
  change (entry.regValue .rcx).toNat + length < 2^32 at outputBound
  have outputT := Common.CallFrame.frame_hasBytes (effect.agrees.memoryWriteFrame footprint)
    (region := registerRegion entry .rcx (min (32*(n+1)) length)) (by
      intro r hr
      rcases Vector.mem_singleton.mp hr with rfl
      intro a ha
      apply outputDisjoint a
      exact ⟨ha.1, Nat.lt_of_lt_of_le ha.2 (Nat.add_le_add_left (Nat.min_le_right _ _) _)⟩)
    (by change (entry.regValue .rcx).toNat + min _ length ≤ _; omega) output
  refine ⟨t, {
    toSavedFrame := savedT
    contextPtr := (fixed 240 (by decide)).trans ((locals 240 (by decide)).trans head.contextPtr)
    descriptors := (fixed 232 (by decide)).trans ((locals 232 (by decide)).trans head.descriptors)
    count := (fixed 248 (by decide)).trans ((locals 248 (by decide)).trans head.count)
    innerPtr := (fixed 424 (by decide)).trans ((locals 424 (by decide)).trans head.innerPtr)
    outerPtr := (fixed 416 (by decide)).trans ((locals 416 (by decide)).trans head.outerPtr)
    tableEnd := (fixed 440 (by decide)).trans ((locals 440 (by decide)).trans head.tableEnd)
    memcpy := (ag.read (r := 12) (n := 64) (by simp [saveEffect, Effect.components])).trans copyPtr
    counter := (fixed 256 (by decide)).trans counter
    pc := pcT
    outputPtr := (branchFrame.read (r := 15) (n := 64) (by decide)).trans (r15U.trans nextPtr)
    remaining := (branchFrame.read (r := 5) (n := 64) (by decide)).trans remainingU
    flag := ?_
    previous := previous
    output := memory ▸ outputT }⟩
  change (t.regValue .rax).setWidth 8 = 1
  have ax : t.regValue .rax = u.regValue .rax := branchFrame.read (r := 0) (n := 64) (by decide)
  rw [ax, show u.regValue .rax = _ from alU, setWidth_mergeGPR8]

end Hkdf.Proofs.NewExpand.Expand
