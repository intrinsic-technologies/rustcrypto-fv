import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Finalize.Mark.Instructions
import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Finalize.Mark.Fill
import Hkdf.Proofs.Common.State
import Hkdf.Proofs.Common.StreamPadding.Mathematics

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Expand.Finalize.InnerPadding

open Hkdf.Spec.Program Hkdf.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common Hkdf.Proofs.Common.Machine Hkdf.Proofs.Common.CallFrame
open Hkdf.Proofs.Common.SHA256 Hkdf.Proofs.Common.StreamPadding

def writes (p : BitVec 64) : Vector MemoryRegion 2 :=
  #v[⟨(p + 80).toNat, 64⟩, ⟨(p - 8).toNat, 8⟩]

structure Result [Bindings] {n : Nat} (entry s t : RamState) (boundary : ReturnBoundary)
    (regions : Vector MemoryRegion n) (message : ByteArray) : Prop where
  execution : ∃ fuel, Advances boundary fuel s t
  running : Running entry boundary regions t
  rip : t.RIP = (if message.size % 64 < 56 then 0x10f320 else 0x10f995)
  rsp : stackPtr t = stackPtr s
  length : t.regValue .r15 = BitVec.ofNat 64 (message.size % 64)
  blocks : t.regValue .r13 = BitVec.ofNat 64 (message.size / 64)
  r12 : t.regValue .r12 = s.regValue .r12
  r14 : t.regValue .r14 = s.regValue .r14
  rbp : t.regValue .rbp = s.regValue .rbp
  mxcsr : t.MXCSR = s.MXCSR
  fcw : t.FP87_Control = s.FP87_Control
  frame : MemoryWriteFrame s t (writes (stackPtr s))
  hash : HashStateAt t (stackPtr t + 144)
    (compressBlocks Hkdf.Proofs.NIST.SHA256.initialHash message)
  padded : (⟨(stackPtr t + 80).toNat, 64⟩ : MemoryRegion).HasBytes
    t.external (paddedBuffer message)

private theorem local_nat {p : BitVec 64} (high : p.toNat + 544 < 2^32)
    (offset : Nat) (bound : offset ≤ 544) :
    (p + BitVec.ofNat 64 offset).toNat = p.toNat + offset := by
  rw [BitVec.toNat_add, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt (by omega : offset < 2^64), Nat.mod_eq_of_lt (by omega)]

private theorem before_write {s t : RamState} {p : BitVec 64} {offset len pos count ret : Nat}
    (high : p.toNat + 544 < 2^32) (low : 8 ≤ p.toNat) (retBound : ret ≤ 8)
    (inside : offset + len ≤ 544) (posBound : pos ≤ 544)
    (apart : offset + len ≤ pos ∨ pos + count ≤ offset)
    (effect : MemoryWriteFrame s t #v[
      ⟨(p + BitVec.ofNat 64 pos).toNat, count⟩, ⟨(p - 8).toNat, ret⟩]) :
    (Component.mem (p + BitVec.ofNat 64 offset) len).Agrees s t := by
  have subNat : (p - 8).toNat = p.toNat - 8 := by
    rw [BitVec.toNat_sub_of_le (by simpa only [BitVec.le_def, BitVec.reduceToNat] using low)]
    rfl
  apply frame_agrees_of_disjoint effect
  · rw [local_nat high offset (by omega)]
    omega
  · intro region member a ha hb
    have cases : region = (⟨(p + BitVec.ofNat 64 pos).toNat, count⟩ : MemoryRegion) ∨
        region = (⟨(p - 8).toNat, ret⟩ : MemoryRegion) := by simpa using member
    change (p + BitVec.ofNat 64 offset).toNat ≤ a ∧
      a < (p + BitVec.ofNat 64 offset).toNat + len at ha
    rw [local_nat high offset (by omega)] at ha
    rcases cases with rfl | rfl
    · change (p + BitVec.ofNat 64 pos).toNat ≤ a ∧
        a < (p + BitVec.ofNat 64 pos).toNat + count at hb
      rw [local_nat high pos posBound] at hb
      omega
    · change (p - 8).toNat ≤ a ∧ a < (p - 8).toNat + ret at hb
      rw [subNat] at hb
      omega

private theorem widen_tail {s t : RamState} (p : BitVec 64) (high : p.toNat + 544 < 2^32)
    {pos count ret : Nat} (posLower : 80 ≤ pos) (tailEnd : pos + count ≤ 144)
    (retBound : ret ≤ 8)
    (frame : MemoryWriteFrame s t #v[
      ⟨(p + BitVec.ofNat 64 pos).toNat, count⟩, ⟨(p - 8).toNat, ret⟩]) :
    MemoryWriteFrame s t (writes p) := by
  apply frame_mono frame
  intro region member a contains
  have cases : region = (⟨(p + BitVec.ofNat 64 pos).toNat, count⟩ : MemoryRegion) ∨
      region = (⟨(p - 8).toNat, ret⟩ : MemoryRegion) := by simpa using member
  rcases cases with rfl | rfl
  · refine ⟨⟨(p + 80).toNat, 64⟩, by simp [writes], ?_⟩
    change (p + BitVec.ofNat 64 pos).toNat ≤ a ∧
      a < (p + BitVec.ofNat 64 pos).toNat + count at contains
    change (p + BitVec.ofNat 64 80).toNat ≤ a ∧ a < (p + BitVec.ofNat 64 80).toNat + 64
    rw [local_nat high pos (by omega)] at contains
    rw [local_nat high 80 (by decide)]
    omega
  · refine ⟨⟨(p - 8).toNat, 8⟩, by simp [writes], ?_⟩
    change (p - 8).toNat ≤ a ∧ a < (p - 8).toNat + 8
    change (p - 8).toNat ≤ a ∧ a < (p - 8).toNat + ret at contains
    omega

private theorem mark_components (s : RamState) :
    (markEffect s).components = [.mem (markerAddress s) 1, .reg 7, .reg 6,
      .reg 2, .flags, .rip] := by
  simp [markEffect, Effect.components, Write.component, Operand.component]

private theorem mark_cover {s : RamState} {c : Component} {a : BitVec 64}
    (member : c ∈ (markEffect s).components) (covered : c.Covers a) :
    (Component.mem (markerAddress s) 1).Covers a := by
  rw [mark_components] at member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact covered
  all_goals exact covered.elim

private theorem marked_byte {s t : RamState} (effect : (markEffect s).Holds s t) :
    t.external[markerAddress s]? = some 128 := by
  have marker := effect.writes.1
  change memLoad t.external (markerAddress s) 8 = 128 at marker
  rw [memLoad_8] at marker
  have byte : memByte t.external (markerAddress s) = 128 := UInt8.toBitVec_inj.mp marker
  cases found : t.external[markerAddress s]? with
  | none =>
    simp only [memByte, PhysicalMemory.read, found, Option.getD_none] at byte
    exact False.elim ((by decide : (0 : UInt8) ≠ 128) byte)
  | some value =>
    simpa only [memByte, PhysicalMemory.read, found, Option.getD_some] using congrArg some byte

private theorem length_of_stream {s : RamState} {message : ByteArray}
    (stream : StreamAt s (stackPtr s + 80) message) :
    loadLength s = BitVec.ofNat 64 (message.size % 64) := by
  rw [loadLength, memLoad_8]
  change ((s.external[stackPtr s + 143]?).getD (0 : UInt8)).toBitVec.setWidth 64 = _
  have tail := stream.tailLength
  rw [show stackPtr s + 80 + 63 = stackPtr s + 143 by bv_omega] at tail
  rw [tail]
  simp only [Option.getD_some]
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat, UInt8.toNat_toBitVec, UInt8.toNat_ofNat']
  have := Nat.mod_lt message.size (by decide : 0 < 64)
  omega

theorem run [bindings : Bindings] {entry s : RamState} {boundary : ReturnBoundary}
    {n : Nat} {regions : Vector MemoryRegion n} {message : ByteArray}
    (stack : Stack.Valid entry 2264)
    (avoid : (Stack.region entry 2264).Avoids (fun a ↦ InProgram a ∨ InPageTables a))
    (stackIn : Stack.region entry 2264 ∈ regions)
    (avoids : ∀ region ∈ regions, region.Avoids InProgram)
    (outside : ¬ InProgram boundary.rip) (stride : UnitStringStride bindings)
    (running : Running entry boundary regions s)
    (rsp : stackPtr s = stackPtr entry - 536) (rip : s.RIP = 0x10f95a)
    (stream : StreamAt s (stackPtr s + 80) message) :
    ∃ t, Result entry s t boundary regions message := by
  let rem := message.size % 64
  have small : rem < 64 := Nat.mod_lt _ (by decide)
  have stackBase : (stackPtr s).toNat = (stackPtr entry).toNat - 536 := by
    rw [rsp]
    exact stack_sub_toNat stack (by decide)
  obtain ⟨stackLow, stackHigh⟩ := stack_bounds stack
  have low : 8 ≤ (stackPtr s).toNat := by omega
  have high : (stackPtr s).toNat + 544 < 2^32 := by omega
  have loadPre : LoadPre s := ⟨rip, by
    change MemReadable s (stackPtr s + BitVec.ofNat 64 143) 1
    rw [local_address rsp 143 (by decide)]
    exact stack_readable stack running.allocated (by decide) (by decide), by
    change MemReadable s (stackPtr s + BitVec.ofNat 64 176) 8
    rw [local_address rsp 176 (by decide)]
    exact stack_readable stack running.allocated (by decide) (by decide)⟩
  obtain ⟨lFuel, l, lRun, lReady, _, lEffect⟩ := load_run boundary outside s
    (supportedMachine_readyToStep running.machine) (load_code running.loaded) loadPre
  have loadNoMem : ∀ c ∈ (loadEffect s).components, ∀ a, ¬ c.Covers a := by
    simp [loadEffect, Effect.components, Write.component, Operand.component, Component.Covers]
  have lRunning := running.of_agrees lRun lReady lEffect.agrees
    (fun c hc a ha ↦ (loadNoMem c hc a ha).elim) avoids (by simp [loadEffect, Effect.components])
  have lRsp : stackPtr l = stackPtr s := lEffect.agrees.read (n := 64) (r := 4)
    (by simp [loadEffect, Effect.components])
  have lLength : l.regValue .r15 = BitVec.ofNat 64 rem :=
    lEffect.writes.1.trans (length_of_stream stream)
  have lBlocks : l.regValue .r13 = BitVec.ofNat 64 (message.size / 64) := by
    apply lEffect.writes.2.1.trans
    apply Hkdf.Proofs.Common.Memory.memLoad_of_loadBytes64
    change X86.Machine.loadBytes s.external (stackPtr s + 176) 8 = _
    rw [show stackPtr s + 176 = stackPtr s + 80 + 96 by bv_omega]
    exact stream.blocks
  have lZeros : l.regValue .rbx = BitVec.ofNat 64 (63 - rem) := by
    change l.regValue .rbx = _
    rw [show l.regValue .rbx = loadLength s ^^^ 63 from lEffect.writes.2.2, length_of_stream stream]
    exact tail_zero_count rem small
  have lMemory := lEffect.agrees.external loadNoMem
  have marker : markerAddress l = stackPtr s + BitVec.ofNat 64 (80 + rem) := by
    change stackPtr l + (l.regValue .r15 + 80) = _
    rw [lRsp, lLength, BitVec.ofNat_add]
    bv_omega
  have markStack : markerAddress l = stackPtr entry - BitVec.ofNat 64 (456 - rem) := by
    rw [marker, local_address rsp _ (by omega), show 536 - (80 + rem) = 456 - rem by omega]
  have markPre : MarkPre l := ⟨lEffect.rip, by
    rw [markStack]
    exact stack_writable1 stack avoid lRunning.allocated (by omega), by
    rw [markStack]
    exact stack_codeApart (codeOffset := 0xf972) stack
      (fun a ha hp ↦ avoid a ha (.inl hp)) (by omega) (by omega) (by decide)⟩
  obtain ⟨mFuel, m, mRun, mReady, _, mEffect⟩ := mark_run boundary outside l
    lReady (mark_code lRunning.loaded) markPre
  have markWrites : WritesWithin (markEffect l).components regions := by
    intro c hc a ha
    have covered := mark_cover hc ha
    rw [markStack] at covered
    exact ⟨_, stackIn, stackRegion_contains_sub stackLow (by omega) (by omega) covered⟩
  have mRunning := lRunning.of_agrees mRun mReady mEffect.agrees markWrites avoids
    (by simp [mark_components])
  have mRsp : stackPtr m = stackPtr s :=
    (mEffect.agrees.read (n := 64) (r := 4) (by simp [mark_components])).trans lRsp
  have destination : m.regValue .rdi = stackPtr m + BitVec.ofNat 64 (80 + (rem + 1)) := by
    have args := mEffect.writes.2.1
    change m.regValue .rdi = stackPtr l + (l.regValue .r15 + 81) at args
    rw [args, lLength, lRsp, mRsp, BitVec.ofNat_add, BitVec.ofNat_add]
    bv_omega
  have length : m.regValue .rdx = BitVec.ofNat 64 (64 - (rem + 1)) :=
    mEffect.writes.2.2.2.trans (lZeros.trans (congrArg (BitVec.ofNat 64) (by omega)))
  obtain ⟨fFuel, f, fRun, fRunning, fRip, fRsp, abi, fFrame, zeros⟩ :=
    fill_run stack avoid stackIn avoids outside stride mRunning (mRsp.trans rsp) (by omega)
      mEffect.rip destination mEffect.writes.2.2.1 length
  obtain ⟨t, bRun, bReady, bRip, bEffect⟩ :=
    branch_run outside (supportedMachine_readyToStep fRunning.machine) fRunning.loaded fRip
  have bNoMem : ∀ c ∈ ([.flags, .rip] : List Component), ∀ a, ¬ c.Covers a := by
    simp [Component.Covers]
  have tRunning := fRunning.of_agrees bRun bReady bEffect
    (fun c hc a ha ↦ (bNoMem c hc a ha).elim) avoids (by simp)
  have tRsp : stackPtr t = stackPtr s :=
    (bEffect.read (n := 64) (r := 4) (by simp)).trans (fRsp.trans mRsp)
  have tMemory := bEffect.external bNoMem
  have fRBX : f.regValue .rbx = BitVec.ofNat 64 (63 - rem) :=
    (abi.1 .rbx (by simp)).trans
      ((mEffect.agrees.read (n := 64) (r := 3) (by simp [mark_components])).trans lZeros)
  have finalRip : t.RIP = (if rem < 56 then 0x10f320 else 0x10f995) := by
    rw [bRip, fRBX, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : 63 - rem < 2^64)]
    by_cases h : rem < 56
    · simp only [h, show ¬63 - rem < 8 by omega, ↓reduceIte]
    · simp only [h, show 63 - rem < 8 by omega, ↓reduceIte]
  have lFrame : MemoryWriteFrame s l (writes (stackPtr s)) :=
    lEffect.agrees.memoryWriteFrame (fun c hc a ha ↦ (loadNoMem c hc a ha).elim)
  have mFrame : MemoryWriteFrame l m #v[
      ⟨(stackPtr s + BitVec.ofNat 64 (80 + rem)).toNat, 1⟩, ⟨(stackPtr s - 8).toNat, 0⟩] := by
    apply mEffect.agrees.memoryWriteFrame
    intro c hc a ha
    refine ⟨⟨(stackPtr s + BitVec.ofNat 64 (80 + rem)).toNat, 1⟩, by simp, ?_⟩
    obtain ⟨i, hi, rfl⟩ := mark_cover hc ha
    have h : i = 0 := by omega
    subst i
    rw [marker]
    change (⟨(stackPtr s + BitVec.ofNat 64 (80 + rem)).toNat, 1⟩ : MemoryRegion).Contains
      (stackPtr s + BitVec.ofNat 64 (80 + rem) + 0#64).toNat
    rw [BitVec.add_zero]
    exact ⟨Nat.le_refl _, Nat.lt_succ_self _⟩
  rw [mRsp] at fFrame zeros
  have tFrame : MemoryWriteFrame f t (writes (stackPtr s)) :=
    bEffect.memoryWriteFrame (fun c hc a ha ↦ (bNoMem c hc a ha).elim)
  have frame := memoryWriteFrame_trans lFrame (memoryWriteFrame_trans
    (widen_tail _ high (by omega) (by omega) (by decide) mFrame)
    (memoryWriteFrame_trans (widen_tail _ high (by omega) (by omega) (by decide) fFrame) tFrame))
  have tHash : HashStateAt t (stackPtr t + 144)
      (compressBlocks Hkdf.Proofs.NIST.SHA256.initialHash message) := by
    rw [tRsp]
    have hash : HashStateAt s (stackPtr s + 144)
        (compressBlocks Hkdf.Proofs.NIST.SHA256.initialHash message) := by
      rw [← show stackPtr s + 80 + 64 = stackPtr s + 144 by bv_omega]
      exact stream.hashWords
    exact hashState_of_bytes hash (before_write high low (ret := 8) (offset := 144) (len := 32)
      (pos := 80) (count := 64) (by decide) (by decide) (by decide) (by decide) frame)
  have keptByMark := before_write high low (offset := 80) (len := rem)
    (by decide : 0 ≤ 8) (by omega) (by omega) (.inl (by omega)) mFrame
  have keptByFill := before_write high low (offset := 80) (len := rem + 1)
    (by decide : 8 ≤ 8) (by omega) (by omega) (.inl (by omega)) fFrame
  have tTail : (⟨(stackPtr s + 80).toNat, rem⟩ : MemoryRegion).HasBytes
      t.external (remainderBytes message) := by
    refine ⟨stream.tail.1, fun i ↦ ?_⟩
    have hi : i.val < rem := by simpa only [remainderBytes_size] using i.isLt
    rw [tMemory]
    have byte := (keptByFill i.val (by omega)).trans ((keptByMark i.val hi).trans
      (congrArg (fun mem : Ram => mem[stackPtr s + 80 + BitVec.ofNat 64 i.val]?) lMemory))
    simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.ofNat_eq_ofNat] using
      byte.trans (by
        simpa only [remainderBytes, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using stream.tail.2 i)
  have tMarker : t.external[stackPtr s + 80 + BitVec.ofNat 64 rem]? = some 128 := by
    rw [tMemory]
    have same := keptByFill rem (by omega)
    have stored := marked_byte mEffect
    rw [marker, BitVec.ofNat_add, ← BitVec.add_assoc] at stored
    exact same.trans stored
  have tPadded : (⟨(stackPtr t + 80).toNat, 64⟩ : MemoryRegion).HasBytes
      t.external (paddedBuffer message) := by
    rw [tRsp]
    apply padded_bytes tTail tMarker
    intro i hi
    rw [tMemory]
    have byte := zeros i (by omega)
    simpa only [BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using byte
  have tLength : t.regValue .r15 = BitVec.ofNat 64 rem :=
    (bEffect.read (n := 64) (r := 15) (by simp)).trans ((abi.1 .r15 (by simp)).trans
      ((mEffect.agrees.read (n := 64) (r := 15) (by simp [mark_components])).trans lLength))
  have tBlocks : t.regValue .r13 = BitVec.ofNat 64 (message.size / 64) :=
    (bEffect.read (n := 64) (r := 13) (by simp)).trans ((abi.1 .r13 (by simp)).trans
      ((mEffect.agrees.read (n := 64) (r := 13) (by simp [mark_components])).trans lBlocks))
  have beforeCall := lEffect.agrees.trans mEffect.agrees
  refine ⟨t, ⟨⟨_, ((lRun.trans mRun).trans fRun).trans bRun⟩, tRunning,
    finalRip, tRsp, tLength, tBlocks, ?_, ?_, ?_, ?_, ?_, frame, tHash, tPadded⟩⟩
  · exact (bEffect.read (n := 64) (r := 12) (by simp)).trans ((abi.1 .r12 (by simp)).trans
      (beforeCall.read (n := 64) (r := 12) (by rw [List.mem_append, mark_components]; simp [loadEffect, Effect.components])))
  · exact (bEffect.read (n := 64) (r := 14) (by simp)).trans ((abi.1 .r14 (by simp)).trans
      (beforeCall.read (n := 64) (r := 14) (by rw [List.mem_append, mark_components]; simp [loadEffect, Effect.components])))
  · exact (bEffect.read (n := 64) (r := 5) (by simp)).trans ((abi.1 .rbp (by simp)).trans
      (beforeCall.read (n := 64) (r := 5) (by rw [List.mem_append, mark_components]; simp [loadEffect, Effect.components])))
  · exact (bEffect.mxcsr (by simp)).trans (abi.2.2.1.trans
      (beforeCall.mxcsr (by rw [List.mem_append, mark_components]; simp [loadEffect, Effect.components])))
  · exact (bEffect.fcw (by simp)).trans (abi.2.2.2.trans
      (beforeCall.fcw (by rw [List.mem_append, mark_components]; simp [loadEffect, Effect.components])))

end Hkdf.Proofs.NewExpand.Expand.Finalize.InnerPadding
