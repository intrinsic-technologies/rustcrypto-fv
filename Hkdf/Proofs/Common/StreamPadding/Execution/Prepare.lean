import Hkdf.Proofs.Common.StreamPadding.Execution.Control
import Hkdf.Proofs.Common.StreamPadding.Execution.Calls
import Hkdf.Proofs.Common.StreamPadding.Execution.Semantics

set_option autoImplicit false

namespace Hkdf.Proofs.Common.StreamPadding.Execution

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Spec.Program Hkdf.Proofs.Common.Machine Hkdf.Proofs.Common.CallFrame
open Hkdf.Proofs.Common.SHA256

attribute [local simp] Variant.lengthReg Variant.lengthIndex Variant.blocksReg
  Variant.blocksIndex Variant.hashReg Variant.hashIndex Variant.remainingReg
  Variant.remainingIndex Variant.stableReg Variant.stableIndex regIndex X86.Syntax.Reg.fin


private theorem fill_agrees {s t : RamState} (v : Variant) (p : BitVec 64)
    (position offset len : Nat) (positionBound : position ≤ 64)
    (low : 8 ≤ p.toNat) (high : p.toNat+v.frame+8 < 2^32)
    (within : offset+len ≤ v.frame+8)
    (apart : offset+len ≤ v.tail+position ∨ v.tail+64 ≤ offset)
    (frame : MemoryWriteFrame s t #v[
      ⟨(p+BitVec.ofNat 64 (v.tail+position)).toNat,64-position⟩,
      ⟨(p-8).toNat,8⟩]) :
    (Component.mem (p+BitVec.ofNat 64 offset) len).Agrees s t := by
  have toNat (i : Nat) (hi : i≤v.frame+8) :
      (p+BitVec.ofNat 64 i).toNat = p.toNat+i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : i<2^64), Nat.mod_eq_of_lt (by omega)]
  have tailBound : v.tail+position≤v.frame+8 := by
    cases v <;> simp only [Variant.tail, Variant.frame] <;> omega
  have minus : (p-8).toNat = p.toNat-8 := by
    rw [BitVec.toNat_sub_of_le (by simpa only [BitVec.le_def, BitVec.reduceToNat] using low)]
    rfl
  apply frame_agrees_of_disjoint frame
  · rw [toNat offset (by omega)]
    omega
  · intro region member a ha hb
    have cases : region = (⟨(p+BitVec.ofNat 64 (v.tail+position)).toNat,64-position⟩ : MemoryRegion) ∨
        region = (⟨(p-8).toNat,8⟩ : MemoryRegion) := by simpa using member
    change (p+BitVec.ofNat 64 offset).toNat ≤ a ∧ a < (p+BitVec.ofNat 64 offset).toNat+len at ha
    rw [toNat offset (by omega)] at ha
    rcases cases with rfl | rfl
    · change (p+BitVec.ofNat 64 (v.tail+position)).toNat ≤ a ∧
        a < (p+BitVec.ofNat 64 (v.tail+position)).toNat+(64-position) at hb
      rw [toNat (v.tail+position) tailBound] at hb
      rcases apart with apart | apart <;> omega
    · change (p-8).toNat ≤ a ∧ a < (p-8).toNat+8 at hb
      rw [minus] at hb
      omega

private theorem mark_hash_agrees {s t : RamState} (v : Variant) (remaining : Nat)
    (effect : (Stages.markEffect v s).Holds s t)
    (remainder : s.regValue v.lengthReg = BitVec.ofNat 64 remaining) (small : remaining<64) :
    (Component.mem (stackPtr s+BitVec.ofNat 64 v.hash) 32).Agrees s t := by
  intro i hi
  apply effect.agrees.byte
  intro c hc covered
  simp only [Stages.markEffect, Effect.components, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, Write.component, Operand.component, Nat.reduceDiv,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact covered.elim
  obtain ⟨j,hj,he⟩ := covered
  have apart := RangeApart.offsets (stackPtr s)
    (a := v.tail+remaining) (len := 1) (b := v.hash) (count := 32)
    (by cases v <;> simp only [Variant.tail] <;> omega) (by cases v <;> decide)
    (.inl (by simp only [Variant.hash]; omega))
  have address : rspOf s+(.reg v.lengthIndex : Operand 64).read s+BitVec.ofNat 64 v.tail =
      stackPtr s+BitVec.ofNat 64 (v.tail+remaining) := by
    simp only [Variant.lengthIndex, read_regIndex, BitVec.setWidth_eq]
    change stackPtr s+s.regValue v.lengthReg+_=_
    rw [remainder,BitVec.ofNat_add]
    bv_omega
  rw [address] at he
  exact apart j hj i hi he.symm

theorem prepare [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {inputBytes : Nat} {message : ByteArray} (v : Variant)
    (pre : CalleePre initial boundary v.helperEntry inputBytes v.outputBytes v.reserve)
    (running : Running initial boundary (regions v initial) s)
    (rsp : stackPtr s = base v initial) (rip : s.RIP = v.pc .entry)
    (stream : StreamAt s (stackPtr s + BitVec.ofNat 64 v.tail) message) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      Running initial boundary (regions v initial) t ∧
      stackPtr t = stackPtr s ∧ t.regValue .rbx = s.regValue .rbx ∧
      t.regValue v.stableReg = s.regValue v.stableReg ∧ t.MXCSR = s.MXCSR ∧
      t.FP87_Control = s.FP87_Control ∧ MemoryWriteFrame s t (writes v (stackPtr s)) ∧
      t.RIP = (if message.size % 64 < 56 then v.pc .length else v.pc .firstHead) ∧
      t.regValue v.lengthReg = BitVec.ofNat 64 (message.size%64) ∧
      t.regValue v.blocksReg = BitVec.ofNat 64 (message.size/64) ∧
      t.regValue v.hashReg = stackPtr t + BitVec.ofNat 64 v.hash ∧
      HashStateAt t (stackPtr t + BitVec.ofNat 64 v.hash)
        (compressBlocks Hkdf.Proofs.NIST.SHA256.initialHash message) ∧
      (⟨(stackPtr t + BitVec.ofNat 64 v.tail).toNat,64⟩ : MemoryRegion).HasBytes
        t.external (paddedBuffer message) := by
  have small := Nat.mod_lt message.size (by decide : 0<64)
  obtain ⟨n,l,runL,readyL,runningL,effectL⟩ := Execution.load v pre running rsp rip
  obtain ⟨rspL,rbxL,stableL,mxcsrL,fcwL⟩ := stable_of_agrees_selected v effectL.agrees
    (by cases v <;> simp [Stages.loadEffect, Effect.components, Write.component, Operand.component] <;> decide)
  have stackL : rspOf l = stackPtr s := rspL
  obtain ⟨hashPointerL,remainderL,blocksL,remainingL,memoryL⟩ := load_observations v effectL stream
  have tailL : (⟨(stackPtr l + BitVec.ofNat 64 v.tail).toNat,message.size%64⟩ : MemoryRegion).HasBytes
      l.external (remainderBytes message) := by
    simpa only [rspL, memoryL, remainderBytes] using stream.tail
  have hashL : HashStateAt l (stackPtr s+BitVec.ofNat 64 v.hash)
      (compressBlocks Hkdf.Proofs.NIST.SHA256.initialHash message) := by
    simpa only [HashStateAt, memoryL, Variant.hash, BitVec.ofNat_add, BitVec.add_assoc,
      BitVec.ofNat_eq_ofNat] using stream.hashWords
  obtain ⟨m,a,runA,readyA,runningA,effectA⟩ := Execution.mark v pre runningL (rspL.trans rsp)
    effectL.rip (message.size%64) remainderL small
  obtain ⟨rspA,rbxA,stableA,mxcsrA,fcwA⟩ := stable_of_agrees_selected v effectA.agrees
    (by cases v <;> simp [Stages.markEffect, Effect.components, Write.component, Operand.component] <;> decide)
  obtain ⟨markerA,tailA⟩ := mark_bytes v effectA remainderL tailL
  have regsA (r : X86.Syntax.Reg) (member : r ∈ ([v.lengthReg,v.blocksReg,v.hashReg,v.remainingReg] : List X86.Syntax.Reg)) :
      a.regValue r = l.regValue r := by
    apply reg_agrees effectA.agrees
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl
    all_goals cases v <;> simp [Stages.markEffect, Effect.components, Write.component, Operand.component] <;> decide
  have args := effectA.writes
  change memLoad a.external
      (rspOf l+(.reg v.lengthIndex : Operand 64).read l+BitVec.ofNat 64 v.tail) 8 = 128 ∧
    a.regValue .rdi =
      rspOf l+(.reg v.lengthIndex : Operand 64).read l+BitVec.ofNat 64 (v.tail+1) ∧
    a.regValue .rsi = 0 ∧ a.regValue .rdx = (.reg v.remainingIndex : Operand 64).read l at args
  simp only [Variant.lengthIndex, Variant.remainingIndex, read_regIndex,
    BitVec.setWidth_eq] at args
  have destination : a.regValue .rdi = stackPtr a+BitVec.ofNat 64 (v.tail+(message.size%64+1)) := by
    rw [args.2.1]
    change stackPtr l+l.regValue v.lengthReg+_ = _
    rw [remainderL, rspA]
    simp only [BitVec.ofNat_add]
    bv_omega
  have count : a.regValue .rdx = BitVec.ofNat 64 (64-(message.size%64+1)) := by
    exact (args.2.2.2.trans remainingL).trans (congrArg (BitVec.ofNat 64) (by omega))
  obtain ⟨k,t,runT,readyT,runningT,ripT,rspT,abiT,frameT,narrow,zeros⟩ :=
    Execution.fill v pre runningA ((rspA.trans rspL).trans rsp) (by omega)
      effectA.rip destination args.2.2.1 count
  have pointerA : stackPtr a = stackPtr s := rspA.trans rspL
  have baseA : stackPtr a = base v initial := pointerA.trans rsp
  have boundsA := local_bounds v pre baseA
  have low : 8≤(stackPtr a).toNat := by have := boundsA.1; omega
  have high : (stackPtr a).toNat+v.frame+8<2^32 := boundsA.2
  have keptTail : (Component.mem (stackPtr s+BitVec.ofNat 64 v.tail) (message.size%64+1)).Agrees a t := by
    simpa only [pointerA] using fill_agrees v (stackPtr a) (message.size%64+1)
      v.tail (message.size%64+1) (by omega) low high
      (by cases v <;> simp only [Variant.tail, Variant.frame] <;> omega) (.inl (by omega)) narrow
  have keptHash : (Component.mem (stackPtr s+BitVec.ofNat 64 v.hash) 32).Agrees a t := by
    simpa only [pointerA] using fill_agrees v (stackPtr a) (message.size%64+1)
      v.hash 32 (by omega) low high (by cases v <;> decide) (.inr (by simp only [Variant.hash]; omega)) narrow
  have hashA : HashStateAt a (stackPtr s+BitVec.ofNat 64 v.hash)
      (compressBlocks Hkdf.Proofs.NIST.SHA256.initialHash message) := by
    apply Hkdf.Proofs.Common.hashState_of_bytes hashL
    have same := mark_hash_agrees v (message.size%64) effectA remainderL small
    intro i hi
    simpa only [rspL] using same i hi
  have padded : (⟨(stackPtr s+BitVec.ofNat 64 v.tail).toNat,64⟩ : MemoryRegion).HasBytes
      t.external (paddedBuffer message) := by
    apply padded_bytes
    · refine ⟨tailA.1, fun i => ?_⟩
      have hi : i.val < message.size%64 := by simpa only [remainderBytes_size] using i.isLt
      have same := keptTail i.val (by omega)
      have old := tailA.2 i
      simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, rspL] using same.trans (by
        simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, stackL] using old)
    · exact (keptTail (message.size%64) (by omega)).trans (by simpa only [stackL] using markerA)
    · intro i hi
      have zero := zeros i (by omega)
      simpa only [pointerA, BitVec.ofNat_add, BitVec.add_assoc] using zero
  have frameL : MemoryWriteFrame s l (writes v (stackPtr s)) :=
    effectL.agrees.memoryWriteFrame (fun c hc address covered => (load_noMem v s c hc address covered).elim)
  have frameA : MemoryWriteFrame l a (writes v (stackPtr s)) := by
    have bound : (stackPtr l).toNat+v.frame+8<2^32 := by simpa only [rspA] using high
    have frame := effectA.agrees.memoryWriteFrame (mark_writes v l (message.size%64) bound remainderL small)
    simpa only [rspL] using frame
  have frameT' : MemoryWriteFrame a t (writes v (stackPtr s)) := by simpa only [pointerA] using frameT
  have remainderT : t.regValue v.lengthReg = BitVec.ofNat 64 (message.size%64) :=
    (abiT.1 v.lengthReg (by cases v <;> simp <;> decide)).trans ((regsA v.lengthReg (by simp)).trans remainderL)
  have blocksT : t.regValue v.blocksReg = BitVec.ofNat 64 (message.size/64) :=
    (abiT.1 v.blocksReg (by cases v <;> simp <;> decide)).trans ((regsA v.blocksReg (by simp)).trans blocksL)
  have hashPointerT : t.regValue v.hashReg = stackPtr s+BitVec.ofNat 64 v.hash :=
    (abiT.1 v.hashReg (by cases v <;> simp <;> decide)).trans ((regsA v.hashReg (by simp)).trans hashPointerL)
  have remainingT : t.regValue v.remainingReg = BitVec.ofNat 64 (63-message.size%64) :=
    (abiT.1 v.remainingReg (by cases v <;> simp <;> decide)).trans ((regsA v.remainingReg (by simp)).trans remainingL)
  obtain ⟨q,runQ,readyQ,runningQ,ripQ,agreesQ⟩ := Execution.branch v pre runningT ripT
  obtain ⟨rspQ,rbxQ,stableQ,mxcsrQ,fcwQ⟩ := stable_of_agrees_selected v agreesQ (by simp)
  have pointerQ : stackPtr q = stackPtr s := rspQ.trans (rspT.trans pointerA)
  have memoryQ : q.external = t.external := agreesQ.external (by simp [Component.Covers])
  have frameQ : MemoryWriteFrame t q (writes v (stackPtr s)) :=
    agreesQ.memoryWriteFrame (by simp [WritesWithin, Component.Covers])
  have branchQ : q.RIP =
      (if message.size%64<56 then v.pc .length else v.pc .firstHead) := by
    rw [ripQ, remainingT, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
    split <;> split <;> first | rfl | omega
  refine ⟨n+m+k+2,q,((runL.trans runA).trans runT).trans runQ,readyQ,runningQ,
    pointerQ,
    rbxQ.trans ((abiT.1 .rbx (by simp)).trans (rbxA.trans rbxL)),
    stableQ.trans ((abiT.1 v.stableReg (by cases v <;> simp <;> decide)).trans (stableA.trans stableL)),
    mxcsrQ.trans (abiT.2.2.1.trans (mxcsrA.trans mxcsrL)),
    fcwQ.trans (abiT.2.2.2.trans (fcwA.trans fcwL)),
    memoryWriteFrame_trans frameL
      (memoryWriteFrame_trans frameA (memoryWriteFrame_trans frameT' frameQ)),
    branchQ,
    (reg_agrees agreesQ v.lengthReg (by simp)).trans remainderT,
    (reg_agrees agreesQ v.blocksReg (by simp)).trans blocksT,?_,?_,?_⟩
  · rw [pointerQ]
    exact (reg_agrees agreesQ v.hashReg (by simp)).trans hashPointerT
  · have hashT := Hkdf.Proofs.Common.hashState_of_bytes hashA keptHash
    simpa only [HashStateAt, memoryQ, pointerQ] using hashT
  · simpa only [memoryQ, pointerQ] using padded

end Hkdf.Proofs.Common.StreamPadding.Execution
