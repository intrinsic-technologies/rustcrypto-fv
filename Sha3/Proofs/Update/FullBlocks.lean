import Sha3.Proofs.Update.FullBlocks.Compose
import Sha3.Proofs.Update.FullBlocks.Loop
import Sha3.Proofs.Update.PermutationCall

namespace Sha3.Proofs.Update.FullBlocks

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program
open Keccak Permutation

theorem slot_of_stateWrites [Bindings] {v : Variant} {initial s t : RamState}
    {bytes : ByteArray} {state : Incremental.State} {components : List Component}
    (hc : CallContext v initial bytes state) (ha : AgreesExcept components s t)
    (hw : StateWrites initial components) :
    (Operand.mem (frameBase initial) : Operand 64).read t =
      (Operand.mem (frameBase initial) : Operand 64).read s := by
  apply memLoad_congr
  intro j hj
  apply congrArg (fun x : Option UInt8 ↦ x.getD 0)
  apply ha.memory
  intro c hcm hcover
  obtain ⟨k, hk, he⟩ := hw c hcm _ hcover
  apply hc.stateStack k hk (272 + j) (by omega)
  rw [BitVec.ofNat_add, ← BitVec.add_assoc]
  change initial.regValue .rsi + BitVec.ofNat 64 k =
    (Update.stackBase initial + 272) + BitVec.ofNat 64 j
  rw [stackBase_add_272]
  exact he.symm

theorem loop_step [Bindings] {boundary : ReturnBoundary} {v : Variant}
    {initial origin s : RamState} {bytes : ByteArray} {state : Incremental.State}
    {offset count index : Nat} (hc : CallContext v initial bytes state)
    (hb : ¬ InProgram boundary.rip) (hspan : offset + count * v.rate ≤ bytes.size)
    (hindex : index < count) (h : LoopInvariant initial origin bytes v offset count index s) :
    ∃ t, Advances boundary (2 * v.lanes + 3 + 6340 + 2) s t ∧
      LoopInvariant initial origin bytes v offset count (index + 1) t := by
  have hsize : offset + index * v.rate + v.rate ≤ bytes.size := by
    have hm := Nat.mul_le_mul_right v.rate hindex
    rw [Nat.succ_mul] at hm
    omega
  have hip : s.RIP = start v := by simpa only [loopPC, ite_eq_left hindex] using h.rip
  obtain ⟨before, hbody, ib, ipb, countb, inputb, argb, fb, lanesb, cursorb⟩ :=
    body_to_call hc h.machine hb hip h.pointer h.input hsize
  obtain ⟨returned, hp, iperm, ripperm, savedp, lanesp, cursorp, slotp⟩ :=
    Update.permutation_advance hc ib boundary hb (callPC v) (callDisplacement v)
      ipb argb (by rw [← (call_encoding v).1]; exact call_image v)
      (call_encoding v).2 (callReturn_inProgram v)
  have countp : (Operand.reg 5 : Operand 64).read returned =
      .ofNat 64 (v.rate * (count - (index + 1))) := by
    have hs : (Operand.reg 5 : Operand 64).read returned =
        (Operand.reg 5 : Operand 64).read before := savedp .rbp (by simp)
    rw [hs, countb, h.counter, count_sub_rate _ _ _ hindex]
  have inputp : (Operand.reg 14 : Operand 64).read returned =
      initial.regValue .rdx + .ofNat 64 (offset + (index + 1) * v.rate) := by
    have hs : (Operand.reg 14 : Operand 64).read returned =
        (Operand.reg 14 : Operand 64).read before := savedp .r14 (by simp)
    rw [hs, inputb, Nat.add_mul, Nat.one_mul, Nat.add_assoc]
  have keptp : ∀ r ∈ keptRegisters, (Operand.reg r : Operand 64).read returned =
      (Operand.reg r : Operand 64).read origin := by
    intro r hr
    rw [saved_kept savedp hr, fb.read, h.kept r hr]
    simp only [keptRegisters, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp [clobbers, setupClobbers]
  have lanesfinal : memoryLanes (initial.regValue .rsi) returned =
      absorbedPrefix (memoryLanes (initial.regValue .rsi) origin) v.rate bytes offset
        (index + 1) := by
    rw [lanesb, h.lanes] at lanesp
    exact lanesp.trans (absorbedPrefix_succ _ _ _ _ _).symm
  obtain ⟨t, ht, rt, _, ipt, ft⟩ := backedge_advance (v := v) iperm.ready iperm.loaded hb ripperm
  have hnomem : ∀ c : Component, c ∈ [.flags, .rip] → ∀ x, ¬ c.Covers x := by
    simp [Component.Covers]
  have it := BodyInvariant.of_stateWrites hc iperm rt ft
    (fun c hc x hx ↦ (hnomem c hc x hx).elim) (by simp)
  have hsize64 : v.rate * count < 2^64 := by
    have := hc.inputRead.low
    rw [Nat.mul_comm] at hspan
    omega
  have test := count_test v count (index + 1) (by omega) hsize64
  have he := ft.external hnomem
  refine ⟨t, (hbody.trans hp).trans ht, it, ?_, ?_, (ft.read (by simp)).trans inputp,
    (ft.read (by simp)).trans countp,
    fun r hr ↦ (ft.read (by simp)).trans (keptp r hr), ?_, ?_, ?_⟩
  · have slotb := slot_of_stateWrites hc fb (by
      intro c hc x hx
      simp only [List.mem_append] at hc
      rcases hc with hc | hc
      · exact block_stateWrites initial c hc x hx
      · exact (setup_nomem c hc x hx).elim)
    simpa only [Operand.read, he] using slotp.trans (slotb.trans h.slot)
  · exact (ft.read (n := 64) (r := 15) (by simp)).trans ((savedp .r15 (by simp)).trans
      ((fb.read (n := 64) (r := 15) (by simp [clobbers, setupClobbers])).trans h.pointer))
  · have hl : memoryLanes (initial.regValue .rsi) t =
        memoryLanes (initial.regValue .rsi) returned := by
      unfold memoryLanes
      simp only [Operand.read, he]
    exact hl.trans lanesfinal
  · simpa only [cursor, Operand.read, he] using cursorp.trans (cursorb.trans h.cursor)
  · change t.RIP = (if ((Operand.reg 5 : Operand 64).read returned).toNat < v.rate
      then tailAddress v else start v) at ipt
    simpa only [countp, test, loopPC, ite_not] using ipt

theorem full_blocks_advance [Bindings] {boundary : ReturnBoundary} {v : Variant}
    {initial origin s : RamState} {bytes : ByteArray} {state : Incremental.State}
    {offset count : Nat} (hc : CallContext v initial bytes state)
    (hb : ¬ InProgram boundary.rip) (hspan : offset + count * v.rate ≤ bytes.size)
    (h : LoopInvariant initial origin bytes v offset count 0 s) :
    ∃ t, Advances boundary (count * (2 * v.lanes + 3 + 6340 + 2)) s t ∧
      LoopInvariant initial origin bytes v offset count count t := by
  have run := AdvanceTriple.iterate (boundary := boundary) (code := Extracted.programImage)
    (invariant := fun index s ↦ LoopInvariant initial origin bytes v offset count index s)
    count (2 * v.lanes + 3 + 6340 + 2)
    (fun index hindex s _ _ h ↦ by
      obtain ⟨t, ht, hi⟩ := loop_step hc hb hspan hindex h
      exact ⟨t, ht, hi.machine.ready,
        CodeIn.of_loaded hi.machine.loaded (SectionsLow.codeLow programSections_low), hi⟩)
  obtain ⟨t, ht, _, _, hi⟩ := run s h.machine.ready
    (CodeIn.of_loaded h.machine.loaded (SectionsLow.codeLow programSections_low)) h
  exact ⟨t, ht, hi⟩

theorem full_blocks_from_start [Bindings] {boundary : ReturnBoundary} {v : Variant}
    {initial s : RamState} {bytes : ByteArray} {state : Incremental.State}
    {offset count : Nat} (hc : CallContext v initial bytes state)
    (hb : ¬ InProgram boundary.rip) (hspan : offset + count * v.rate ≤ bytes.size)
    (hcount : 0 < count) (hInv : BodyInvariant initial s) (hip : s.RIP = fullBlockAddress v)
    (hpointer : s.regValue .r15 = initial.regValue .rsi)
    (hinput : (Operand.reg 14 : Operand 64).read s = initial.regValue .rdx + .ofNat 64 offset)
    (hcounter : (Operand.reg 5 : Operand 64).read s = .ofNat 64 (v.rate * count)) :
    ∃ t, Advances boundary (count * (2 * v.lanes + 3 + 6340 + 2)) s t ∧
      BodyInvariant initial t ∧ t.RIP = tailAddress v ∧
      (Operand.reg 5 : Operand 64).read t = 0 ∧
      (Operand.reg 14 : Operand 64).read t =
        initial.regValue .rdx + .ofNat 64 (offset + count * v.rate) ∧
      (∀ r ∈ keptRegisters, (Operand.reg r : Operand 64).read t =
        (Operand.reg r : Operand 64).read s) ∧
      memoryLanes (initial.regValue .rsi) t =
        absorbedPrefix (memoryLanes (initial.regValue .rsi) s) v.rate bytes offset count ∧
      cursor (initial.regValue .rsi) t = cursor (initial.regValue .rsi) s ∧
      (Operand.mem (frameBase initial) : Operand 64).read t =
        (Operand.mem (frameBase initial) : Operand 64).read s ∧
      t.regValue .r15 = initial.regValue .rsi := by
  have hip' : s.RIP = loopPC v count 0 := by
    simpa only [loopPC, ite_eq_left hcount, show start v = fullBlockAddress v by cases v <;> rfl]
      using hip
  obtain ⟨t, ht, hi⟩ := full_blocks_advance hc hb hspan
    (LoopInvariant.initial (bytes := bytes) hInv hpointer hinput hcounter hip')
  obtain ⟨ipt, countert, lanest⟩ := hi.complete
  exact ⟨t, ht, hi.machine, ipt, countert, hi.input, hi.kept, lanest, hi.cursor, hi.slot, hi.pointer⟩

end Sha3.Proofs.Update.FullBlocks
