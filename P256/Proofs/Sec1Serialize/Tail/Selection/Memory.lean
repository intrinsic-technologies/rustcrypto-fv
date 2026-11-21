import P256.Proofs.Sec1Serialize.Tail.Selection.State

set_option autoImplicit false

namespace P256.Proofs.Sec1Serialize.Selection

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame
open Conversion (Stage)

variable [Bindings] {s t u : RamState} {boundary : ReturnBoundary}

omit [Bindings] in
theorem sub_add_index (a : BitVec 64) {offset i : Nat} (hi : i ≤ offset)
    (ho : offset < 2^64) :
    a - BitVec.ofNat 64 offset + BitVec.ofNat 64 i = a - BitVec.ofNat 64 (offset - i) := by
  rw [← BitVec.ofNat_sub_ofNat_of_le offset i (by omega) hi]
  simp only [BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.neg_neg, BitVec.add_assoc]

theorem stack_apart (pre : CalleePre s boundary 0x110d70 72 65 328)
    {a b n m : Nat} (ha : a ≤ 328) (hb : b ≤ 328)
    (hn : n ≤ a + 8) (hm : m ≤ b + 8)
    (hab : b + n ≤ a ∨ a + m ≤ b) :
    RangeApart (stackPtr s - BitVec.ofNat 64 a) n
      (stackPtr s - BitVec.ofNat 64 b) m := by
  have hs := stack_bounds pre.stack
  change 328 ≤ (stackPtr s).toNat ∧ (stackPtr s).toNat + 8 < 2^32 at hs
  have ha' : (stackPtr s - BitVec.ofNat 64 a).toNat =
      (stackPtr s).toNat - a := stack_sub_toNat pre.stack ha
  have hb' : (stackPtr s - BitVec.ofNat 64 b).toNat =
      (stackPtr s).toNat - b := stack_sub_toNat pre.stack hb
  apply RangeApart.of_toNat
  · rw [ha']; omega
  · rw [hb']; omega
  · rw [ha', hb']; omega

theorem byte_store_pre (pre : CalleePre s boundary 0x110d70 72 65 328)
    (stage : Stage s s t boundary) {offset pc len : Nat}
    (ho : offset ≤ 328) (hl : pc + len ≤ 118431)
    (hrip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 pc) :
    StorePre (Extracted.textAddress + BitVec.ofNat 64 pc) len
      (fun _ => stackPtr s - BitVec.ofNat 64 offset) 1 t := by
  refine ⟨hrip, writable_of_grow (stack_sub_writable pre.stack (fun a ha hr => pre.avoids _ (by simp) a ha (.inr hr)) ho (by omega) (by decide)
    (by have := Nat.mod_lt (stackPtr s - BitVec.ofNat 64 offset).toNat (by decide : 0 < 4096); omega))
    stage.allocated, ?_⟩
  intro i hi j hj he
  apply pre.avoids (Stack.region s 328) (by simp) _
    (stack_contains pre ho (by omega) ⟨i, hi, rfl⟩) (.inl ?_)
  rw [he]
  simpa only [BitVec.ofNat_add, ← BitVec.add_assoc] using
    inProgram_of_textOffset (pc+j) (by omega)

theorem stage_store (pre : CalleePre s boundary 0x110d70 72 65 328)
    (stage : Stage s s t boundary) {offset : Nat} (ho : offset ≤ 312) (hmin : 48 < offset)
    (step : Machine.step t = some (.next u)) (ready : ReadyToStep u)
    (agree : AgreesExcept [.mem (stackPtr s - BitVec.ofNat 64 offset) 1, .rip] t u)
    (next : InProgram u.RIP) : Stage s s u boundary := by
  have state := stage.toFrameState.after_effect pre (by decide) ready agree
    (by
      intro c hc a ha
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · exact ⟨workRegion s 328, by simp, work_contains pre (by omega) (by omega) ha⟩
      · exact ha.elim)
    (by simp)
  obtain ⟨fuel, hfuel⟩ := stage.execution
  exact ⟨state, fuel + 1, hfuel.trans (Advances.of_step step
    (.inl (boundary_ne_program pre.outerBoundary next)))⟩

omit [Bindings] in
theorem bytes_of_hasBytes {offset : Nat} {bytes : ByteArray}
    (h : (bufferRegion s offset).HasBytes t.external bytes) :
    Bytes t.external (stackPtr s - BitVec.ofNat 64 offset) 65 (fun i => bytes[i]!) := by
  have hsize : bytes.size = 65 := h.1
  intro i hi
  have hb := h.2 ⟨i, by omega⟩
  simpa only [bufferRegion, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, getElem!_pos bytes i (by omega)] using hb

omit [Bindings] in
theorem hasBytes_of_bytes {offset : Nat} {bytes : ByteArray} (hsize : bytes.size = 65)
    (h : Bytes t.external (stackPtr s - BitVec.ofNat 64 offset) 65 (fun i => bytes[i]!)) :
    (bufferRegion s offset).HasBytes t.external bytes := by
  refine ⟨hsize, ?_⟩
  intro i
  simpa only [bufferRegion, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, getElem!_pos bytes i.val i.isLt] using
    h i.val (by omega)

omit [Bindings] in
theorem byte_of_read {address : BitVec 64} {byte : UInt8}
    (hm : (t.external[address]?).isSome)
    (hr : (Operand.mem address : Operand 8).read t = byte.toBitVec) :
    t.external[address]? = some byte := by
  obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp hm
  have hread : (Operand.mem address : Operand 8).read t = v.toBitVec := by
    have hb : Bytes t.external address 1 (fun _ => v) := by
      intro i hi
      have : i = 0 := by omega
      simpa [this] using hv
    change memLoad t.external address 8 = v.toBitVec
    simpa only [BitVec.reduceOfNat, BitVec.add_zero] using hb.loadByte 0 (by decide)
  have he := hread.symm.trans hr
  exact hv.trans (congrArg some (UInt8.eq_of_toBitVec_eq he))

end P256.Proofs.Sec1Serialize.Selection
