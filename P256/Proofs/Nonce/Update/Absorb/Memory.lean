import P256.Proofs.Nonce.Update.Absorb.State
import P256.Proofs.HMAC.State
import P256.Proofs.Nonce.Update.Prepare.Memory

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Absorb

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

theorem hasBytes_append {memory : Ram} {address : BitVec 64} {first second : ByteArray}
    (left : (MemoryRegion.mk address.toNat first.size).HasBytes memory first)
    (right : (MemoryRegion.mk (address + BitVec.ofNat 64 first.size).toNat second.size).HasBytes
      memory second) :
    (MemoryRegion.mk address.toNat (first ++ second).size).HasBytes memory (first ++ second) := by
  refine ⟨rfl, fun i => ?_⟩
  by_cases before : i.val < first.size
  · have h := left.2 ⟨i.val, before⟩
    simpa only [ByteArray.getElem_append_left before] using h
  · have after : i.val - first.size < second.size := by
      have bound : i.val < first.size + second.size := by
        simpa only [ByteArray.size_append] using i.isLt
      omega
    have h := right.2 ⟨i.val - first.size, after⟩
    change memory[BitVec.ofNat 64 ((address + BitVec.ofNat 64 first.size).toNat +
      (i.val - first.size))]? = some second[i.val - first.size] at h
    simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at h
    rw [BitVec.add_assoc, ← BitVec.ofNat_add,
      Nat.add_sub_of_le (by omega : first.size ≤ i.val)] at h
    simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      ByteArray.getElem_append_right (by omega : first.size ≤ i.val)] using h

theorem hasBytes_extract {memory : Ram} {address : BitVec 64} {input : ByteArray}
    (bytes : (MemoryRegion.mk address.toNat input.size).HasBytes memory input)
    (start stop : Nat) :
    (MemoryRegion.mk (address + BitVec.ofNat 64 start).toNat (input.extract start stop).size).HasBytes
      memory (input.extract start stop) := by
  refine ⟨rfl, fun i => ?_⟩
  have h := bytes.2 ⟨start + i.val, ByteArray.getElem_extract_aux i.isLt⟩
  simpa only [ByteArray.getElem_extract, BitVec.ofNat_add, BitVec.ofNat_toNat,
    BitVec.setWidth_eq, BitVec.add_assoc] using h

theorem hasBytes_singleton {memory : Ram} {address : BitVec 64} {byte : UInt8}
    (present : memory[address]? = some byte) :
    (MemoryRegion.mk address.toNat 1).HasBytes memory ⟨#[byte]⟩ := by
  refine ⟨rfl, fun i => ?_⟩
  have eq : i.val = 0 := by have bound : i.val < 1 := i.isLt; omega
  simpa [eq, ByteArray.getElem_eq_getElem_data] using present

theorem frame_after [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
    {state : State} {components : List Component}
    (pre : DrbgCalleePre initial boundary 0x109f30 1856 state)
    (input : FrameState initial s) (ready : ReadyToStep t)
    (agrees : AgreesExcept components s t) (rsp : .reg 4 ∉ components)
    (writes : ∀ c ∈ components, ∀ a, c.Covers a →
      (ScalarFrame.workRegion initial 1856).Contains a.toNat)
    (hdf : Component.df ∉ components := by component_not_mem)
    (hmxcsr : Component.mxcsr ∉ components := by component_not_mem)
    (hfcw : Component.fcw ∉ components := by component_not_mem) : FrameState initial t := by
  exact input.after_effect pre.callee (by decide) ready agrees
    (fun c hc a ha => ⟨ScalarFrame.workRegion initial 1856, by simp, writes c hc a ha⟩)
    rsp hdf hmxcsr hfcw

theorem drbg_after [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
    {original state : State} {components : List Component}
    (pre : DrbgCalleePre initial boundary 0x109f30 1856 original)
    (input : DrbgAt s (initial.regValue .rdi) state)
    (agrees : AgreesExcept components s t)
    (writes : ∀ c ∈ components, ∀ a, c.Covers a →
      (ScalarFrame.workRegion initial 1856).Contains a.toNat) :
    DrbgAt t (initial.regValue .rdi) state := by
  apply input.copy
  intro i hi
  apply agrees.byte
  intro c hc covered
  exact pre.separation _
    (memoryRegion_contains_add pre.stateBounded (Nat.le_refl _) (Nat.le_refl _) hi)
    (Prepare.work_substack pre (writes c hc _ covered))

theorem stack_writable1 [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {state : State} (pre : DrbgCalleePre initial boundary 0x109f30 1856 state)
    (frame : FrameState initial s) {offset : Nat} (bound : offset ≤ 680) :
    MemWritable s (stackPtr s + BitVec.ofNat 64 offset) 1 := by
  rw [ScalarFrame.scalar_stack_address (frameOffset := 680) frame.rsp (by decide) bound]
  apply writable_of_grow _ frame.allocated
  exact stack_sub_writable (offset := 680 - offset) pre.stack
    (fun a ha ht => pre.avoids _ (by simp) a ha (.inr ht))
    (by omega) (by omega) (by decide) (by omega)

theorem stack_writable8 [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {state : State} (pre : DrbgCalleePre initial boundary 0x109f30 1856 state)
    (frame : FrameState initial s) {offset : Nat} (bound : offset ≤ 680)
    (aligned : offset % 8 = 0) :
    MemWritable s (stackPtr s + BitVec.ofNat 64 offset) 8 := by
  rw [ScalarFrame.scalar_stack_address (frameOffset := 680) frame.rsp (by decide) bound]
  apply writable_of_grow _ frame.allocated
  exact stack_sub_writable8 (offset := 680 - offset) pre.stack
    (fun a ha ht => pre.avoids _ (by simp) a ha (.inr ht)) (by omega) (by omega)

end P256.Proofs.Nonce.Update.Absorb
