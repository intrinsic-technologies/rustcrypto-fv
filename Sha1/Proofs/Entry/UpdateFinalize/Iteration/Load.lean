import Sha1.Proofs.Entry.UpdateFinalize.Iteration.Load.Machine
import Sha1.Proofs.Streaming.UpdateFinalize.Geometry
import Sha1.Proofs.Entry.UpdateFinalize.Iteration.Transport

namespace Sha1.Proofs.Entry.UpdateFinalize

open Sha1.Spec Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha1.Proofs.Buffered Sha1.Proofs.Streaming.UpdateFinalize
open Sha1.Proofs.Streaming

section

variable [bindings : Bindings] {initial s : RamState} {inputs : Array Slices.Input}

private theorem read_region_byte (hf : Frame initial s)
    (hc : SliceHash.ValidCall SliceHash.updateFinalize bindings initial inputs)
    {r : MemoryRegion} (hr : r ∈ Slices.readRegions initial inputs)
    {a : BitVec 64} (ha : r.Contains a.toNat) :
    s.external[a]? = initial.external[a]? := by
  apply hf.memory
  intro q hq
  simp only [Vector.mem_mk, Array.mem_singleton] at hq
  subst q
  exact (hc.separation.2 _ (Vector.getElem_mem (i := 1) (by decide))).1 r hr _ ha

private theorem table_entry_read (hf : Frame initial s)
    (hc : SliceHash.ValidCall SliceHash.updateFinalize bindings initial inputs)
    {base : BitVec 64} (ht : (⟨base.toNat, 8 * inputs.size⟩ : MemoryRegion) ∈
      Slices.readRegions initial inputs)
    (hb : base.toNat + 8 * inputs.size < 2^32) {i : Nat} (hi : i < inputs.size) :
    (Operand.mem (base + BitVec.ofNat 64 (8 * i)) : Operand 64).read s =
    (Operand.mem (base + BitVec.ofNat 64 (8 * i)) : Operand 64).read initial := by
  apply memLoad_congr
  intro j hj
  change j < 8 at hj
  apply congrArg (fun x : Option UInt8 ↦ x.getD 0)
  apply read_region_byte hf hc ht
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, toNat_add_ofNat _ _ (by omega)]
  exact ⟨by dsimp; omega, by dsimp; omega⟩

private theorem slice_update_pre
    (hf : Frame initial s)
    (hc : SliceHash.ValidCall SliceHash.updateFinalize bindings initial inputs)
    (hStride : UnitStringStride bindings) (hOutside : ¬ InProgram (returnBoundary initial).rip)
    {i : Nat} (hi : i < inputs.size) (hrip : s.RIP = 0x101cf5)
    (hAbs : Absorbed (stackPtr s + 0xd8) (Slices.message (inputs.extract 0 i)) s)
    (hInput : (Operand.reg 14 : Operand 64).read s = inputs[i].address)
    (hSize : (Operand.reg 3 : Operand 64).read s = BitVec.ofNat 64 inputs[i].bytes.size) :
    UpdatePre .updateFinalize (returnBoundary initial)
      (Slices.message (inputs.extract 0 i)) inputs[i].bytes s ∧
      (UpdateKind.inputRegion .updateFinalize s inputs[i].bytes).start ≠ 0 := by
  have hregion : UpdateKind.inputRegion .updateFinalize s inputs[i].bytes = inputs[i].region :=
    congrArg (fun (p : BitVec 64) ↦ (⟨p.toNat, inputs[i].bytes.size⟩ : MemoryRegion)) hInput
  have hin := hc.inputInMemory.inputsInMemory ⟨i, hi⟩
  have hmem : inputs[i].region ∈ Slices.readRegions initial inputs := by
    simp only [Slices.readRegions, List.mem_cons, Array.mem_toList_iff, Array.mem_map]
    exact .inr (.inr ⟨inputs[i], Array.getElem_mem hi, rfl⟩)
  have sep := hc.separation.2 _ (Vector.getElem_mem (i := 1) (by decide))
  have hsep := sep.1 _ hmem
  obtain ⟨hl, _, hh, hal⟩ := hf.stack_bounds hc.stackAvailable
  have scratch {a : Nat} (ha : (⟨(stackPtr s).toNat - 344, 344⟩ : MemoryRegion).Contains a) :
      (Stack.region initial SliceHash.updateFinalize.minStackBytes).Contains a := by
    apply (hf.stack_contains hc.stackAvailable).mpr
    change (stackPtr s).toNat - 344 ≤ a ∧ a < (stackPtr s).toNat - 344 + 344 at ha
    omega
  have ctx {a : Nat} (ha : (UpdateKind.contextRegion .updateFinalize s).Contains a) :
      (Stack.region initial SliceHash.updateFinalize.minStackBytes).Contains a := by
    apply (hf.stack_contains hc.stackAvailable).mpr
    have addr := (hf.finalize_storage hc).stackAddress (offset := 0xd8) (by decide)
    change (stackPtr s + BitVec.ofNat 64 0xd8).toNat ≤ a ∧
      a < (stackPtr s + BitVec.ofNat 64 0xd8).toNat + 92 at ha
    rw [addr] at ha
    omega
  have alloc (a : BitVec 64) (ha : (Stack.region initial SliceHash.updateFinalize.minStackBytes).Contains a.toNat) :=
    Option.isSome_iff_exists.mp (hf.grows a (Option.isSome_iff_exists.mpr (hc.stackAvailable.2.1 a ha)))
  refine ⟨⟨hStride, hf.ready, hf.code, hf.df.df, hrip, hOutside, hAbs, ?_, hSize, ?_,
      hregion ▸ hin.2.1, hl, ?_, hal, fun a ha ↦ alloc a (scratch ha), fun a ha ↦ alloc a (ctx ha),
      ?_, ?_, fun a ha ↦ sep.2 a (scratch ha), fun a ha ↦ sep.2 a (ctx ha)⟩, hregion ▸ hin.1⟩
  · rw [hregion]
    refine ⟨hin.2.2.1, fun j ↦ ?_⟩
    rw [read_region_byte hf hc hmem]
    · exact hin.2.2.2 j
    · have hb : inputs[i].region.start + inputs[i].bytes.size < 2^32 := hin.2.1
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      exact ⟨by omega, by change _ < inputs[i].region.start + inputs[i].bytes.size; omega⟩
  · have hp := validInputs_message_extract_size_lt hc.inputInMemory 0 i
    have hb := validInputs_bytes_size_lt hc.inputInMemory ⟨i, hi⟩
    change inputs[i].bytes.size < 2^32 at hb
    omega
  · change (stackPtr s).toNat + 216 + 92 < 2^32
    omega
  · rw [hregion]
    exact fun a ha hs ↦ hsep a ha (scratch hs)
  · rw [hregion]
    exact fun a ha hs ↦ hsep a ha (ctx hs)

end

theorem load_slice [bindings : Bindings] {initial : RamState} {inputs : Array Slices.Input}
    {i : Nat} {s : RamState} (hCall : SliceHash.ValidCall SliceHash.updateFinalize bindings initial inputs)
    (hStride : UnitStringStride bindings) (hOutside : ¬ InProgram (returnBoundary initial).rip)
    (hi : i < inputs.size) (h : Header initial inputs i s) :
    ∃ fuel u, Advances (returnBoundary initial) fuel s u ∧ Frame initial u ∧
      UpdatePre .updateFinalize (returnBoundary initial)
        (Slices.message (inputs.extract 0 i)) inputs[i].bytes u ∧
      (UpdateKind.inputRegion .updateFinalize u inputs[i].bytes).start ≠ 0 ∧
      u.regValue .r15 = BitVec.ofNat 64 i ∧ u.regValue .r12 = BitVec.ofNat 64 inputs.size := by
  have hidx : (Operand.reg 15 : Operand 64).read s = BitVec.ofNat 64 i := (h.counters hi).1
  have shift : BitVec.ofNat 64 i <<< 3 = BitVec.ofNat 64 (8 * i) := by
    rw [BitVec.shiftLeft_eq_mul_twoPow]
    change BitVec.ofNat 64 i * BitVec.ofNat 64 8 = BitVec.ofNat 64 (8 * i)
    rw [← BitVec.ofNat_mul, Nat.mul_comm]
  have ptr : tableAddress s 0xc8 = initial.regValue .rdi + BitVec.ofNat 64 (8 * i) := by
    rw [tableAddress, h.pointers, hidx, shift]
  have len : tableAddress s 0xd0 = initial.regValue .rdx + BitVec.ofNat 64 (8 * i) := by
    rw [tableAddress, h.lengths, hidx, shift]
  have storage := h.toFrame.finalize_storage hCall
  have lift {address : BitVec 64} (hm : MemReadable initial address 8) : MemReadable s address 8 :=
    ⟨hm.low, fun j hj ↦ h.grows _ (hm.mem j hj)⟩
  have hPre : SliceLoadPre s := by
    refine ⟨?_, (storage.stackWritable 0xc8 8 (by decide)).readable,
      (storage.stackWritable 0xd0 8 (by decide)).readable, ?_, ?_⟩
    · simpa only [ite_eq_left hi] using h.rip
    · rw [ptr]
      exact lift (validInputs_pointer_readable hCall.inputInMemory ⟨i, hi⟩)
    · rw [len]
      exact lift (validInputs_length_readable hCall.inputInMemory ⟨i, hi⟩)
  obtain ⟨fuel, u, hAdvance, hReady, _, he⟩ := slice_load_block _ hOutside s h.ready
    (Sha1.Proofs.Compress.Machine.program_text_slice h.code 0x1cdd 24 (by decide +kernel)) hPre
  have hag : AgreesExcept [.reg 14, .reg 0, .reg 3, .rip] s u := he.agrees
  have hm := hag.external (by simp [Component.Covers])
  have hs : stackPtr u = stackPtr s := hag.read (n := 64) (r := 4) (by decide)
  have hf := readOnly_frame h.toFrame hReady (CodeIn.of_external_eq hm h.code)
    (hag.directionFlagClear (by decide) h.df) hs hm hag.rest
  have ha := readOnly_absorbed h.absorbed hm
  rw [← hs] at ha
  have hp : (Operand.reg 14 : Operand 64).read u =
      (Operand.mem (tableAddress s 0xc8) : Operand 64).read s := he.writes.1
  have hl : (Operand.reg 3 : Operand 64).read u =
      (Operand.mem (tableAddress s 0xd0) : Operand 64).read s := he.writes.2.2
  rw [ptr, table_entry_read h.toFrame hCall (by simp [Slices.readRegions, Slices.pointerTable,
    registerRegion]) hCall.inputInMemory.pointerTableValid.2 hi] at hp
  rw [len, table_entry_read h.toFrame hCall (by simp [Slices.readRegions, Slices.lengthTable,
    registerRegion]) hCall.inputInMemory.lengthTableValid.2 hi] at hl
  obtain ⟨hupdate, hnonzero⟩ := slice_update_pre hf hCall hStride hOutside hi he.rip ha
    (hp.trans (validInputs_pointer_read hCall.inputInMemory ⟨i, hi⟩))
    (hl.trans (validInputs_length_read hCall.inputInMemory ⟨i, hi⟩))
  exact ⟨fuel, u, hAdvance, hf, hupdate, hnonzero,
    (hag.read (n := 64) (r := 15) (by decide)).trans hidx,
    (hag.read (n := 64) (r := 12) (by decide)).trans (h.counters hi).2⟩

end Sha1.Proofs.Entry.UpdateFinalize
