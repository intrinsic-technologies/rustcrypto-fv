import Sha1.Proofs.Buffered.Finalize.Family.Contracts
import Sha1.Proofs.Buffered.Finalize.Family.Prepare.Machine
import Sha1.Proofs.Buffered.Finalize.Digest.Prepare

namespace Sha1.Proofs.Buffered.Finalize.Family

open Sha1.Spec Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Standards.NIST
open Sha1.Proofs.Compress.Machine
open PrepareMachine

private theorem entry_noMem {s : RamState} {x : BitVec 64} {c : Component}
    (hc : c ∈ (entryEffect s).components) : ¬ c.Covers x := by
  simp only [entryEffect, Effect.components, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, Write.component, Operand.component, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl <;> exact id

private theorem copy_mem {s : RamState} {x : BitVec 64} {c : Component}
    (hc : c ∈ [.reg 1, .reg 6, .reg 7, .mem (stackPtr s + 32) 96, .rip])
    (h : c.Covers x) : Component.Covers (.mem (stackPtr s + 32) 96) x := by
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;> first | exact h | exact h.elim

private theorem effectA_mem {s : RamState} {x : BitVec 64} {c : Component}
    (hc : c ∈ (effectA s).components) (h : c.Covers x) :
    Component.Covers (.mem (stackPtr s + 24) 4) x := by
  simp only [effectA, Effect.components, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, Write.component, Operand.component, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl <;> first | exact h | exact h.elim

private theorem effectB_mem {s : RamState} {x : BitVec 64} {c : Component}
    (hc : c ∈ (effectB s).components) (h : c.Covers x) :
    Component.Covers (.mem (stackPtr s + 16) 8) x ∨
      Component.Covers (.mem (stackPtr s + 8) 8) x := by
  simp only [effectB, Effect.components, List.map_cons, List.map_nil, List.cons_append,
    List.nil_append, Write.component, Operand.component, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl <;>
    first | exact .inl h | exact .inr h | exact h.elim

private theorem effectA_untouched {s : RamState} {off len i : Nat} (hi : i < len)
    (bound : off + len ≤ 2^64) (apart : 28 ≤ off ∨ off + len ≤ 24) :
    ∀ c ∈ (effectA s).components,
      ¬ c.Covers (stackPtr s + BitVec.ofNat 64 off + BitVec.ofNat 64 i) :=
  fun c hc h ↦ Digest.covers_apart (a := 24) (len := 4) rfl hi
    (by decide) bound apart (effectA_mem hc h)

private theorem effectB_untouched {s : RamState} {off len i : Nat} (hi : i < len)
    (bound : off + len ≤ 2^64) (apart : 24 ≤ off) :
    ∀ c ∈ (effectB s).components,
      ¬ c.Covers (stackPtr s + BitVec.ofNat 64 off + BitVec.ofNat 64 i) := by
  intro c hc h
  rcases effectB_mem hc h with h | h
  · exact Digest.covers_apart (a := 16) (len := 8) rfl hi
      (by decide) bound (.inl apart) h
  · exact Digest.covers_apart (a := 8) (len := 8) rfl hi
      (by decide) bound (.inl (by omega)) h

private theorem copyPre [Bindings] {b : ReturnBoundary} {m : ByteArray} {s u : RamState}
    (h : Pre .updateFinalizeCopy b m s) (hr : ReadyToStep u)
    (hc : CodeIn Extracted.programImage u) (he : (entryEffect s).Holds s u)
    (hsp : stackPtr u = stackPtr s) : Streams.CopyPre .updateFinalizeCopy 0x1ddd 216 32 u := by
  refine ⟨h.toStorage.of_agrees he.agrees hsp, hr, hc, ?_, ?_, he.rip, ?_, ?_, ?_,
    by decide, by decide, by decide, by decide, by decide +kernel⟩
  · exact program_text_slice hc 0x1ddd 3 (by decide +kernel)
  · exact (he.agrees.directionFlagClear (by simp [entryEffect, Effect.components]) h.df).df
  · rw [hsp]
    exact he.writes.2.1
  · rw [hsp]
    exact he.writes.1
  · exact he.writes.2.2

private theorem copiedState {c u t : RamState} {m : ByteArray}
    (hst : Storage .updateFinalizeCopy c)
    (hsrc : Absorbed (stackPtr c + 216) m c)
    (hA : (effectA c).Holds c u) (hB : (effectB u).Holds u t) : StateBytes t (absorbedHash m) := by
  have husp := effectA_rsp hA
  have htsp := effectB_rsp hB
  have hrsp := htsp.trans husp
  have hts := (hst.of_agrees hA.agrees husp).of_agrees hB.agrees htsp
  have allocatedC (offset len : Nat) (hl : offset + len ≤ 312) :
      ∀ i < len, (c.external[stackPtr c + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?).isSome :=
    (hst.stackWritable offset len hl).mem
  have allocatedT (offset len : Nat) (hl : offset + len ≤ 312) :
      ∀ i < len, (t.external[stackPtr c + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?).isSome := by
    simpa only [hrsp] using (hts.stackWritable offset len hl).mem
  have hWA := hA.writes.2.2.2.2
  have hWB := hB.writes
  simp only [effectB, Write.AllHold] at hWB
  rw [husp] at hWB
  have W0 : memLoad t.external (stackPtr c + 8) 64 = memLoad c.external (stackPtr c + 288) 64 :=
    hWB.2.2.2.trans (Digest.read_of_agrees hA.agrees fun i hi ↦
      effectA_untouched (off := 288) hi (by decide) (by decide))
  have W8 : memLoad t.external (stackPtr c + 16) 64 = memLoad c.external (stackPtr c + 296) 64 :=
    hWB.2.2.1.trans (Digest.read_of_agrees hA.agrees fun i hi ↦
      effectA_untouched (off := 296) hi (by decide) (by decide))
  have W16 : memLoad t.external (stackPtr c + 24) 32 = memLoad c.external (stackPtr c + 304) 32 := by
    have hpres : (Operand.mem (stackPtr u + 24) : Operand 32).read t =
        (Operand.mem (stackPtr u + 24) : Operand 32).read u :=
      Digest.read_of_agrees hB.agrees fun i hi ↦ effectB_untouched (off := 24) hi (by decide) (by decide)
    rw [husp] at hpres
    exact hpres.trans hWA
  have transfer (i : Nat) (hi : i < 20) :
      t.external[stackPtr c + 8 + BitVec.ofNat 64 i]? =
        c.external[stackPtr c + 288 + BitVec.ofNat 64 i]? := by
    have addOffset (offset j : Nat) :
        stackPtr c + BitVec.ofNat 64 offset + BitVec.ofNat 64 j =
          stackPtr c + BitVec.ofNat 64 (offset + j) := by
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    by_cases hi8 : i < 8
    · exact Digest.bytes_eq_of_read_eq (allocatedT 8 8 (by decide))
        (allocatedC 288 8 (by decide)) W0 i hi8
    change t.external[stackPtr c + BitVec.ofNat 64 8 + BitVec.ofNat 64 i]? =
      c.external[stackPtr c + BitVec.ofNat 64 288 + BitVec.ofNat 64 i]?
    rw [addOffset 8 i, addOffset 288 i]
    by_cases hi16 : i < 16
    · have h : t.external[stackPtr c + BitVec.ofNat 64 16 + BitVec.ofNat 64 (i - 8)]? =
          c.external[stackPtr c + BitVec.ofNat 64 296 + BitVec.ofNat 64 (i - 8)]? :=
        Digest.bytes_eq_of_read_eq (allocatedT 16 8 (by decide))
          (allocatedC 296 8 (by decide)) W8 (i - 8) (by omega)
      rw [addOffset 16 (i - 8), addOffset 296 (i - 8),
        show 16 + (i - 8) = 8 + i by omega, show 296 + (i - 8) = 288 + i by omega] at h
      exact h
    · have h : t.external[stackPtr c + BitVec.ofNat 64 24 + BitVec.ofNat 64 (i - 16)]? =
          c.external[stackPtr c + BitVec.ofNat 64 304 + BitVec.ofNat 64 (i - 16)]? :=
        Digest.bytes_eq_of_read_eq (allocatedT 24 4 (by decide))
          (allocatedC 304 4 (by decide)) W16 (i - 16) (by omega)
      rw [addOffset 24 (i - 16), addOffset 304 (i - 16),
        show 24 + (i - 16) = 8 + i by omega, show 304 + (i - 16) = 288 + i by omega] at h
      exact h

  have hbytes := hsrc.state
  rw [BitVec.add_assoc] at hbytes
  change (⟨(stackPtr c + 288).toNat, 20⟩ : MemoryRegion).HasBytes
    c.external (absorbedStateBytes m) at hbytes
  change (⟨(stackPtr t + 8).toNat, 20⟩ : MemoryRegion).HasBytes
    t.external (absorbedStateBytes m)
  refine ⟨hbytes.1, fun i ↦ ?_⟩
  have hi : i.val < 20 := by simpa only [absorbedStateBytes_size] using i.isLt
  have hb := hbytes.2 i
  simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hb ⊢
  rw [hrsp]
  exact (transfer i.val hi).trans hb

private theorem frame [Bindings] {b : ReturnBoundary} {s a c u t : RamState}
    (hs : Storage .updateFinalizeCopy s)
    (he : (entryEffect s).Holds s a) (hc : Streams.CopyPost b 0x1ddd 216 32 a c)
    (hA : (effectA c).Holds c u) (hB : (effectB u).Holds u t)
    (ha : stackPtr a = stackPtr s) (hcs : stackPtr c = stackPtr s)
    (hu : stackPtr u = stackPtr s) :
    AgreesExcept (Kind.updateFinalizeCopy.changes s) s t := by
  apply agrees_changes (((he.agrees.trans hc.agrees).trans hA.agrees).trans hB.agrees)
  · intro component h hm
    simp only [List.mem_append] at h
    rcases h with ((h | h) | h) | h
    all_goals
      simp only [entryEffect, effectA, effectB, Effect.components, List.map_cons, List.map_nil,
        List.cons_append, List.nil_append, Write.component, Operand.component, List.mem_cons,
        List.not_mem_nil, or_false] at h
    · rcases h with rfl | rfl | rfl | rfl <;>
        simp [Kind.changes, Kind.workRegisters, Kind.localChanges]
    · rcases h with rfl | rfl | rfl | rfl | rfl <;>
        simp_all [Component.isMem, Kind.changes, Kind.workRegisters, Kind.localChanges]
    · rcases h with rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp_all [Component.isMem, Kind.changes, Kind.workRegisters, Kind.localChanges]
    · rcases h with rfl | rfl | rfl | rfl | rfl <;>
        simp_all [Component.isMem, Kind.changes, Kind.workRegisters, Kind.localChanges]
  · intro x component h hcover
    simp only [List.mem_append] at h
    rcases h with ((h | h) | h) | h
    · exact (entry_noMem h hcover).elim
    · exact hs.localWithin (offset := 32) (len := 96) (by decide)
        (ha ▸ copy_mem h hcover)
    · exact hs.localWithin (offset := 24) (len := 4) (by decide)
        (hcs ▸ effectA_mem h hcover)
    · rcases effectB_mem h hcover with h | h
      · exact hs.localWithin (offset := 16) (len := 8) (by decide) (hu ▸ h)
      · exact hs.localWithin (offset := 8) (len := 8) (by decide) (hu ▸ h)

theorem prepare [Bindings] {b : ReturnBoundary} {m : ByteArray} {s : RamState}
    (h : Pre .updateFinalizeCopy b m s) : ∃ t, Run b s t ∧ Prepared m t := by
  obtain ⟨n, a, ha, har, hac, he⟩ := entry h
  have hasp : stackPtr a = stackPtr s := he.agrees.read (n := 64) (r := 4)
    (by simp [entryEffect, Effect.components])
  have hcp := copyPre h har hac he hasp
  have hsa : Absorbed (stackPtr a + 216) m a := by
    rw [hasp]
    exact absorbed_of_copy h.absorbed (fun _ _ ↦ he.agrees.byte fun _ hc ↦ entry_noMem hc)
  obtain ⟨c, hcopy⟩ := Streams.copy_context h.stride b h.boundaryOutside hcp
  have hcsp := hcopy.rsp.trans hasp
  have hcs := hcp.toStorage.of_agrees hcopy.agrees hcopy.rsp
  have hsrc := hcopy.sourceAbsorbed hcp hsa
  have hd := hcopy.absorbed hsa
  obtain ⟨k, u, t, hn, hr, hc, hA, hB⟩ :=
    normalize hcopy.ready hcopy.code h.boundaryOutside hcs hcopy.rip
  have husp := effectA_rsp hA
  have htsp := effectB_rsp hB
  have hrsp := htsp.trans husp
  have htOrigin := hrsp.trans hcsp
  have hag := frame h.toStorage he hcopy hA hB hasp hcsp (husp.trans hcsp)
  have htail : (⟨(stackPtr t + 32).toNat, (tailBytes m).size⟩ : MemoryRegion).HasBytes
      t.external (tailBytes m) := by
    rw [hrsp]
    apply hasBytes_of_copy _ hd.tail
    intro i hi
    have hi64 : i < 64 := Nat.lt_trans hi (tailBytes_lt m)
    have hbyte := hB.agrees.byte (effectB_untouched (off := 32) hi64 (by decide) (by decide))
    rw [husp] at hbyte
    exact hbyte.trans (hA.agrees.byte (effectA_untouched (off := 32) hi64 (by decide) (by decide)))
  have hpos : (Operand.reg 14 : Operand 64).read t = BitVec.ofNat 64 (m.size % 64) := by
    have hp := hd.position
    change (Operand.mem (stackPtr c + 32 + 63) : Operand 8).read c = _ at hp
    rw [BitVec.add_assoc, size_tailBytes] at hp
    change (Operand.mem (stackPtr c + 95) : Operand 8).read c = _ at hp
    rw [hB.agrees.read (n := 64) (r := 14) (by simp [effectB, Effect.components]), hA.writes.1, hp]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  have hblocks : (Operand.reg 15 : Operand 64).read t = BitVec.ofNat 64 (m.size / 64) := by
    have hb := hd.blocks
    change (Operand.mem (stackPtr c + 32 + 64) : Operand 64).read c = _ at hb
    rw [BitVec.add_assoc] at hb
    rw [hB.agrees.read (n := 64) (r := 15) (by simp [effectB, Effect.components]), hA.writes.2.1]
    exact hb
  have hdf := (hag.directionFlagClear (by simp [Kind.changes, Kind.workRegisters, Kind.localChanges])
    h.df).df
  have hsaved : savedOutput t = savedOutput s := by
    unfold savedOutput
    rw [htOrigin]
    apply Digest.read_of_agrees (((he.agrees.trans hcopy.agrees).trans hA.agrees).trans hB.agrees)
    intro i hi component hmem hcover
    simp only [List.mem_append] at hmem
    rcases hmem with ((hmem | hmem) | hmem) | hmem
    · exact entry_noMem hmem hcover
    · exact Digest.covers_apart (a := 32) (len := 96) (b := 192) (count := 8) rfl hi
        (by decide) (by decide) (by decide) (hasp ▸ copy_mem hmem hcover)
    · exact effectA_untouched (off := 192) (len := 8) hi (by decide) (by decide) component hmem
        (hcsp.symm ▸ hcover)
    · exact effectB_untouched (off := 192) (len := 8) hi (by decide) (by decide) component hmem
        ((husp.trans hcsp).symm ▸ hcover)
  exact ⟨t, ⟨⟨n + 12 + k, (ha.trans hcopy.advances).trans hn⟩, hr, hc, htOrigin, hsaved, hag⟩,
    ⟨⟨hpos, hblocks⟩, hB.rip, hdf, copiedState hcs hsrc hA hB, htail⟩⟩

end Sha1.Proofs.Buffered.Finalize.Family
