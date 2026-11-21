import Md5.Proofs.Buffered.Finalize.Streams.Slices.Padded
import Md5.Proofs.Buffered.Finalize.Streams.Slices.Branch
import Md5.Proofs.Buffered.Finalize.Streams.Slices.Transition

namespace Md5.Proofs.Buffered.Finalize.Streams.Slices

open Md5.Spec Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Block

structure BranchReady [Bindings] (message : ByteArray) (s : RamState) (update : Bool := false) : Prop
    extends Storage (streamKind update) s where
  ready : ReadyToStep s
  code : CodeIn Extracted.programImage s
  rip : s.RIP = if message.size % 64 < 56 then (BitVec.ofNat 64 (relocated update 0x10053d)) else (BitVec.ofNat 64 (relocated update 0x10048d))
  first : (⟨(stackPtr s + 16).toNat, 64⟩ : MemoryRegion).HasBytes s.external (firstBlock message)
  buffer : (⟨(stackPtr s).toNat, 16⟩ : MemoryRegion).HasBytes s.external
    ⟨(absorbedBuffer message).toBytes.toArray⟩
  blocks : (.reg 14 : Operand 64).read s = BitVec.ofNat 64 (message.size / 64)
  position : (.reg 15 : Operand 64).read s = BitVec.ofNat 64 (message.size % 64)

theorem branch {update : Bool} [Bindings] {boundary : ReturnBoundary} {message : ByteArray} {s u : RamState}
    (hOutside : ¬ InProgram boundary.rip) (h : Padded (update := update) boundary message s u) :
    ∃ t, Transition (update := update) boundary s t ∧ BranchReady (update := update) message t := by
  cases update
  case' false => let update := false
  case' true => let update := true
  all_goals
    obtain ⟨t, ht, hr, hc, hip, ha⟩ := padding_branch (update := update) h.ready h.code hOutside h.rip
      (Nat.mod_lt _ (by decide)) h.remaining
    have hsp : stackPtr t = stackPtr u := ha.read (n := 64) (r := 4) (by simp)
    have hmem (a : BitVec 64) : t.external[a]? = u.external[a]? := by
      apply ha.byte
      intro c hc hcover
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> exact hcover.elim
    have htr : Transition (update := update) boundary u t := ⟨⟨2, ht⟩, ha.mono (by
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;> simp [update, streamKind, Kind.changes])⟩
    refine ⟨t, (Transition.trans ⟨h.advances, h.agrees⟩ htr),
      h.storage.of_agrees ha hsp, hr, hc, hip, ?_, ?_, ?_, ?_⟩
    · rw [hsp]
      exact ⟨h.padded.1, fun i ↦ (hmem _).trans (h.padded.2 i)⟩
    · rw [hsp]
      exact ⟨h.result.1, fun i ↦ (hmem _).trans (h.result.2 i)⟩
    · rw [ha.read (n := 64) (r := 14) (by simp)]
      exact h.blocks
    · rw [ha.read (n := 64) (r := 15) (by simp)]
      exact h.position

theorem BranchReady.short {update : Bool} [Bindings] {message : ByteArray} {s : RamState}
    (h : BranchReady (update := update) message s) (hShort : message.size % 64 < 56) : LengthReady (update := update) message s := by
  cases update
  case' false => let update := false
  case' true => let update := true
  all_goals
    refine ⟨h.toStorage, h.ready, h.code, ?_, ?_, ?_, h.blocks, h.position⟩
    · simpa only [ite_eq_left hShort] using h.rip
    · have hb := bytes_of_hasBytes h.first
      simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq, size_firstBlock] at hb
      intro i hi
      simpa only [ite_eq_left hShort] using hb i (by omega)
    · simpa only [paddedBuffer, ite_eq_left hShort] using h.buffer

end Md5.Proofs.Buffered.Finalize.Streams.Slices
