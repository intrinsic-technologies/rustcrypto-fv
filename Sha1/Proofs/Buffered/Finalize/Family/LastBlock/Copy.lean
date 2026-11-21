import Sha1.Proofs.Buffered.Finalize.Family.Contracts
import Sha1.Proofs.Buffered.Finalize.Family.LastBlock.Steps
import Sha1.Proofs.Buffered.Finalize.Digest.Final

namespace Sha1.Proofs.Buffered.Finalize.Family.LastBlock

open Sha1.Spec Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha1.Proofs.Compress.Machine
open Sha1.Proofs.Buffered.Finalize.Steps
open Sha1.Proofs.Buffered.Finalize.Digest.BlockCopy (cover_shift)

private def WritesWithin (s : RamState) (e : Effect) (lo hi : Nat) : Prop :=
  ∀ x c, c ∈ e.components → c.Covers x →
    Component.Covers (.mem (stackPtr s + BitVec.ofNat 64 lo) (hi - lo)) x

private theorem length_writesWithin (s : RamState) : WritesWithin s (lengthEffect s) 88 192 := by
  intro x c hc hcov
  simp only [lengthEffect, Effect.components, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, Write.component, Operand.component,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact hcov.elim
  · exact cover_shift (d := 88) (len := 8) hcov (by decide) (by decide)
  · exact cover_shift (d := 184) (len := 8) hcov (by decide) (by decide)

private theorem upper_writesWithin (s : RamState) :
    WritesWithin s (upperCopyEffect s) 152 184 := by
  intro x c hc hcov
  simp only [upperCopyEffect, Effect.components, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, Write.component, Operand.component,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact hcov.elim
  · exact cover_shift (d := 176) (len := 8) hcov (by decide) (by decide)
  · exact cover_shift (d := 168) (len := 8) hcov (by decide) (by decide)
  · exact cover_shift (d := 160) (len := 8) hcov (by decide) (by decide)
  · exact cover_shift (d := 152) (len := 8) hcov (by decide) (by decide)

private theorem lower_writesWithin (s : RamState) :
    WritesWithin s (lowerCopyEffect s) 128 152 := by
  intro x c hc hcov
  simp only [lowerCopyEffect, Effect.components, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, Write.component, Operand.component,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact hcov.elim
  · exact cover_shift (d := 144) (len := 8) hcov (by decide) (by decide)
  · exact cover_shift (d := 136) (len := 8) hcov (by decide) (by decide)
  · exact cover_shift (d := 128) (len := 8) hcov (by decide) (by decide)

private theorem WritesWithin.disjoint {s : RamState} {e : Effect} {lo hi offset count i : Nat}
    (h : WritesWithin s e lo hi) (hlo : lo ≤ hi) (hhi : hi ≤ 192)
    (hcount : offset + count ≤ 2 ^ 64) (hi' : i < count)
    (hApart : hi ≤ offset ∨ offset + count ≤ lo)
    (c : Component) (hc : c ∈ e.components) :
    ¬ c.Covers (stackPtr s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i) := by
  intro hcov
  apply Digest.covers_apart (a := lo) (len := hi - lo) (b := offset) (count := count)
    rfl hi' (by omega) hcount (by omega)
  exact h _ _ hc hcov

private theorem WritesWithin.byte {s t : RamState} {e : Effect} {lo hi j : Nat}
    (h : WritesWithin s e lo hi) (he : e.Holds s t) (hlo : lo ≤ hi) (hhi : hi ≤ 192)
    (hj : j < 312) (hapart : hi ≤ j ∨ j < lo) :
    t.external[stackPtr s + BitVec.ofNat 64 j]? = s.external[stackPtr s + BitVec.ofNat 64 j]? := by
  apply he.agrees.byte
  intro c hc
  simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
    h.disjoint hlo hhi (offset := j) (count := 1) (i := 0) (by omega) (by decide) (by omega) c hc

private theorem phase_run [Bindings] {b : ReturnBoundary} {s t : RamState} {fuel lo hi : Nat}
    {e : Effect} (storage : Storage .updateFinalizeCopy s) (code : CodeIn Extracted.programImage s)
    (advance : Advances b fuel s t) (ready : ReadyToStep t) (effect : e.Holds s t)
    (frame : WritesWithin s e lo hi) (hlo : lo ≤ hi) (hhi : hi ≤ 192)
    (regs : ∀ c ∈ e.components, c.isMem = false → c ∈ Kind.updateFinalizeCopy.changes s) :
    Run b s t := by
  have covers (x : BitVec 64) (c : Component) (hc : c ∈ e.components) (hx : c.Covers x) :=
    storage.localWithin (offset := lo) (len := hi - lo) (by
      simp only [Kind.stackBytes]; omega) (frame x c hc hx)
  have agrees := agrees_changes effect.agrees regs covers
  have rsp : stackPtr t = stackPtr s := agrees.read (n := 64) (r := 4)
    (by simp [Kind.changes, Kind.localChanges, Kind.workRegisters])
  refine ⟨⟨fuel, advance⟩, ready, effect.codeIn ?_ code, rsp, ?_, agrees⟩
  · intro x hx c hc hcov
    exact storage.stackAvoids x.1 (storage.localCover (covers x.1 c hc hcov)) (.inl ⟨x.2, hx⟩)
  · unfold savedOutput
    rw [rsp]
    apply Digest.read_of_agrees effect.agrees
    intro i hi
    exact frame.disjoint hlo hhi (offset := 192) (count := 8) (by decide) hi (.inl hhi)

private theorem length_value_eq {s : RamState} {m : ByteArray} (pos : Position m s) :
    lengthValue s = bswapSpec (Digest.lengthWord m) := by
  have h32 : (Operand.reg 14 : Operand 32).read s = BitVec.ofNat 32 (m.size % 64) := by
    change ((Operand.reg 14 : Operand 64).read s).setWidth 32 = _
    rw [pos.position]
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  rw [lengthValue, h32, pos.blocks, Sha1.Proofs.Wrapper.Hash.tail_shift_or_blocks]
  rfl

theorem copy_last_block [Bindings] {b : ReturnBoundary} {m : ByteArray} {s : RamState}
    (outside : ¬ InProgram b.rip) (storage : Storage .updateFinalizeCopy s)
    (ready : ReadyToStep s) (code : CodeIn Extracted.programImage s) (h : Last m s) :
    ∃ t, Run b s t ∧ t.RIP = 0x101f69 ∧ StateBytes t (penultimateHash m) ∧
      (⟨(stackPtr t + 128).toNat, 64⟩ : MemoryRegion).HasBytes t.external (Digest.lastBlock m) := by
  have lengthCode : CodeIn (codeRange 0x101ef3 lengthBytes) s :=
    program_text_slice code 0x1ef3 27 (by decide +kernel)
  obtain ⟨n, u, ua, ur, _, ul⟩ := length_execution b outside s ready lengthCode ⟨storage, h.rip⟩
  have runU := phase_run storage code ua ur ul (length_writesWithin s) (by decide) (by decide) (by
    intro c hc hm
    simp only [lengthEffect, Effect.components, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, Write.component, Operand.component,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [Component.isMem, Kind.changes, Kind.workRegisters])
  have storageU := storage.of_agrees runU.agrees runU.rsp
  have upperCode : CodeIn (codeRange 0x101f0e upperCopyBytes) u :=
    program_text_slice runU.code 0x1f0e 52 (by decide +kernel)
  obtain ⟨n, v, va, vr, _, vu⟩ := upperCopy_execution b outside u ur upperCode ⟨storageU, ul.rip⟩
  have runV := phase_run storageU runU.code va vr vu (upper_writesWithin u) (by decide) (by decide) (by
    intro c hc hm
    simp only [upperCopyEffect, Effect.components, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, Write.component, Operand.component,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [Component.isMem, Kind.changes, Kind.workRegisters])
  have storageV := storageU.of_agrees runV.agrees runV.rsp
  have lowerCode : CodeIn (codeRange 0x101f42 lowerCopyBytes) v :=
    program_text_slice runV.code 0x1f42 39 (by decide +kernel)
  obtain ⟨n, t, ta, tr, _, tl⟩ := lowerCopy_execution b outside v vr lowerCode ⟨storageV, vu.rip⟩
  have runT := phase_run storageV runV.code ta tr tl (lower_writesWithin v) (by decide) (by decide) (by
    intro c hc hm
    simp only [lowerCopyEffect, Effect.components, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, Write.component, Operand.component,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [Component.isMem, Kind.changes, Kind.workRegisters])
  have run := runU.trans (runV.trans runT)
  have rspV := runV.rsp.trans runU.rsp
  have storageT := storageV.of_agrees runT.agrees runT.rsp
  have unchanged (j : Nat) (hj : j < 88) :
      t.external[stackPtr s + BitVec.ofNat 64 j]? = s.external[stackPtr s + BitVec.ofNat 64 j]? := by
    have hU := (length_writesWithin s).byte ul (by decide) (by decide) (by omega) (Or.inr hj)
    have hV := (upper_writesWithin u).byte vu (by decide) (by decide) (by omega) (j := j) (by omega)
    have hT := (lower_writesWithin v).byte tl (by decide) (by decide) (by omega) (j := j) (by omega)
    rw [runU.rsp] at hV
    rw [rspV] at hT
    exact hT.trans (hV.trans hU)
  have state : StateBytes t (penultimateHash m) := by
    rw [StateBytes, run.rsp]
    apply Digest.hasBytes_resize' _ (Wrapper.Hash.Serialize.stateBytes_size _)
    apply hasBytes_of_copy (src := stackPtr s + 8) (dst := stackPtr s + 8) _
      (Digest.hasBytes_resize h.state (Wrapper.Hash.Serialize.stateBytes_size _).symm)
    intro i hi
    rw [Wrapper.Hash.Serialize.stateBytes_size] at hi
    change t.external[stackPtr s + BitVec.ofNat 64 8 + BitVec.ofNat 64 i]? =
      s.external[stackPtr s + BitVec.ofNat 64 8 + BitVec.ofNat 64 i]?
    rw [Digest.stack_offset]
    exact unchanged (8 + i) (by omega)
  have upperWrites := vu.writes
  simp only [upperCopyEffect, Write.AllHold] at upperWrites
  have lowerWrites := tl.writes
  simp only [lowerCopyEffect, Write.AllHold] at lowerWrites
  have prefixCopy (q i : Nat) (hq : q < 7) (hi : i < 8) :
      t.external[stackPtr s + BitVec.ofNat 64 (128 + 8 * q + i)]? =
      s.external[stackPtr s + BitVec.ofNat 64 (32 + 8 * q + i)]? := by
    let src := 32 + 8 * q
    let dst := 128 + 8 * q
    change t.external[stackPtr s + BitVec.ofNat 64 (dst + i)]? =
      s.external[stackPtr s + BitVec.ofNat 64 (src + i)]?
    have eqU := (length_writesWithin s).byte ul (by decide) (by decide)
      (j := src + i) (by dsimp [src]; omega) (by dsimp [src]; omega)
    by_cases small : q < 3
    · have write : (Operand.mem (stackPtr v + BitVec.ofNat 64 dst) : Operand 64).read t =
          (Operand.mem (stackPtr v + BitVec.ofNat 64 src) : Operand 64).read v := by
        rcases (show q = 0 ∨ q = 1 ∨ q = 2 by omega) with rfl | rfl | rfl
        · exact lowerWrites.2.2.2.2
        · exact lowerWrites.2.2.2.1
        · exact lowerWrites.2.2.1
      have copy := stack_word_bytes storageV storageT runT.rsp (src := src) (dst := dst) (by simp only [Kind.stackBytes]; dsimp [src]; omega)
        (by simp only [Kind.stackBytes]; dsimp [dst]; omega) write i hi
      rw [BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add] at copy
      have eqV := (upper_writesWithin u).byte vu (by decide) (by decide)
        (j := src + i) (by dsimp [src]; omega) (by dsimp [src]; omega)
      rw [rspV] at copy
      rw [runU.rsp] at eqV
      exact copy.trans (eqV.trans eqU)
    · have write : (Operand.mem (stackPtr u + BitVec.ofNat 64 dst) : Operand 64).read v =
          (Operand.mem (stackPtr u + BitVec.ofNat 64 src) : Operand 64).read u := by
        rcases (show q = 3 ∨ q = 4 ∨ q = 5 ∨ q = 6 by omega) with rfl | rfl | rfl | rfl
        · exact upperWrites.2.2.2.2
        · exact upperWrites.2.2.2.1
        · exact upperWrites.2.2.1
        · exact upperWrites.2.1
      have copy := stack_word_bytes storageU storageV runV.rsp (src := src) (dst := dst) (by simp only [Kind.stackBytes]; dsimp [src]; omega)
        (by simp only [Kind.stackBytes]; dsimp [dst]; omega) write i hi
      rw [BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add] at copy
      have eqT := (lower_writesWithin v).byte tl (by decide) (by decide)
        (j := dst + i) (by dsimp [dst]; omega) (.inl (by dsimp [dst]; omega))
      rw [runU.rsp] at copy
      rw [rspV] at eqT
      exact eqT.trans (copy.trans eqU)
  have length (i : Nat) (hi : i < 8) :
      t.external[stackPtr s + BitVec.ofNat 64 (184 + i)]? =
        some ((Digest.lengthBlockBytes m)[i]!) := by
    have eqV := (upper_writesWithin u).byte vu (by decide) (by decide) (j := 184 + i)
      (by omega) (.inl (by omega))
    have eqT := (lower_writesWithin v).byte tl (by decide) (by decide) (j := 184 + i)
      (by omega) (.inl (by omega))
    rw [runU.rsp] at eqV
    rw [rspV] at eqT
    rw [eqT, eqV]
    have sizeBytes := Bytes.of_memLoad (n := 64) (storageU.stackWritable 184 8 (by decide)).mem i hi
    have writes := ul.writes
    simp only [lengthEffect, Write.AllHold] at writes
    rw [runU.rsp, BitVec.add_assoc, ← BitVec.ofNat_add] at sizeBytes
    have word : memLoad u.external (stackPtr s + BitVec.ofNat 64 184) 64 = lengthValue s := writes.2.2.2
    rw [sizeBytes, word, length_value_eq h.toPosition, Digest.storedByte_bswap64 _ i hi,
      Digest.getElem_lengthBlockBytes _ i hi]
  have block : Bytes t.external (stackPtr t + 128) 64 (fun i ↦ (Digest.lastBlock m)[i]!) := by
    apply Digest.lastBlock_bytes
    · intro i hi
      change t.external[stackPtr t + BitVec.ofNat 64 128 + BitVec.ofNat 64 i]? = _
      rw [run.rsp, Digest.stack_offset]
      have copy := prefixCopy (i / 8) (i % 8) (by omega) (by omega)
      have index : 8 * (i / 8) + i % 8 = i := by omega
      rw [Nat.add_assoc, Nat.add_assoc, index] at copy
      rw [copy, ← Digest.stack_offset (stackPtr s) 32 i]
      exact h.prefixBytes i hi
    · intro i hi
      change t.external[stackPtr t + BitVec.ofNat 64 128 + BitVec.ofNat 64 (56 + i)]? = _
      rw [run.rsp, Digest.stack_offset, ← Nat.add_assoc]
      exact length i hi
  exact ⟨t, run, tl.rip, state, Digest.hasBytes_of_bytes_size block (Digest.size_lastBlock m)⟩

end Sha1.Proofs.Buffered.Finalize.Family.LastBlock
