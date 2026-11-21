import Md5.Proofs.Buffered.Update.Slices.Full.Contracts
import Md5.Proofs.Buffered.Update.Counter

namespace Md5.Proofs.Buffered.Update.Slices

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Block

abbrev counterAddEffect (variant : Bool) :=
  Update.Counter.addM64R64Effect (pc variant 0x1003c5) 2 (.sib 4 none 0 (.d32 272))

theorem counterAddEffect_components {variant : Bool} (s : RamState) :
    (counterAddEffect variant s).components = [.mem (stackPtr s + 272) 8, .flags, .rip] := by
  x86_norm [counterAddEffect, Update.Counter.addM64R64Effect, stackPtr]
  rfl

theorem counter_add {variant : Bool} [Bindings] {boundary : ReturnBoundary} {message input : ByteArray}
    {s u : RamState} {changes : List Component}
    (h : UpdatePre (kind variant) boundary message input s) (ha : AgreesExcept changes s u)
    (hsp : stackPtr u = stackPtr s) (hrip : u.RIP = (pc variant 0x1003c5))
    (hready : ReadyToStep u) (hcode : CodeIn Extracted.programImage u) :
    ∃ v, Advances boundary 1 u v ∧ ReadyToStep v ∧ CodeIn Extracted.programImage v ∧
      (counterAddEffect variant u).Holds u v := by
  have hw : MemoryRoutines.WritableRange u (stackPtr u + 272) 8 := by
    rw [hsp]
    cases variant <;> exact h.contextWritable_of_agrees ha 80 8 (by decide)
  have hbytes : CodeIn (codeRange (pc variant 0x1003c5) [0x48, 0x01, 0x94, 0x24, 0x10, 0x01, 0x00, 0x00]) u :=
    by
      cases variant with
      | false => exact program_text_slice hcode 0x3c5 8 (by decide +kernel)
      | true => exact program_text_slice hcode 0x1975 8 (by decide +kernel)
  have hap : RangeApart (stackPtr u + 272) 8 (pc variant 0x1003c5) 8 := by
    intro i hi j hj heq
    apply hw.code i hi
    rw [heq]
    cases variant with
    | false =>
      have ht := text_address_in_program (0x3c5 + j) (by
        have hs : 0x3cd ≤ Extracted.textBytes.size := by decide +kernel
        omega)
      simpa [pc, Extracted.textAddress, BitVec.ofNat_add, ← BitVec.add_assoc] using ht
    | true =>
      have ht := text_address_in_program (0x1975 + j) (by
        have hs : 0x197d ≤ Extracted.textBytes.size := by decide +kernel
        omega)
      simpa [pc, Extracted.textAddress, BitVec.ofNat_add, ← BitVec.add_assoc] using ht
  obtain ⟨v, hv, hr, he⟩ := (Update.Counter.add_m64_r64_effect_step
    (pc variant 0x1003c5) 0x48 (by unfold RexWPrefix; decide) 2 (.sib 4 none 0 (.d32 272))
    (by decide) (by decide) (by decide)).advances hready hbytes
    ⟨hrip, ⟨hw.readable.low, hw.readable.mem, hw.tables⟩, hap⟩
    (by
      cases variant with
      | false => exact text_address_ne_return h.boundaryOutside 0x3cd (by decide +kernel)
      | true => exact text_address_ne_return h.boundaryOutside 0x197d (by decide +kernel))
  refine ⟨v, hv, hr, ?_, he⟩
  apply CodeIn.of_agreesExcept he.agrees _ hcode
  intro x hx c hc hcover
  change c ∈ (counterAddEffect variant u).components at hc
  rw [counterAddEffect_components] at hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · obtain ⟨i, hi, heq⟩ := hcover
    exact hw.code i hi (heq ▸ ⟨x.2, hx⟩)
  · exact hcover.elim
  · exact hcover.elim

set_option maxRecDepth 4096 in
theorem counter_add_agrees {variant : Bool} {s u v : RamState}
    (hsp : stackPtr u = stackPtr s) (he : (counterAddEffect variant u).Holds u v) :
    AgreesExcept ((kind variant).changes s) u v := by
  have ha : AgreesExcept [.mem (stackPtr u + 272) 8, .flags, .rip] u v := by
    rw [← counterAddEffect_components]
    exact he.agrees
  apply ha.widen
  · intro c hc hm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    all_goals cases variant <;> simp_all [kind, Component.isMem, UpdateKind.changes]
  · intro address c hc hcover
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · refine ⟨.mem ((kind variant).context s) 88, by cases variant <;> simp [kind, UpdateKind.changes], ?_⟩
      obtain ⟨i, hi, rfl⟩ := hcover
      refine ⟨80 + i, by omega, ?_⟩
      rw [hsp, BitVec.ofNat_add]
      rw [kind_context]
      change stackPtr s + 272 + BitVec.ofNat 64 i =
        stackPtr s + 192 + (80 + BitVec.ofNat 64 i)
      rw [← BitVec.add_assoc (stackPtr s + 192) 80, BitVec.add_assoc (stackPtr s) 192 80]
      rfl
    · exact hcover.elim
    · exact hcover.elim

theorem counter_add_write {variant : Bool} {u v : RamState} (he : (counterAddEffect variant u).Holds u v) :
    (Operand.mem (stackPtr u + 272) : Operand 64).read v =
      (Operand.mem (stackPtr u + 272) : Operand 64).read u + (Operand.reg 2 : Operand 64).read u := by
  have hw := he.writes
  x86_norm [counterAddEffect, Update.Counter.addM64R64Effect] at hw
  exact hw

set_option maxRecDepth 4096 in
theorem counter_add_buffer {variant : Bool} [Bindings] {boundary : ReturnBoundary} {message input : ByteArray}
    {buffer : Standards.RFC.MD5.Buffer} {s u v : RamState}
    (h : UpdatePre (kind variant) boundary message input s) (hsp : stackPtr u = stackPtr s)
    (he : (counterAddEffect variant u).Holds u v)
    (hb : (⟨((kind variant).context s).toNat + 64, 16⟩ : MemoryRegion).HasBytes
      u.external ⟨buffer.toBytes.toArray⟩) :
    (⟨((kind variant).context s).toNat + 64, 16⟩ : MemoryRegion).HasBytes
      v.external ⟨buffer.toBytes.toArray⟩ := by
  have hhi : ((kind variant).context s).toNat + 88 < 2^32 := h.contextBounded
  have hbase : stackPtr u + 272 = (kind variant).context s + 80 := by
    rw [hsp]
    rw [kind_context]
    change stackPtr s + 272 = stackPtr s + 192 + 80
    rw [BitVec.add_assoc]
    rfl
  have hf : MemoryWriteFrame u v
      #v[(⟨((kind variant).context s).toNat + 80, 8⟩ : MemoryRegion)] := by
    apply he.agrees.memoryWriteFrame
    intro c hc address hcover
    rw [counterAddEffect_components] at hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · refine ⟨⟨((kind variant).context s).toNat + 80, 8⟩, by simp, ?_⟩
      apply contains_of_mem_covers (show
        (⟨((kind variant).context s).toNat + 80, 8⟩ : MemoryRegion).Bounded from by
          change ((kind variant).context s).toNat + 80 + 8 < 2^32
          omega)
      rw [hbase] at hcover
      change (Component.mem ((kind variant).context s + 80#64) 8).Covers address at hcover
      simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using hcover
    · exact hcover.elim
    · exact hcover.elim
  apply hasBytes_of_memoryWriteFrame hf hb
  · change ((kind variant).context s).toNat + 64 + 16 < 2^32
    omega
  · intro region hr
    simp only [Vector.mem_mk, List.mem_toArray, List.mem_cons, List.not_mem_nil, or_false] at hr
    subst region
    intro address ha hb
    dsimp only [MemoryRegion.Contains] at ha hb
    omega

end Md5.Proofs.Buffered.Update.Slices
