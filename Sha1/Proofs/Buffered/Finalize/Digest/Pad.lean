import Sha1.Proofs.Buffered.Finalize.Digest.Prepare
import Sha1.Proofs.Buffered.Finalize.Digest.Padding
import Sha1.Proofs.Buffered.Finalize.Digest.Blocks

namespace Sha1.Proofs.Buffered.Finalize.Digest

open Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha1.Proofs.Compress.Machine

structure Padded [Bindings] (boundary : ReturnBoundary) (message : ByteArray)
    (s t : RamState) : Prop where
  advances : ∃ fuel, Advances boundary fuel s t
  ready : ReadyToStep t
  code : CodeIn Extracted.programImage t
  rip : t.RIP = 0x100132
  storage : Storage .digestCopy t
  df : DirectionFlagClear t.RFLAGS
  rsp : stackPtr t = stackPtr s
  position : (Operand.reg 15 : Operand 64).read t = BitVec.ofNat 64 (message.size % 64)
  remaining : (Operand.reg 14 : Operand 64).read t = BitVec.ofNat 64 (63 - message.size % 64)
  blocks : (Operand.reg 12 : Operand 64).read t = BitVec.ofNat 64 (message.size / 64)
  padded : Bytes t.external (stackPtr t + 24) 64 (fun i ↦ (firstBlock message)[i]!)
  state : (⟨(stackPtr t).toNat, 20⟩ : MemoryRegion).HasBytes t.external
    (absorbedStateBytes message)
  agrees : AgreesExcept (Kind.digestCopy.changes s) s t

theorem call_preserves_bytes [Bindings] {boundary : ReturnBoundary} {ret base : BitVec 64}
    {s t : RamState} {len : Nat} {bytes : Nat → UInt8}
    (h : CallSiteResult boundary ret s t) (hb : Bytes s.external base len bytes)
    (hd : RangeApart base len (rdi.read s) (MemoryRoutines.rdx.read s).toNat)
    (hs : RangeApart base len (pushAddr s) 8) : Bytes t.external base len bytes := by
  apply hb.of_agreesExcept h.agrees
  intro i hi c hc hcover
  simp only [callSiteChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact hcover.elim
  · obtain ⟨j, hj, he⟩ := hcover
    exact hd i hi j hj he
  · obtain ⟨j, hj, he⟩ := hcover
    exact hs i hi j hj he

theorem pad [bindings : Bindings] {boundary : ReturnBoundary} {message : ByteArray}
    {s v : RamState} (hstride : UnitStringStride bindings)
    (hout : ¬ InProgram boundary.rip) (hv : Prepared boundary message s v) :
    ∃ t, Padded boundary message s t := by
  have hn : message.size % 64 < 64 := Nat.mod_lt _ (by decide)
  obtain ⟨n1, u1, h1, hr1, hc1, he1⟩ := Prefix.run hv.ready hv.code hout hv.rip
  have hsp1 : stackPtr u1 = stackPtr v := he1.agrees.read (n := 64) (r := 4) (by
    simp [Prefix.effect, Effect.components])
  have h15₁ : (Operand.reg 15 : Operand 64).read u1 = BitVec.ofNat 64 (message.size % 64) :=
    (he1.agrees.read (n := 64) (r := 15) (by simp [Prefix.effect, Effect.components])).trans
      hv.position
  have h12₁ : (Operand.reg 12 : Operand 64).read u1 = BitVec.ofNat 64 (message.size / 64) :=
    (he1.agrees.read (n := 64) (r := 12) (by simp [Prefix.effect, Effect.components])).trans
      hv.blocks
  have h14₁ : (Operand.reg 14 : Operand 64).read u1 =
      BitVec.ofNat 64 (63 - message.size % 64) := by
    have hw := he1.writes
    simp only [Prefix.effect, Write.AllHold] at hw
    rw [hw, hv.position]
    exact remaining_xor _ hn
  have hs1 : Storage .digestCopy u1 := hv.storage.of_agrees he1.agrees hsp1
  have hdf1 : DirectionFlagClear u1.RFLAGS :=
    (he1.agrees.directionFlagClear (by simp [Prefix.effect, Effect.components]) ⟨hv.df⟩).df
  have hm1 : u1.external = v.external := he1.agrees.external (by
    simp [Prefix.effect, Effect.components, Component.Covers])
  obtain ⟨n2, u2, h2, hr2, hc2, he2⟩ := Padding.run hr1 hc1 hout
    ⟨hs1, he1.rip, by rw [h15₁, BitVec.toNat_ofNat]; omega⟩
  have hsp2 : stackPtr u2 = stackPtr v := (Padding.effect_rsp he2).trans hsp1
  have hw2 := he2.writes
  simp only [Padding.effect, Write.AllHold] at hw2
  rw [h15₁, hsp1] at hw2
  have hs2 : Storage .digestCopy u2 := hs1.of_agrees he2.agrees (Padding.effect_rsp he2)
  have hdf2 : DirectionFlagClear u2.RFLAGS :=
    (he2.agrees.directionFlagClear (by simp [Padding.effect, Effect.components]) ⟨hdf1⟩).df
  have hDst : rdi.read u2 = stackPtr u2 + BitVec.ofNat 64 (message.size % 64 + 25) := by
    change (Operand.reg 7 : Operand 64).read u2 = _
    rw [hw2.2.1, hsp2, BitVec.add_assoc]
    congr 1
    rw [BitVec.ofNat_add]
    rfl
  have hdx : MemoryRoutines.rdx.read u2 = BitVec.ofNat 64 (63 - message.size % 64) :=
    hw2.2.2.2.trans h14₁
  obtain ⟨t, ht⟩ := Padding.memset hstride hr2 hc2 hout hs2 he2.rip hdf2 hn hDst hdx
  have hspt : stackPtr t = stackPtr v := ht.rsp.trans hsp2
  have hmarker_addr : stackPtr v + BitVec.ofNat 64 (message.size % 64) + 24 =
      stackPtr v + BitVec.ofNat 64 (24 + message.size % 64) := by
    rw [BitVec.add_assoc, Nat.add_comm, BitVec.ofNat_add]
    rfl
  rw [hmarker_addr] at hw2
  have hpadByte (a : BitVec 64)
      (ha : ¬ Component.Covers (.mem (stackPtr v + BitVec.ofNat 64 (24 + message.size % 64)) 1) a) :
      u2.external[a]? = u1.external[a]? := by
    apply he2.agrees.byte
    intro c hc hcov
    simp only [Padding.effect, Effect.components, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, Write.component, Operand.component,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hcov.elim
    rw [h15₁, hsp1, hmarker_addr] at hcov
    exact ha hcov
  have hcallByte (a : BitVec 64)
      (hd : ¬ Component.Covers (.mem (stackPtr v + BitVec.ofNat 64 (message.size % 64 + 25))
        (63 - message.size % 64)) a)
      (hp : ∃ k < 280, a = stackPtr v + BitVec.ofNat 64 k) :
      t.external[a]? = u2.external[a]? := by
    apply ht.agrees.byte
    intro c hc hcov
    simp only [callSiteChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hcov.elim
    · rw [hDst, hdx, hsp2, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show 63 - message.size % 64 < 2^64 by omega)] at hcov
      exact hd hcov
    · obtain ⟨k, hk, rfl⟩ := hp
      obtain ⟨j, hj, he⟩ := hcov
      have hap := hs2.stackApartPush (offset := k) (len := 1) (by simp only [Kind.stackBytes]; omega)
      rw [hsp2] at hap
      exact hap 0 (by decide) j hj (by rw [BitVec.add_zero]; exact he)
  have hpos_apart (k : Nat) (hk : k < 280) (hne : k ≠ 24 + message.size % 64) :
      ¬ Component.Covers (.mem (stackPtr v + BitVec.ofNat 64 (24 + message.size % 64)) 1)
        (stackPtr v + BitVec.ofNat 64 k) := by
    have := covers_apart (base := stackPtr v) (a := 24 + message.size % 64) (len := 1) (b := k)
      (count := 1) (i := 0) (by rw [BitVec.add_zero])
      (by decide) (by omega) (by omega) (by omega)
    exact this
  have hdst_apart (k : Nat) (hk : k < message.size % 64 + 25 ∨ 88 ≤ k) (hk' : k < 280) :
      ¬ Component.Covers (.mem (stackPtr v + BitVec.ofNat 64 (message.size % 64 + 25))
        (63 - message.size % 64)) (stackPtr v + BitVec.ofNat 64 k) := by
    have := covers_apart (base := stackPtr v) (a := message.size % 64 + 25)
      (len := 63 - message.size % 64) (b := k) (count := 1) (i := 0)
      (by rw [BitVec.add_zero])
      (by decide) (by omega) (by omega) (by omega)
    exact this
  have hkeep (k : Nat) (hk : k < message.size % 64 + 24 ∨ 88 ≤ k) (hk' : k < 280) :
      t.external[stackPtr v + BitVec.ofNat 64 k]? = v.external[stackPtr v + BitVec.ofNat 64 k]? := by
    rw [hcallByte _ (hdst_apart k (by omega) hk') ⟨k, hk', rfl⟩,
      hpadByte _ (hpos_apart k hk' (by omega)), hm1]
  have hs3 (a j : Nat) : stackPtr v + BitVec.ofNat 64 a + BitVec.ofNat 64 j =
      stackPtr v + BitVec.ofNat 64 (a + j) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  have hpadded : Bytes t.external (stackPtr t + 24) 64 (fun i ↦ (firstBlock message)[i]!) := by
    rw [hspt]
    apply firstBlock_bytes message
    · intro i hi
      have htl := bytes_of_hasBytes hv.tail i (by rw [size_tailBytes]; exact hi)
      simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq] at htl
      change t.external[stackPtr v + BitVec.ofNat 64 24 + BitVec.ofNat 64 i]? = _
      change v.external[stackPtr v + BitVec.ofNat 64 24 + BitVec.ofNat 64 i]? = _ at htl
      rw [hs3] at htl ⊢
      rw [hkeep (24 + i) (by omega) (by omega)]
      exact htl
    · change t.external[stackPtr v + BitVec.ofNat 64 24 + BitVec.ofNat 64 (message.size % 64)]? = _
      rw [hs3, hcallByte _ (hdst_apart _ (by omega) (by omega)) ⟨_, by omega, rfl⟩]
      have hm := hw2.1
      have hr : ∀ i < 8 / 8, (u2.external[stackPtr v + BitVec.ofNat 64 (24 + message.size % 64) +
          BitVec.ofNat 64 i]?).isSome := by
        intro i hi
        have := (hs2.stackWritable (24 + message.size % 64) 1
          (by simp only [Kind.stackBytes]; omega)).mem i hi
        rwa [hsp2] at this
      have hb := Bytes.of_memLoad hr 0 (by decide)
      change memLoad u2.external _ 8 = _ at hm
      rw [hm, BitVec.add_zero] at hb
      rw [hb]
      rfl
    · intro i hlo hhi
      change t.external[stackPtr v + BitVec.ofNat 64 24 + BitVec.ofNat 64 i]? = _
      have hlen : i - (message.size % 64 + 1) < (MemoryRoutines.rdx.read u2).toNat := by
        rw [hdx, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show 63 - message.size % 64 < 2^64 by omega)]
        omega
      have hh := ht.fill (i - (message.size % 64 + 1)) hlen
      rw [hDst, hw2.2.2.1, hsp2, hs3, show message.size % 64 + 25 + (i - (message.size % 64 + 1)) =
        24 + i by omega] at hh
      rw [hs3, hh]
      rfl
  have hstate : (⟨(stackPtr t).toNat, 20⟩ : MemoryRegion).HasBytes t.external
      (absorbedStateBytes message) := by
    have hsrc := hv.state
    rw [← absorbedStateBytes_size message] at hsrc ⊢
    rw [hspt]
    apply hasBytes_of_copy _ hsrc
    intro i hi
    rw [absorbedStateBytes_size] at hi
    exact hkeep i (by omega) (by omega)
  have hreg (r : BitVec 5) (h1 : Component.reg r ∉ (Prefix.effect v).components)
      (h2 : Component.reg r ∉ (Padding.effect u1).components)
      (h3 : Component.reg r ∉ callSiteChanges u2) :
      (Operand.reg r : Operand 64).read t = (Operand.reg r : Operand 64).read u1 :=
    (ht.agrees.read h3).trans (he2.agrees.read h2)
  have hag1 : AgreesExcept (Kind.digestCopy.changes s) v u1 := by
    rw [← Kind.changes_eq_of_rsp _ hv.rsp (by decide)]
    apply agrees_changes he1.agrees
    · intro c hc _
      simp only [Prefix.effect, Effect.components, List.map_cons, List.map_nil,
        List.cons_append, List.nil_append, Write.component, Operand.component,
        List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      all_goals simp [Kind.changes, Kind.workRegisters]
    · intro x c hc hcov
      simp only [Prefix.effect, Effect.components, List.map_cons, List.map_nil,
        List.cons_append, List.nil_append, Write.component, Operand.component,
        List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      all_goals exact hcov.elim
  have hag2 : AgreesExcept (Kind.digestCopy.changes s) u1 u2 := by
    rw [← Kind.changes_eq_of_rsp _ (hsp1.trans hv.rsp) (by decide)]
    apply agrees_changes he2.agrees
    · intro c hc hm
      simp only [Padding.effect, Effect.components, List.map_cons, List.map_nil,
        List.cons_append, List.nil_append, Write.component, Operand.component,
        List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp_all [Component.isMem, Kind.changes, Kind.workRegisters]
    · intro x c hc hcov
      simp only [Padding.effect, Effect.components, List.map_cons, List.map_nil,
        List.cons_append, List.nil_append, Write.component, Operand.component,
        List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
      all_goals try exact hcov.elim
      rw [h15₁, hsp1, hmarker_addr] at hcov
      rw [hsp1]
      exact hv.storage.localWithin (offset := 24 + message.size % 64) (len := 1)
        (by simp only [Kind.stackBytes]; omega) hcov
  have hag3 : AgreesExcept (Kind.digestCopy.changes s) u2 t := by
    rw [← Kind.changes_eq_of_rsp _ (hsp2.trans hv.rsp) (by decide)]
    apply agrees_changes ht.agrees
    · intro c hc hm
      simp only [callSiteChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp_all [Component.isMem, Kind.changes, Kind.workRegisters]
    · intro x c hc hcov
      simp only [callSiteChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals try exact hcov.elim
      · rw [hDst, hdx, BitVec.toNat_ofNat,
          Nat.mod_eq_of_lt (show 63 - message.size % 64 < 2^64 by omega)] at hcov
        exact hs2.localWithin (offset := message.size % 64 + 25)
          (len := 63 - message.size % 64) (by simp only [Kind.stackBytes]; omega) hcov
      · obtain ⟨j, hj, rfl⟩ := hcov
        refine ⟨336 + j, by simp only [Kind.stackBytes, Kind.frameBytes]; omega, ?_⟩
        simp only [pushAddr, BitVec.sub_eq_add_neg, BitVec.add_assoc]
        congr 1
        rw [BitVec.ofNat_add, ← BitVec.add_assoc]
        congr 1
  have hag : AgreesExcept (Kind.digestCopy.changes s) s t :=
    (((hv.agrees.trans hag1).trans hag2).trans hag3).mono (by simp)
  have hnot (r : BitVec 5) (hr : r = 12 ∨ r = 14 ∨ r = 15) :
      Component.reg r ∉ callSiteChanges u2 := by
    rcases hr with rfl | rfl | rfl <;> simp [callSiteChanges]
  have hnot2 (r : BitVec 5) (hr : r = 12 ∨ r = 14 ∨ r = 15) :
      Component.reg r ∉ (Padding.effect u1).components := by
    rcases hr with rfl | rfl | rfl <;> simp [Padding.effect, Effect.components]
  obtain ⟨callFuel, hcall⟩ := ht.advances
  obtain ⟨n0, h0⟩ := hv.advances
  refine ⟨t, ⟨⟨n0 + (n1 + (n2 + callFuel)), h0.trans (h1.trans (h2.trans hcall))⟩, ht.ready,
    ht.code, ht.rip, hs2.of_agrees ht.agrees ht.rsp, ?_, hspt.trans hv.rsp, ?_, ?_, ?_,
    hpadded, hstate, hag⟩⟩
  · exact (((hag1.trans hag2).trans hag3).directionFlagClear
      (by simp [Kind.changes, Kind.workRegisters, Kind.localChanges]) ⟨hv.df⟩).df
  · rw [(ht.agrees.read (hnot 15 (by decide))).trans (he2.agrees.read (hnot2 15 (by decide)))]
    exact h15₁
  · rw [(ht.agrees.read (hnot 14 (by decide))).trans (he2.agrees.read (hnot2 14 (by decide)))]
    exact h14₁
  · rw [(ht.agrees.read (hnot 12 (by decide))).trans (he2.agrees.read (hnot2 12 (by decide)))]
    exact h12₁

end Sha1.Proofs.Buffered.Finalize.Digest
