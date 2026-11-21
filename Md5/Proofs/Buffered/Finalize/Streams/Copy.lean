import Md5.Proofs.Buffered.Finalize.Geometry
import Md5.Proofs.Buffered.Finalize.Copy
import Md5.Proofs.MemoryRoutines.Movsq

namespace Md5.Proofs.Buffered.Finalize.Streams

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure CopyPre [Bindings] (kind : Kind) (offset src dst : Nat) (s : RamState) : Prop
    extends Storage kind s where
  ready : ReadyToStep s
  code : CodeIn Extracted.programImage s
  bytes : CodeIn (codeRange (Extracted.textAddress + BitVec.ofNat 64 offset)
    [0xf3, 0x48, 0xa5]) s
  df : DirectionFlagClear s.RFLAGS
  rip : s.RIP = Extracted.textAddress + BitVec.ofNat 64 offset
  source : rsi.read s = stackPtr s + BitVec.ofNat 64 src
  destination : rdi.read s = stackPtr s + BitVec.ofNat 64 dst
  count : rcx.read s = 11
  sourceBound : src + 88 ≤ kind.stackBytes
  destinationBound : dst + 88 ≤ kind.stackBytes
  destinationAligned : dst % 8 = 0
  disjoint : src + 88 ≤ dst ∨ dst + 88 ≤ src
  codeBound : offset + 3 < Extracted.textBytes.size

structure CopyPost [Bindings] (boundary : ReturnBoundary) (offset src dst : Nat)
    (s t : RamState) : Prop where
  advances : Advances boundary 11 s t
  ready : ReadyToStep t
  code : CodeIn Extracted.programImage t
  rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 (offset + 3)
  copy : ∀ i < 88, t.external[stackPtr s + BitVec.ofNat 64 dst + BitVec.ofNat 64 i]? =
    s.external[stackPtr s + BitVec.ofNat 64 src + BitVec.ofNat 64 i]?
  agrees : AgreesExcept
    [.reg 1, .reg 6, .reg 7, .mem (stackPtr s + BitVec.ofNat 64 dst) 88, .rip] s t

theorem CopyPost.rsp [Bindings] {boundary : ReturnBoundary} {offset src dst : Nat}
    {s t : RamState} (h : CopyPost boundary offset src dst s t) : stackPtr t = stackPtr s :=
  h.agrees.read (n := 64) (r := 4) (by simp)

theorem CopyPost.absorbed [Bindings] {boundary : ReturnBoundary} {offset src dst : Nat}
    {message : ByteArray} {s t : RamState} (h : CopyPost boundary offset src dst s t)
    (ha : Absorbed (stackPtr s + BitVec.ofNat 64 src) message s) :
    Absorbed (stackPtr t + BitVec.ofNat 64 dst) message t := by
  rw [h.rsp]
  exact absorbed_of_copy ha h.copy

theorem copy_context [bindings : Bindings] (hstride : UnitStringStride bindings)
    (boundary : ReturnBoundary) (hOutside : ¬ InProgram boundary.rip)
    {kind : Kind} {offset src dst : Nat} {s : RamState}
    (h : CopyPre kind offset src dst s) : ∃ t, CopyPost boundary offset src dst s t := by
  have h11 : (11 : BitVec 64).toNat = 11 := by decide +kernel
  have hs := h.toStorage.stackRange src 88 h.sourceBound
  have hd := h.toStorage.stackRange dst 88 h.destinationBound
  have hsaddr := h.toStorage.stackAddress (offset := src) (by have := h.sourceBound; omega)
  have hdaddr := h.toStorage.stackAddress (offset := dst) (by have := h.destinationBound; omega)
  have hpre : MemoryRoutines.Movsq.RepMovsqPre
      (Extracted.textAddress + BitVec.ofNat 64 offset) s := by
    refine ⟨h.rip, h.df, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [h.source, h.count, h11, Nat.reduceMul] using hs.readable.low
    · simpa only [h.destination, h.count, h11, Nat.reduceMul] using hd.readable.low
    · intro _
      rw [h.destination, hdaddr, Nat.add_mod, h.destinationAligned, Nat.add_zero, Nat.mod_mod]
      have hh := h.stackAligned
      omega
    · simpa only [h.source, h.count, h11, Nat.reduceMul] using hs.readable.mem
    · simpa only [h.destination, h.count, h11, Nat.reduceMul] using hd.readable.mem
    · simp only [h.source, h.destination, h.count, h11, Nat.reduceMul, hsaddr, hdaddr]
      have hh := h.disjoint
      rcases hh with hh | hh
      · left; omega
      · right; omega
    · simpa only [h.destination, h.count, h11, Nat.reduceMul] using hd.tables
    · simpa only [h.destination, h.count, h11, Nat.reduceMul] using
        h.toStorage.stackApart h.destinationBound (Nat.le_of_lt h.codeBound)
  let t := nextStates 11 s
  have hn : max (rcx.read s).toNat 1 = 11 := by rw [h.count]; rfl
  have hr := MemoryRoutines.Movsq.rep_movsq_done hstride _ 0x48
    (by unfold RexWPrefix; decide) s h.ready h.bytes hpre
  rw [hn] at hr
  have ha := MemoryRoutines.Movsq.rep_movsq_agrees hstride _ 0x48
    (by unfold RexWPrefix; decide) s h.ready h.bytes hpre
  rw [hn, h.destination, h.count] at ha
  have hrun := MemoryRoutines.Movsq.rep_movsq_advances hstride boundary _ 0x48
    (by unfold RexWPrefix; decide) s h.ready h.bytes hpre
    (Block.text_address_ne_return hOutside offset (by have := h.codeBound; omega))
    (by
      rw [add_ofNat_add_ofNat]
      exact Block.text_address_ne_return hOutside (offset + 3) h.codeBound)
  rw [hn] at hrun
  refine ⟨t, hrun, hr.ready, ?_, ?_, ?_, ha⟩
  · apply CodeIn.of_agreesExcept ha _ h.code
    intro x hx c hc hcover
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact hcover.elim
    obtain ⟨i, hi, he⟩ := hcover
    exact hd.code i hi ⟨x.2, he ▸ hx⟩
  · rw [hr.rip, h.rip]
    exact add_ofNat_add_ofNat _ _ 3
  · simpa only [h.source, h.destination, h.count, h11, Nat.reduceMul] using hr.copy

theorem CopyPost.sourceAbsorbed [Bindings] {boundary : ReturnBoundary}
    {kind : Kind} {offset src dst : Nat} {message : ByteArray} {s t : RamState}
    (h : CopyPost boundary offset src dst s t) (hp : CopyPre kind offset src dst s)
    (ha : Absorbed (stackPtr s + BitVec.ofNat 64 src) message s) :
    Absorbed (stackPtr t + BitVec.ofNat 64 src) message t := by
  rw [h.rsp]
  apply absorbed_of_copy ha
  intro i hi
  apply h.agrees.byte
  intro c hc hcover
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl
  all_goals try exact hcover.elim
  obtain ⟨j, hj, he⟩ := hcover
  have hbound : kind.stackBytes < 2^64 := by cases kind <;> decide
  exact RangeApart.offsets (stackPtr s)
    (by have := hp.sourceBound; omega) (by have := hp.destinationBound; omega)
    hp.disjoint i hi j hj he

end Md5.Proofs.Buffered.Finalize.Streams
