import P256.Proofs.Signing.Wrapper.Hash.Finalize.Compress.Preserve
import P256.Proofs.HMAC.Key.Output.Bytes
import P256.Proofs.Program.CopyBytes

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Hash.Finalize.Compress.Blocks

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

 theorem stack_address {initial s : RamState} (rsp : stackPtr s = stackPtr initial - 520)
    (i : BitVec 64) : rspOf s + i = stackPtr initial - (520 - i) := by
  change stackPtr s + i = _
  rw [rsp]
  simp only [BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.neg_neg, BitVec.add_assoc]

 theorem stack_readable [Bindings] {initial start s : RamState} {secret message : ByteArray}
    (pre : HashEntry initial start secret message) (state : Frame initial start s)
    {offset len : Nat} (bound : offset ≤ 5112) (span : len ≤ offset + 8) :
    MemReadable s (stackPtr initial - BitVec.ofNat 64 offset) len :=
  readable_of_grow (stack_sub_readable (stack pre.context) bound span) state.allocated

 theorem stack_writable8 [Bindings] {initial start s : RamState} {secret message : ByteArray}
    (pre : HashEntry initial start secret message) (state : Frame initial start s)
    {offset : Nat} (bound : offset ≤ 5112) (aligned : offset % 8 = 0) :
    MemWritable s (stackPtr initial - BitVec.ofNat 64 offset) 8 :=
  writable_of_grow (stack_sub_writable8 (stack pre.context)
    (fun a ha hb => stack_avoids pre.context a ha (.inr hb)) bound aligned) state.allocated

 theorem stack_codeApart [Bindings] {initial start : RamState} {secret message : ByteArray}
    (pre : HashEntry initial start secret message)
    {offset len codeOffset codeLen : Nat} (bound : offset ≤ 5112) (span : len ≤ offset + 8)
    (codeBound : codeOffset + codeLen ≤ 118431) :
    RangeApart (stackPtr initial - BitVec.ofNat 64 offset) len
      (Extracted.textAddress + BitVec.ofNat 64 codeOffset) codeLen :=
  stack_buffer_code_apart (stack pre.context) (stack_avoids pre.context) bound span codeBound

 theorem agrees_of_footprint {s t : RamState} {small large : List Component}
    (h : AgreesExcept small s t)
    (hreg : ∀ c ∈ small, c.isMem = false → c ∈ large)
    (hmem : ∀ c ∈ small, ∀ a, c.Covers a → ∃ d ∈ large, d.Covers a) :
    AgreesExcept large s t := by
  refine ⟨?_, ?_, h.rest, h.grow⟩
  · intro c hc hm
    exact h.agree c (fun hs => hc (hreg c hs hm)) hm
  · intro a ha
    apply h.memory a
    intro c hc hcover
    obtain ⟨d, hd, hcover'⟩ := hmem c hc a hcover
    exact ha d hd hcover'

def Writes (initial : RamState) (components : List Component) : Prop :=
  ∀ c ∈ components, ∀ a, c.Covers a →
    (Component.mem (stackPtr initial - 456) 64).Covers a ∨
    (Component.mem (stackPtr initial - 520) 64).Covers a

theorem writes_mem {initial s : RamState} {offset len : Nat}
    (rsp : stackPtr s = stackPtr initial - 520)
    (bounds : 64 ≤ offset ∧ offset + len ≤ 128 ∨ 0 ≤ offset ∧ offset + len ≤ 64) :
    ∀ a, (Component.mem (rspOf s + BitVec.ofNat 64 offset) len).Covers a →
      (Component.mem (stackPtr initial - 456) 64).Covers a ∨
      (Component.mem (stackPtr initial - 520) 64).Covers a := by
  intro a ha
  obtain ⟨i, hi, rfl⟩ := ha
  change rspOf s = stackPtr initial - 520 at rsp
  rcases bounds with low | high
  · left
    refine ⟨offset-64+i, by omega, ?_⟩
    rw [rsp, BitVec.ofNat_add, ← BitVec.ofNat_sub_ofNat_of_le offset 64 (by omega) low.1]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rw [← BitVec.add_assoc (BitVec.ofNat 64 offset),
      BitVec.add_comm (BitVec.ofNat 64 offset) (-64#64),
      BitVec.add_assoc (-64#64), ← BitVec.add_assoc (-456)]
    rfl
  · right
    refine ⟨offset+i, by omega, ?_⟩
    rw [rsp, BitVec.ofNat_add, BitVec.add_assoc]


theorem kept_bytes {initial s t : RamState} {components : List Component} {offset len : Nat}
    (frame : AgreesExcept components s t) (writes : Writes initial components)
    (first : OffsetsApart (-456) 64 (-(BitVec.ofNat 64 offset)) len)
    (second : OffsetsApart (-520) 64 (-(BitVec.ofNat 64 offset)) len)
    (bound : 64 + len < 2^64) :
    ∀ i < len, t.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      s.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  intro i hi
  apply frame.byte
  intro c hc covers
  rcases writes c hc _ covers with ⟨j, hj, he⟩ | ⟨j, hj, he⟩
  · apply OffsetsApart.ne first (stackPtr initial) hj hi bound
    simpa only [BitVec.sub_eq_add_neg] using he.symm
  · apply OffsetsApart.ne second (stackPtr initial) hj hi bound
    simpa only [BitVec.sub_eq_add_neg] using he.symm

theorem preserve [Bindings] {initial start s t : RamState} {secret message : ByteArray} {hash : Array UInt32} {fuel : Nat} {components : List Component}
    (pre : HashEntry initial start secret message) (input : HashAt initial start s hash)
    (run : Advances (returnBoundary initial) fuel s t) (ready : ReadyToStep t)
    (frame : AgreesExcept components s t) (writes : Writes initial components)
    (sp : Component.reg 4 ∉ components) (r15 : Component.reg 15 ∉ components)
    (hdf : Component.df ∉ components := by component_not_mem) :
    HashAt initial start t hash := by
  refine ⟨live_after_effect pre input.toLive run ready frame ?_ sp hdf, ?_,
    (frame.read (n := 64) r15).trans input.hashPointer⟩
  · intro c hc a ha
    refine ⟨workRegion initial, by simp, ?_⟩
    rcases writes c hc a ha with lo | hi
    · exact Hash.work_contains pre.context (by decide) (by decide) lo
    · exact Hash.work_contains pre.context (by decide) (by decide) hi
  · apply input.hashWords.copy
    have kept := kept_bytes frame writes (offset := 392) (len := 32)
      (by unfold OffsetsApart; decide +kernel) (by unfold OffsetsApart; decide +kernel)
      (by decide)
    simpa only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc,
      BitVec.reduceNeg, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using kept

end P256.Proofs.Signing.Wrapper.Hash.Finalize.Compress.Blocks
