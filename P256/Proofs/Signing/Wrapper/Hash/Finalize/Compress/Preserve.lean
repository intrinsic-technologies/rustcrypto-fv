import P256.Proofs.Signing.Wrapper.Hash.Finalize.Compress.Interface
import P256.Proofs.Signing.Wrapper.Hash.Interface
import P256.Proofs.HMAC.Finalize.Copy

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Hash.Finalize.Compress

open P256.Spec P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

abbrev workRegion (initial : RamState) : MemoryRegion := Hash.workRegion initial

theorem work_contains [Bindings] {initial start : RamState} {secret message : ByteArray}
    (pre : HashEntry initial start secret message)
    {offset len : Nat} {a : BitVec 64} (bound : offset + len ≤ 280)
    (covered : (Component.mem (frameBase initial + BitVec.ofNat 64 offset) len).Covers a) :
    (workRegion initial).Contains a.toNat := by
  have address : frameBase initial + BitVec.ofNat 64 offset =
      stackPtr initial - BitVec.ofNat 64 (520 - offset) := by
    rw [← BitVec.ofNat_sub_ofNat_of_le 520 offset (by omega) (by omega)]
    simp only [frameBase, BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.neg_neg,
      BitVec.add_assoc, BitVec.ofNat_eq_ofNat]
  rw [address] at covered
  exact Hash.work_contains pre.context (by omega) (by omega) covered

theorem work_widen [Bindings] {initial start : RamState} {secret message : ByteArray}
    (pre : HashEntry initial start secret message)
    {a : BitVec 64} (inside : (workRegion initial).Contains a.toNat) :
    (Wrapper.workRegion initial).Contains a.toNat := Hash.work_widen pre.context inside

theorem work_read [Bindings] {initial start s t : RamState} {secret message : ByteArray}
    (pre : HashEntry initial start secret message)
    (memory : MemoryWriteFrame s t #v[workRegion initial])
    {offset : Nat} (bound : offset ≤ 240) :
    memLoad t.external (stackPtr initial - BitVec.ofNat 64 offset) 64 =
      memLoad s.external (stackPtr initial - BitVec.ofNat 64 offset) 64 := by
  have bounds := stack_bounds (stack pre.context)
  have low := stack_sub_toNat (stack pre.context) (offset := offset) (by omega)
  apply memLoad_congr
  intro i hi
  change (t.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?).getD 0 =
    (s.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?).getD 0
  rw [memory _]
  intro region hr hin
  have he : region = workRegion initial := by simpa using hr
  subst region
  change (stackPtr initial).toNat - 5112 ≤ _ ∧
    (stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat <
      (stackPtr initial).toNat - 5112 + (5112 - 240) at hin
  rw [BitVec.toNat_add, BitVec.toNat_ofNat, low] at hin
  have iBound : i < 8 := hi
  omega

theorem live_after_registers [Bindings] {initial start s t : RamState}
    {secret message : ByteArray} {cs : List Component} {fuel : Nat}
    (pre : HashEntry initial start secret message) (input : Live initial start s)
    (run : Advances (returnBoundary initial) fuel s t)
    (ready : ReadyToStep t) (agrees : AgreesExcept cs s t)
    (memory : ∀ c ∈ cs, ∀ a, ¬ c.Covers a) (sp : .reg 4 ∉ cs)
    (df : Component.df ∉ cs := by component_not_mem) : Live initial start t :=
  ⟨input.toFrame.after_registers pre.context run ready agrees memory sp df⟩

theorem live_after_effect [Bindings] {initial start s t : RamState}
    {secret message : ByteArray} {cs : List Component} {fuel : Nat}
    (pre : HashEntry initial start secret message) (input : Live initial start s)
    (run : Advances (returnBoundary initial) fuel s t) (ready : ReadyToStep t)
    (agrees : AgreesExcept cs s t) (writes : WritesWithin cs #v[workRegion initial])
    (sp : .reg 4 ∉ cs) (df : Component.df ∉ cs := by component_not_mem) :
    Live initial start t :=
  ⟨input.toFrame.after_effect pre.context run ready agrees writes
    ((agrees.read (n := 64) sp).trans input.rsp) df⟩

theorem hashAt_after_registers [Bindings] {initial start s t : RamState}
    {secret message : ByteArray} {hash : Array UInt32} {cs : List Component} {fuel : Nat}
    (pre : HashEntry initial start secret message) (input : HashAt initial start s hash)
    (run : Advances (returnBoundary initial) fuel s t)
    (ready : ReadyToStep t) (agrees : AgreesExcept cs s t)
    (memory : ∀ c ∈ cs, ∀ a, ¬ c.Covers a) (sp : .reg 4 ∉ cs) (r15 : .reg 15 ∉ cs)
    (df : Component.df ∉ cs := by component_not_mem) : HashAt initial start t hash := by
  refine ⟨live_after_registers pre input.toLive run ready agrees memory sp df,
    ?_, (agrees.read (n := 64) (r := 15) r15).trans input.hashPointer⟩
  simpa only [SHA256.HashStateAt, agrees.external memory] using input.hashWords

theorem working_after_registers [Bindings] {initial start s t : RamState}
    {secret message : ByteArray} {hash : Array UInt32}
    {cs : List Component} {fuel : Nat} (pre : HashEntry initial start secret message)
    (input : Working initial start s message hash)
    (run : Advances (returnBoundary initial) fuel s t) (ready : ReadyToStep t)
    (agrees : AgreesExcept cs s t) (memory : ∀ c ∈ cs, ∀ a, ¬ c.Covers a)
    (sp : .reg 4 ∉ cs) (r15 : .reg 15 ∉ cs) (r14 : .reg 14 ∉ cs) (rbx : .reg 3 ∉ cs)
    (df : Component.df ∉ cs := by component_not_mem) :
    Working initial start t message hash := by
  exact ⟨hashAt_after_registers pre input.toHashAt run ready agrees memory sp r15 df,
    (agrees.read (n := 64) (r := 14) r14).trans input.blocks,
    (agrees.read (n := 64) (r := 3) rbx).trans input.tailLength⟩

end P256.Proofs.Signing.Wrapper.Hash.Finalize.Compress
