import P256.Proofs.Verifying.Message.Hash.Finalize.Compress.Interface
import P256.Proofs.Verifying.Message.Frame
import P256.Proofs.HMAC.Finalize.Copy

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Hash.Finalize.Compress

open P256.Spec P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

abbrev workRegion (initial : RamState) : MemoryRegion :=
  ScalarFrame.Work.region initial 9992 792

theorem work_contains [Bindings] {initial : RamState} {boundary : ReturnBoundary}
    {message : ByteArray} (pre : Message.Pre initial boundary message)
    {offset len : Nat} {a : BitVec 64} (bound : offset + len ≤ 384)
    (covered : (Component.mem (frameBase initial + BitVec.ofNat 64 offset) len).Covers a) :
    (workRegion initial).Contains a.toNat := by
  have address : frameBase initial + BitVec.ofNat 64 offset =
      stackPtr initial - BitVec.ofNat 64 (1176 - offset) := by
    rw [← BitVec.ofNat_sub_ofNat_of_le 1176 offset (by omega) (by omega)]
    simp only [frameBase, BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.neg_neg,
      BitVec.add_assoc, BitVec.ofNat_eq_ofNat]
  rw [address] at covered
  exact ScalarFrame.Work.contains pre.toCalleePre (by omega) (by omega) covered

theorem work_widen [Bindings] {initial : RamState} {boundary : ReturnBoundary}
    {message : ByteArray} (pre : Message.Pre initial boundary message)
    {a : BitVec 64} (inside : (workRegion initial).Contains a.toNat) :
    (ScalarFrame.workRegion initial 9992).Contains a.toNat := by
  have bounds := stack_bounds pre.stack
  change (stackPtr initial).toNat - 9992 ≤ a.toNat ∧
    a.toNat < (stackPtr initial).toNat - 9992 + (9992 - 792) at inside
  change (stackPtr initial).toNat - 9992 ≤ a.toNat ∧
    a.toNat < (stackPtr initial).toNat - 9992 + (9992 - 48)
  constructor <;> omega

theorem work_read [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
    {message : ByteArray} (pre : Message.Pre initial boundary message)
    (memory : MemoryWriteFrame s t #v[workRegion initial])
    {offset : Nat} (bound : offset ≤ 792) :
    memLoad t.external (stackPtr initial - BitVec.ofNat 64 offset) 64 =
      memLoad s.external (stackPtr initial - BitVec.ofNat 64 offset) 64 := by
  apply ScalarFrame.Work.read pre.toCalleePre (savedBytes := 792) (by decide) _ bound
    (by omega)
  intro a outside
  apply memory a
  intro region member inside
  have eq : region = workRegion initial := by simpa using member
  subst region
  exact outside _ (by simp [workRegion]) inside

theorem live_after_registers [Bindings] {initial s t : RamState}
    {boundary : ReturnBoundary} {cs : List Component} {fuel : Nat}
    (input : Live initial s boundary) (run : Advances boundary fuel s t)
    (ready : ReadyToStep t) (agrees : AgreesExcept cs s t)
    (memory : ∀ c ∈ cs, ∀ a, ¬ c.Covers a) (sp : .reg 4 ∉ cs)
    (df : Component.df ∉ cs := by component_not_mem)
    (mxcsr : Component.mxcsr ∉ cs := by component_not_mem)
    (fcw : Component.fcw ∉ cs := by component_not_mem) : Live initial t boundary := by
  have unchanged := agrees.external memory
  refine ⟨input.toFrameState.after_registers ready agrees memory sp df mxcsr fcw, ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨fuel0, run0⟩ := input.execution
    exact ⟨fuel0 + fuel, run0.trans run⟩
  · simpa only [unchanged] using input.savedKey
  · simpa only [unchanged] using input.savedOutput
  · simpa only [unchanged] using input.savedSignature
  · intro a outside
    rw [unchanged]
    exact input.stackFrame a outside

theorem live_after_effect [Bindings] {initial s t : RamState}
    {boundary : ReturnBoundary} {message : ByteArray} {cs : List Component} {fuel : Nat}
    (pre : Message.Pre initial boundary message) (input : Live initial s boundary)
    (run : Advances boundary fuel s t) (ready : ReadyToStep t)
    (agrees : AgreesExcept cs s t) (writes : WritesWithin cs #v[workRegion initial])
    (sp : .reg 4 ∉ cs) (df : Component.df ∉ cs := by component_not_mem)
    (mxcsr : Component.mxcsr ∉ cs := by component_not_mem)
    (fcw : Component.fcw ∉ cs := by component_not_mem) : Live initial t boundary := by
  have memory := agrees.memoryWriteFrame writes
  have wide : WritesWithin cs #v[ScalarFrame.workRegion initial 9992] := by
    intro c hc a covered
    obtain ⟨region, member, inside⟩ := writes c hc a covered
    have eq : region = workRegion initial := by simpa using member
    subst region
    exact ⟨_, by simp, work_widen pre inside⟩
  refine ⟨input.toFrameState.after_effect pre.toCalleePre (by decide) ready agrees ?_ sp df mxcsr fcw,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro c hc a covered
    obtain ⟨region, member, inside⟩ := wide c hc a covered
    have eq : region = ScalarFrame.workRegion initial 9992 := by simpa using member
    subst region
    exact ⟨_, by simp, inside⟩
  · obtain ⟨fuel0, run0⟩ := input.execution
    exact ⟨fuel0 + fuel, run0.trans run⟩
  · have h := work_read pre memory (offset := 720) (by decide)
    have address : frameBase initial + 456 = stackPtr initial - 720 := by
      simp only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc]
      rfl
    rw [address]
    exact h.trans (by simpa only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc,
      BitVec.reduceNeg, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using input.savedKey)
  · have h := work_read pre memory (offset := 792) (by decide)
    have address : frameBase initial + 384 = stackPtr initial - 792 := by
      simp only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc]
      rfl
    rw [address]
    exact h.trans (by simpa only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc,
      BitVec.reduceNeg, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using input.savedOutput)
  · have h := work_read pre memory (offset := 712) (by decide)
    have address : frameBase initial + 464 = stackPtr initial - 712 := by
      simp only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc]
      rfl
    rw [address]
    exact h.trans (by simpa only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc,
      BitVec.reduceNeg, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using input.savedSignature)
  · exact memoryWriteFrame_trans input.stackFrame
      (work_frame_stack pre.toCalleePre (agrees.memoryWriteFrame wide))

theorem hashAt_after_registers [Bindings] {initial s t : RamState}
    {boundary : ReturnBoundary} {hash : Array UInt32} {cs : List Component} {fuel : Nat}
    (input : HashAt initial s boundary hash) (run : Advances boundary fuel s t)
    (ready : ReadyToStep t) (agrees : AgreesExcept cs s t)
    (memory : ∀ c ∈ cs, ∀ a, ¬ c.Covers a) (sp : .reg 4 ∉ cs) (rbx : .reg 3 ∉ cs)
    (df : Component.df ∉ cs := by component_not_mem)
    (mxcsr : Component.mxcsr ∉ cs := by component_not_mem)
    (fcw : Component.fcw ∉ cs := by component_not_mem) : HashAt initial t boundary hash := by
  refine ⟨live_after_registers input.toLive run ready agrees memory sp df mxcsr fcw,
    ?_, (agrees.read (n := 64) (r := 3) rbx).trans input.hashPointer⟩
  simpa only [SHA256.HashStateAt, agrees.external memory] using input.hashWords

theorem working_after_registers [Bindings] {initial s t : RamState}
    {boundary : ReturnBoundary} {message : ByteArray} {hash : Array UInt32}
    {cs : List Component} {fuel : Nat} (input : Working initial s boundary message hash)
    (run : Advances boundary fuel s t) (ready : ReadyToStep t) (agrees : AgreesExcept cs s t)
    (memory : ∀ c ∈ cs, ∀ a, ¬ c.Covers a)
    (sp : .reg 4 ∉ cs) (rbx : .reg 3 ∉ cs) (r12 : .reg 12 ∉ cs) (r15 : .reg 15 ∉ cs)
    (df : Component.df ∉ cs := by component_not_mem)
    (mxcsr : Component.mxcsr ∉ cs := by component_not_mem)
    (fcw : Component.fcw ∉ cs := by component_not_mem) :
    Working initial t boundary message hash := by
  exact ⟨hashAt_after_registers input.toHashAt run ready agrees memory sp rbx df mxcsr fcw,
    (agrees.read (n := 64) (r := 12) r12).trans input.blocks,
    (agrees.read (n := 64) (r := 15) r15).trans input.tailLength⟩

end P256.Proofs.Verifying.Message.Hash.Finalize.Compress
