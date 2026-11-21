import P256.Proofs.Nonce.Fill.Tail.State
import P256.Proofs.Nonce.Fill.Work
import P256.Proofs.Nonce.Fill.Memory
import X86Proofs.Program.ReadWrite.Bytes
import X86Proofs.Program.Compose

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill.Tail.Compare

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Signing.Search
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)

def WordWrites (base : BitVec 64) (offsets : List Nat) (cs : List Component) : Prop :=
  ∀ c ∈ cs, ∀ address, c.Covers address →
    ∃ off ∈ offsets, ∃ i < 8, address = base + BitVec.ofNat 64 off + BitVec.ofNat 64 i

theorem WordWrites.nat256 {s t : RamState} {base : BitVec 64} {offsets : List Nat}
    {cs : List Component} {offset value : Nat} (writes : WordWrites base offsets cs)
    (agrees : AgreesExcept cs s t) (bounds : ∀ off ∈ offsets, off + 8 ≤ 2^64)
    (hoff : offset + 32 ≤ 2^64)
    (apart : ∀ off ∈ offsets, off + 8 ≤ offset ∨ offset + 32 ≤ off)
    (input : Nat256At s (base + BitVec.ofNat 64 offset) value) :
    Nat256At t (base + BitVec.ofNat 64 offset) value := by
  refine ⟨input.1, fun i hi => ?_⟩
  rw [agrees.byte ?_]
  · exact input.2 i hi
  · intro c hc cover
    obtain ⟨off, ho, j, hj, he⟩ := writes c hc _ cover
    exact RangeApart.offsets base (bounds off ho) hoff (apart off ho) j hj i hi he.symm

theorem WordWrites.load {s t : RamState} {base : BitVec 64} {offsets : List Nat}
    {cs : List Component} {offset n : Nat} (writes : WordWrites base offsets cs)
    (agrees : AgreesExcept cs s t) (bounds : ∀ off ∈ offsets, off + 8 ≤ 2^64)
    (hoff : offset + n / 8 ≤ 2^64)
    (apart : ∀ off ∈ offsets, off + 8 ≤ offset ∨ offset + n / 8 ≤ off) :
    memLoad t.external (base + BitVec.ofNat 64 offset) n =
      memLoad s.external (base + BitVec.ofNat 64 offset) n := by
  apply memLoad_congr
  intro i hi
  apply congrArg (fun byte : Option UInt8 => byte.getD 0)
  apply agrees.byte
  intro c hc cover
  obtain ⟨off, ho, j, hj, he⟩ := writes c hc _ cover
  exact RangeApart.offsets base (bounds off ho) hoff (apart off ho) j hj i hi he.symm

def ScratchOffset (off : Nat) : Prop :=
  (8 ≤ off ∧ off + 8 ≤ 40) ∨ (72 ≤ off ∧ off + 8 ≤ 136) ∨
    (152 ≤ off ∧ off + 8 ≤ 184)

theorem context_after_stack [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} {original state : Nonce.State} {cs : List Component}
    {offsets : List Nat} (pre : Pre initial boundary orderAddress original)
    (input : Context initial s orderAddress state) (ready : ReadyToStep t)
    (agrees : AgreesExcept cs s t) (writes : WordWrites (frameBase initial) offsets cs)
    (bounds : ∀ off ∈ offsets, ScratchOffset off)
    (rsp : .reg 4 ∉ cs) (r13 : .reg 13 ∉ cs) (r15 : .reg 15 ∉ cs)
    (hdf : Component.df ∉ cs := by component_not_mem)
    (hmxcsr : Component.mxcsr ∉ cs := by component_not_mem)
    (hfcw : Component.fcw ∉ cs := by component_not_mem) :
    Context initial t orderAddress state := by
  have small (off : Nat) (ho : off ∈ offsets) : off + 8 ≤ 184 := by
    have := bounds off ho
    unfold ScratchOffset at this
    omega
  have within : WritesWithin cs #v[ScalarFrame.workRegion initial 2096] := by
    intro c hc a ha
    obtain ⟨off, ho, i, hi, rfl⟩ := writes c hc a ha
    refine ⟨ScalarFrame.workRegion initial 2096, by simp, ?_⟩
    have h := small off ho
    rw [frameBase_add initial (by omega)]
    apply ScalarFrame.work_contains pre.toCalleePre (offset := 232 - off) (len := 8)
      (by omega) (by omega)
    exact ⟨i, hi, rfl⟩
  have memory := agrees.memoryWriteFrame within
  have frame := input.toFrame.after_effect pre ready agrees
    (fun c hc a ha => by
      obtain ⟨region, hr, hin⟩ := within c hc a ha
      have eq : region = ScalarFrame.workRegion initial 2096 := by simpa using hr
      subst region
      exact ⟨_, by simp [workRegions], hin⟩) rsp hdf hmxcsr hfcw
  have load (offset n : Nat) (hoff : offset + n / 8 ≤ 2^64)
      (apart : ∀ off ∈ offsets, off + 8 ≤ offset ∨ offset + n / 8 ≤ off) :
      memLoad t.external (frameBase initial + BitVec.ofNat 64 offset) n =
        memLoad s.external (frameBase initial + BitVec.ofNat 64 offset) n :=
    writes.load agrees (fun off ho => by have := small off ho; omega) hoff apart
  have apart (offset n : Nat) (h : offset = 40 ∨ offset = 48 ∨ offset = 56 ∨
      offset = 64 ∨ offset = 136 ∨ offset = 144) (hn : n / 8 ≤ 8) :
      ∀ off ∈ offsets, off + 8 ≤ offset ∨ offset + n / 8 ≤ off := by
    intro off ho
    have hb := bounds off ho
    unfold ScratchOffset at hb
    omega
  have slots : Slots initial t := ⟨
    (load 40 64 (by decide) (apart 40 64 (by omega) (by decide))).trans input.outputSlot,
    (load 48 64 (by decide) (apart 48 64 (by omega) (by decide))).trans input.lengthSlot,
    (load 56 32 (by decide) (apart 56 32 (by omega) (by decide))).trans input.bitsSlot,
    (load 64 64 (by decide) (apart 64 64 (by omega) (by decide))).trans input.statePointerSlot,
    (load 136 64 (by decide) (apart 136 64 (by omega) (by decide))).trans input.valuePointerSlot,
    (load 144 64 (by decide) (apart 144 64 (by omega) (by decide))).trans input.generatorPointerSlot⟩
  have generator := input.generator.of_frame pre.outputBounded pre.orderBounded memory
    (by
      intro region hr
      have eq : region = ScalarFrame.workRegion initial 2096 := by simpa using hr
      subst region
      intro a ha hin
      exact pre.separation 1 2 (by decide) a ha (work_substack pre hin))
    (by
      intro region hr
      have eq : region = ScalarFrame.workRegion initial 2096 := by simpa using hr
      subst region
      intro a ha hin
      exact pre.orderDisjoint _ (by simp) a ha (work_substack pre hin))
  exact ⟨frame, slots, (agrees.read (n := 64) (r := 13) r13).trans input.r13,
    (agrees.read (n := 64) (r := 15) r15).trans input.r15, generator⟩

theorem after_stack [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
    {orderAddress : BitVec 64} {original state : Nonce.State} {cs : List Component}
    {offsets : List Nat} (pre : Pre initial boundary orderAddress original)
    (input : Compared initial s orderAddress state) (ready : ReadyToStep t)
    (agrees : AgreesExcept cs s t) (writes : WordWrites (frameBase initial) offsets cs)
    (bounds : ∀ off ∈ offsets, 8 ≤ off ∧ off + 8 ≤ 40)
    (rsp : .reg 4 ∉ cs) (r13 : .reg 13 ∉ cs) (r15 : .reg 15 ∉ cs)
    (hdf : Component.df ∉ cs := by component_not_mem)
    (hmxcsr : Component.mxcsr ∉ cs := by component_not_mem)
    (hfcw : Component.fcw ∉ cs := by component_not_mem) :
    Compared initial t orderAddress state := by
  refine ⟨context_after_stack pre input.toContext ready agrees writes
    (fun off ho => Or.inl (bounds off ho)) rsp r13 r15 hdf hmxcsr hfcw, ?_⟩
  exact writes.nat256 (offset := 72) agrees (fun off ho => by have := bounds off ho; omega)
    (by decide) (fun off ho => by have := bounds off ho; omega) input.integer

end P256.Proofs.Nonce.Fill.Tail.Compare

namespace P256.Proofs.Nonce.Fill.Tail

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)

theorem Compared.after_registers [Bindings] {initial s t : RamState}
    {orderAddress : BitVec 64} {state : Nonce.State} {components : List Component}
    (input : Compared initial s orderAddress state) (ready : ReadyToStep t)
    (agrees : AgreesExcept components s t)
    (noMemory : ∀ c ∈ components, ∀ a, ¬ c.Covers a)
    (sp : .reg 4 ∉ components) (r13 : .reg 13 ∉ components) (r15 : .reg 15 ∉ components)
    (hdf : Component.df ∉ components := by component_not_mem)
    (hmxcsr : Component.mxcsr ∉ components := by component_not_mem)
    (hfcw : Component.fcw ∉ components := by component_not_mem) :
    Compared initial t orderAddress state := by
  refine ⟨input.toContext.after_registers ready agrees noMemory sp r13 r15 hdf hmxcsr hfcw, ?_⟩
  simpa only [Nat256At, agrees.external noMemory] using input.integer

end P256.Proofs.Nonce.Fill.Tail
