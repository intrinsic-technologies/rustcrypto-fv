import Sha3.Proofs.Update.Layout

namespace Sha3.Proofs.Update

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

theorem SavedFrame.of_memory_eq {initial s t : RamState}
    (h : SavedFrame initial s)
    (hsaved : ∀ (i : Fin 6) j, j < 8 →
      t.external[frameBase initial + BitVec.ofNat 64 (8 + 8 * i.val) +
        BitVec.ofNat 64 j]? =
      s.external[frameBase initial + BitVec.ofNat 64 (8 + 8 * i.val) +
        BitVec.ofNat 64 j]?)
    (hreturn : ∀ j, j < 8 →
      t.external[initial.regValue .rsp + BitVec.ofNat 64 j]? =
        s.external[initial.regValue .rsp + BitVec.ofNat 64 j]?) : SavedFrame initial t := by
  constructor
  · intro i
    refine Eq.trans ?_ (h.saved i)
    apply memLoad_congr
    intro j hj
    exact congrArg (fun x : Option UInt8 ↦ x.getD 0) (hsaved i j hj)
  · refine Eq.trans ?_ h.returnSlot
    apply memLoad_congr
    intro j hj
    exact congrArg (fun x : Option UInt8 ↦ x.getD 0) (hreturn j hj)

theorem SavedFrame.of_memoryWriteFrame {initial s t : RamState}
    {regions : Vector MemoryRegion n} (h : SavedFrame initial s)
    (hframe : MemoryWriteFrame s t regions)
    (hsaved : ∀ region ∈ regions, ∀ (i : Fin 6) j, j < 8 →
      ¬ region.Contains (frameBase initial + BitVec.ofNat 64 (8 + 8 * i.val) +
        BitVec.ofNat 64 j).toNat)
    (hreturn : ∀ region ∈ regions, ∀ j, j < 8 →
      ¬ region.Contains (initial.regValue .rsp + BitVec.ofNat 64 j).toNat) :
    SavedFrame initial t :=
  h.of_memory_eq (fun i j hj ↦ hframe _ (fun region hr ↦ hsaved region hr i j hj))
    (fun j hj ↦ hframe _ (fun region hr ↦ hreturn region hr j hj))

theorem SavedFrame.of_agreesExcept {initial s t : RamState} {components : List Component}
    (h : SavedFrame initial s) (hframe : AgreesExcept components s t)
    (hsaved : ∀ c ∈ components, ∀ (i : Fin 6) j, j < 8 →
      ¬ c.Covers (frameBase initial + BitVec.ofNat 64 (8 + 8 * i.val) + BitVec.ofNat 64 j))
    (hreturn : ∀ c ∈ components, ∀ j, j < 8 →
      ¬ c.Covers (initial.regValue .rsp + BitVec.ofNat 64 j)) : SavedFrame initial t :=
  h.of_memory_eq (fun i j hj ↦ hframe.memory _ (fun c hc ↦ hsaved c hc i j hj))
    (fun j hj ↦ hframe.memory _ (fun c hc ↦ hreturn c hc j hj))

theorem frameBase_add_56 (initial : RamState) :
    frameBase initial + 56 = initial.regValue .rsp := BitVec.sub_add_cancel _ _

theorem stackBase_add_272 (initial : RamState) :
    stackBase initial + 272 = frameBase initial := by
  simp only [stackBase, frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc]
  exact congrArg (initial.regValue .rsp + ·) (by decide +kernel)

theorem stackBase_add_328 (initial : RamState) :
    stackBase initial + 328 = initial.regValue .rsp := BitVec.sub_add_cancel _ _

theorem BodyInvariant.of_agreesExcept [Bindings]
    {v : Variant} {initial s t : RamState} {bytes : ByteArray} {state : Incremental.State}
    {components : List Component} (hc : CallContext v initial bytes state)
    (h : BodyInvariant initial s) (hr : ReadyToStep t)
    (ha : AgreesExcept components s t)
    (hw : WritesWithin components (writeRegions initial))
    (hsp : Component.reg 4 ∉ components)
    (hsaved : SavedFrame initial t) (hcs : components.all scalarClobber = true := by first | rfl | decide) : BodyInvariant initial t := by
  have hm := ha.memoryWriteFrame hw
  refine ⟨hr, ?_, (ha.read (n := 64) hsp).trans h.stack,
    hsaved, memoryWriteFrame_trans h.memory hm,
    fun address halloc ↦ ha.grow address (h.grows address halloc), (ha.scalarFrame_eq hcs).trans h.rest⟩
  apply programLoaded_of_memoryWriteFrame hm _ h.loaded
  intro region hregion address haddress hprogram
  exact hc.avoids region hregion address haddress (.inl hprogram)

def StateWrites (initial : RamState) (components : List Component) : Prop :=
  ∀ c ∈ components, ∀ address, c.Covers address →
    ∃ i < 201, address = initial.regValue .rsi + BitVec.ofNat 64 i

theorem StateWrites.writesWithin [Bindings] {v : Variant} {initial : RamState}
    {bytes : ByteArray} {state : Incremental.State} {components : List Component}
    (hc : CallContext v initial bytes state) (hw : StateWrites initial components) :
    WritesWithin components (writeRegions initial) := by
  intro c hcm address hcover
  obtain ⟨i, hi, rfl⟩ := hw c hcm address hcover
  refine ⟨stateRegion initial, by simp [writeRegions], ?_⟩
  have hl := hc.stateRead.low
  simp only [stateRegion, MemoryRegion.Contains, BitVec.toNat_add, BitVec.toNat_ofNat]
  constructor <;> omega

theorem SavedFrame.of_stateWrites [Bindings] {v : Variant} {initial s t : RamState}
    {bytes : ByteArray} {state : Incremental.State} {components : List Component}
    (hc : CallContext v initial bytes state) (h : SavedFrame initial s)
    (ha : AgreesExcept components s t) (hw : StateWrites initial components) :
    SavedFrame initial t := by
  apply h.of_agreesExcept ha
  · intro c hcm i j hj hcover
    obtain ⟨k, hk, he⟩ := hw c hcm _ hcover
    apply hc.stateStack k hk (280 + 8 * i.val + j) (by have := i.isLt; omega)
    have heq : stackBase initial + BitVec.ofNat 64 (280 + 8 * i.val + j) =
        frameBase initial + BitVec.ofNat 64 (8 + 8 * i.val) + BitVec.ofNat 64 j := by
      have hbase : stackBase initial + BitVec.ofNat 64 280 =
          frameBase initial + BitVec.ofNat 64 8 := by
        simp only [stackBase, frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc]
        exact congrArg (initial.regValue .rsp + ·) (by decide +kernel)
      simpa only [BitVec.ofNat_add, BitVec.add_assoc] using
        congrArg (fun x ↦ x + BitVec.ofNat 64 (8 * i.val) + BitVec.ofNat 64 j) hbase
    rw [heq]
    exact he.symm
  · intro c hcm j hj hcover
    obtain ⟨k, hk, he⟩ := hw c hcm _ hcover
    apply hc.stateStack k hk (328 + j) (by omega)
    have heq : stackBase initial + BitVec.ofNat 64 (328 + j) =
        initial.regValue .rsp + BitVec.ofNat 64 j := by
      have hbase : stackBase initial + BitVec.ofNat 64 328 = initial.regValue .rsp :=
        BitVec.sub_add_cancel _ _
      simpa only [BitVec.ofNat_add, BitVec.add_assoc] using
        congrArg (· + BitVec.ofNat 64 j) hbase
    rw [heq]
    exact he.symm

theorem BodyInvariant.of_stateWrites [Bindings]
    {v : Variant} {initial s t : RamState} {bytes : ByteArray} {state : Incremental.State}
    {components : List Component} (hc : CallContext v initial bytes state)
    (h : BodyInvariant initial s) (hr : ReadyToStep t)
    (ha : AgreesExcept components s t) (hw : StateWrites initial components)
    (hsp : Component.reg 4 ∉ components)
    (hcs : components.all scalarClobber = true := by first | rfl | decide) :
    BodyInvariant initial t :=
  h.of_agreesExcept hc hr ha (hw.writesWithin hc) hsp
    (h.saved.of_stateWrites hc ha hw) hcs

theorem BodyInvariant.readable [Bindings] {initial s : RamState}
    (h : BodyInvariant initial s) {address : BitVec 64} {count : Nat}
    (hr : MemReadable initial address count) : MemReadable s address count :=
  ⟨hr.low, fun i hi ↦ h.grows _ (hr.mem i hi)⟩

theorem StateAt.of_bytes_eq {pointer : BitVec 64} {state : Incremental.State}
    {s t : RamState} (h : StateAt pointer state s)
    (he : ∀ i, i < 201 → t.external[pointer + BitVec.ofNat 64 i]? =
      s.external[pointer + BitVec.ofNat 64 i]?) : StateAt pointer state t := by
  constructor
  · refine Eq.trans ?_ h.lanes
    funext i
    apply memLoad_congr
    intro j hj
    change (t.external[pointer + BitVec.ofNat 64 (8 * i.val) + BitVec.ofNat 64 j]?).getD 0 =
      (s.external[pointer + BitVec.ofNat 64 (8 * i.val) + BitVec.ofNat 64 j]?).getD 0
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, he (8 * i.val + j) (by have := i.isLt; omega)]
  · refine Eq.trans ?_ h.cursor
    unfold Update.cursor
    congr 1
    apply memLoad_congr
    intro j hj
    have hj0 : j = 0 := by omega
    subst j
    simpa only [BitVec.add_zero, BitVec.ofNat_eq_ofNat, memByte, PhysicalMemory.read] using
      congrArg (fun x : Option UInt8 ↦ x.getD 0) (he 200 (by decide))


theorem frameSlot_contains [Bindings] {v : Variant} {initial : RamState}
    {bytes : ByteArray} {state : Incremental.State} (hc : CallContext v initial bytes state)
    {i : Nat} (hi : i < 8) :
    (⟨(stackBase initial).toNat, stackBytes⟩ : MemoryRegion).Contains
      (frameBase initial + BitVec.ofNat 64 i).toNat := by
  have hu := hc.stack.2.2.1
  have hf : (frameBase initial).toNat = (initial.regValue .rsp).toNat - 56 :=
    stack_sub_toNat (offset := 56) hu (by decide)
  have hs : (stackBase initial).toNat = (initial.regValue .rsp).toNat - 328 :=
    stack_sub_toNat (offset := 328) hu (by decide)
  have hl := stack_sub_low hc.stack (offset := 56) (by decide)
  change (frameBase initial).toNat + 56 < 2 ^ 32 at hl
  change 328 ≤ (initial.regValue .rsp).toNat at hu
  simp only [MemoryRegion.Contains, stackBytes, BitVec.toNat_add,
    BitVec.toNat_ofNat, hf, hs] at ⊢
  omega

theorem BodyInvariant.cursorSlot_readable [Bindings] {v : Variant} {initial s : RamState}
    {bytes : ByteArray} {state : Incremental.State} (hc : CallContext v initial bytes state)
    (h : BodyInvariant initial s) : MemReadable s (s.regValue .rsp) 8 := by
  rw [h.stack]
  refine ⟨?_, fun i hi ↦ h.grows _ ?_⟩
  · have hl := stack_sub_low hc.stack (show 56 ≤ 328 by decide)
    change _ < 2 ^ 32 at hl
    change (initial.regValue .rsp - 56#64).toNat + 8 ≤ 2 ^ 32
    omega
  · exact Option.isSome_iff_exists.mpr
      (stack_sub_allocated (offset := 56) hc.stack (by decide) (by omega))

theorem BodyInvariant.of_cursorSlotWrites [Bindings] {v : Variant} {initial s t : RamState}
    {bytes : ByteArray} {state : Incremental.State} {components : List Component}
    (hc : CallContext v initial bytes state) (h : BodyInvariant initial s)
    (hr : ReadyToStep t) (ha : AgreesExcept components s t)
    (hw : ∀ c ∈ components, ∀ address, c.Covers address →
      ∃ i < 8, address = frameBase initial + BitVec.ofNat 64 i)
    (hsp : Component.reg 4 ∉ components)
    (hcs : components.all scalarClobber = true := by first | rfl | decide) :
    BodyInvariant initial t ∧
      Permutation.memoryLanes (initial.regValue .rsi) t =
        Permutation.memoryLanes (initial.regValue .rsi) s := by
  have hsaved : SavedFrame initial t := by
    apply h.saved.of_agreesExcept ha
    · intro c hcm i j hj hcover
      obtain ⟨k, hk, he⟩ := hw c hcm _ hcover
      rw [BitVec.add_assoc, ← BitVec.ofNat_add] at he
      have hn := congrArg BitVec.toNat ((BitVec.add_right_inj (frameBase initial)).mp he)
      have hi := i.isLt
      simp only [BitVec.toNat_ofNat] at hn
      omega
    · intro c hcm j hj hcover
      obtain ⟨k, hk, he⟩ := hw c hcm _ hcover
      rw [← frameBase_add_56 initial, BitVec.add_assoc] at he
      have hn := congrArg BitVec.toNat ((BitVec.add_right_inj (frameBase initial)).mp he)
      simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat] at hn
      omega
  refine ⟨h.of_agreesExcept hc hr ha ?_ hsp hsaved hcs, ?_⟩
  · intro c hcm address hcover
    obtain ⟨i, hi, rfl⟩ := hw c hcm address hcover
    exact ⟨_, by simp [writeRegions], frameSlot_contains hc hi⟩
  · funext lane
    apply memLoad_congr
    intro j hj
    apply congrArg (fun x : Option UInt8 ↦ x.getD 0)
    apply ha.memory
    intro c hcm hcover
    obtain ⟨i, hi, he⟩ := hw c hcm _ hcover
    apply hc.stateStack (8 * lane.val + j) (by have := lane.isLt; omega) (272 + i) (by omega)
    have heq : stackBase initial + BitVec.ofNat 64 (272 + i) = frameBase initial + BitVec.ofNat 64 i := by
      simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using congrArg (· + BitVec.ofNat 64 i) (stackBase_add_272 initial)
    rw [heq]
    simpa only [BitVec.ofNat_add, BitVec.add_assoc] using he

end Sha3.Proofs.Update
