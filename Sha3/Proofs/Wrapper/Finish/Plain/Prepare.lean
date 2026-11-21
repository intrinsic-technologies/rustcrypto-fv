import Sha3.Proofs.Wrapper.Finish.Arguments
import Sha3.Proofs.Update.Layout
import Sha3.Proofs.Wrapper.Setup.Initialize
import Sha3.Proofs.Wrapper.Setup.Prefix
import Sha3.Proofs.Wrapper.Finish.Plain.Mov32
import Sha3.Proofs.Wrapper.Finish.Plain.Code

namespace Sha3.Proofs.Wrapper.Finish.Plain

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

def zeroCount : Variant → Nat
  | .sha224 | .sha256 => 4
  | .sha384 => 6
  | .sha512 => 8

def prepareSteps (v : Variant) : Nat := zeroCount v + 2

def zeroOffset (v : Variant) (i : Nat) (mode : Mode := .plain) : Nat :=
  digestOffset mode + 8 * (zeroCount v - 1 - i)
def zeroWidth (v : Variant) (i : Nat) : Nat := if v = .sha224 ∧ i = 0 then 4 else 8
def zeroPC (v : Variant) (i : Nat) (keccak : Bool := false) (mode : Mode := .plain) : BitVec 64 :=
  startAddress mode v keccak + BitVec.ofNat 64
    (9 * i - (if v = .sha224 ∧ 0 < i then 1 else 0) - (if mode ≠ .digest ∧ zeroCount v ≤ i then 1 else 0))

def prepareChanges (initial : RamState) (v : Variant) (keccak : Bool := false) (mode : Mode := .plain) : List Component :=
  [.reg 6, .reg 7, .rip] ++ (List.range (zeroCount v)).map
    (fun i ↦ .mem (frameBase initial v mode keccak + BitVec.ofNat 64 (zeroOffset v i mode)) (zeroWidth v i))

theorem prepareChanges_noRsp (initial : RamState) (v : Variant) (keccak : Bool := false) (mode : Mode := .plain) :
    Component.reg 4 ∉ prepareChanges initial v keccak mode := by simp [prepareChanges]

theorem prepareChanges_cover {initial : RamState} {v : Variant} {keccak : Bool} {mode : Mode} {c : Component}
    (hc : c ∈ prepareChanges initial v keccak mode) {address : BitVec 64} (ha : c.Covers address) :
    ∃ i < digestOffset mode + v.digestBytes, address = frameBase initial v mode keccak + BitVec.ofNat 64 i := by
  simp only [prepareChanges, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_map, List.mem_range] at hc
  rcases hc with (rfl | rfl | rfl) | ⟨i, hi, rfl⟩
  all_goals try exact ha.elim
  obtain ⟨j, hj, rfl⟩ := ha
  refine ⟨zeroOffset v i mode + j, ?_, ?_⟩
  · have h : ∀ i : Fin (zeroCount v), zeroOffset v i mode + zeroWidth v i ≤ digestOffset mode + v.digestBytes := by
      cases mode <;> cases keccak <;> cases v <;> decide +kernel
    have hh : zeroOffset v i mode + zeroWidth v i ≤ digestOffset mode + v.digestBytes := h ⟨i, hi⟩
    omega
  · rw [BitVec.add_assoc, BitVec.ofNat_add]

theorem prepareChanges_writes {initial : RamState} {v : Variant} {keccak : Bool} {mode : Mode}
    (hs : Stack.Valid initial (mode.entry v keccak).minStackBytes) :
    WritesWithin (prepareChanges initial v keccak mode)
      #v[Stack.region initial (mode.entry v keccak).minStackBytes] := by
  intro c hc a ha
  obtain ⟨i, hi, rfl⟩ := prepareChanges_cover hc ha
  refine ⟨_, Vector.mem_iff_getElem.mpr ⟨0, by decide, rfl⟩, ?_⟩
  apply frameAddress_contains hs (by rw [Mode.stackBudget mode v keccak]; omega)
  have h : digestOffset mode + v.digestBytes ≤ mode.frameSize v keccak := by cases mode <;> cases keccak <;> cases v <;> decide +kernel
  omega

theorem prepareChanges_saved {initial s t : RamState} {v : Variant} {keccak : Bool} {mode : Mode}
    (hs : SavedFrame initial s mode) (ha : AgreesExcept (prepareChanges initial v keccak mode) s t) :
    SavedFrame initial t mode := by
  apply hs.of_localFrame (v := v) (mode := mode) (keccak := keccak) ha
  intro c hc a hcover
  obtain ⟨i, hi, rfl⟩ := prepareChanges_cover hc hcover
  refine ⟨8 + i, ?_, ?_⟩
  · have h : digestOffset mode + v.digestBytes + 8 * mode.pushCount ≤ mode.frameSize v keccak := by cases mode <;> cases keccak <;> cases v <;> decide +kernel
    have hpush : 1 ≤ mode.pushCount := by cases mode <;> decide +kernel
    omega
  · rw [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.sub_add_cancel]

theorem prepareChanges_read {initial s t : RamState} {v : Variant} {keccak : Bool} {mode : Mode} {offset width : Nat}
    (ha : AgreesExcept (prepareChanges initial v keccak mode) s t)
    (hlo : digestOffset mode + v.digestBytes ≤ offset) (hhi : offset + width / 8 < 2^64) :
    (Operand.mem (frameBase initial v mode keccak + BitVec.ofNat 64 offset) : Operand width).read t =
      (Operand.mem (frameBase initial v mode keccak + BitVec.ofNat 64 offset) : Operand width).read s := by
  apply memLoad_congr
  intro j hj
  simp only [memByte, PhysicalMemory.read]
  rw [ha.byte (by
    intro c hc hcover
    obtain ⟨i, hi, he⟩ := prepareChanges_cover hc hcover
    have hd : digestOffset mode + v.digestBytes ≤ 2^64 := by cases mode <;> cases keccak <;> cases v <;> decide +kernel
    have apart := RangeApart.offsets (frameBase initial v mode keccak) (a := 0) (b := offset)
      (len := digestOffset mode + v.digestBytes) (count := width / 8) (by omega) (by omega) (.inl (by omega))
    apply apart i hi j hj
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using he.symm)]

private theorem prepareAdvance [bindings : Bindings] {initial s : RamState} {v : Variant} {keccak : Bool} {mode : Mode}
    {inputs : Array Input} {split : Nat} {p : BitVec 64} {bytes : List UInt8}
    {pre : RamState → Prop} {effect : RamState → Effect}
    (hCall : ValidInvocation bindings v mode initial inputs split keccak)
    (step : StepEffect pre (codeRange p bytes) effect) (image : ImageAt p bytes)
    (frame : ∀ c ∈ (effect s).components, c ∈ prepareChanges initial v keccak mode)
    (inv : Invariant initial v mode s keccak) (hs : stackPtr s = frameBase initial v mode keccak)
    (hp : pre s) :
    ∃ t, Advances (returnBoundary initial) 1 s t ∧ Invariant initial v mode t keccak ∧
      stackPtr t = frameBase initial v mode keccak ∧ (effect s).Holds s t ∧
      AgreesExcept (prepareChanges initial v keccak mode) s t := by
  obtain ⟨t, ht, hr, he⟩ := step s inv.ready (image.code inv.loaded) hp
  have ha := he.agrees.mono frame
  have htsp : stackPtr t = frameBase initial v mode keccak :=
    (ha.read (r := 4) (n := 64) (prepareChanges_noRsp initial v keccak mode)).trans hs
  refine ⟨t, Advances.of_step ht (.inr ?_), inv.of_agreesExcept hCall hr ha ?_ (by simp [prepareChanges]), htsp, he, ha⟩
  · change stackPtr t ≠ _
    rw [htsp]
    rw [frameBase]
    exact stackSub_ne_returnBoundary initial _ (by cases mode <;> cases keccak <;> cases v <;> decide +kernel)
  · intro c hc a hcover
    obtain ⟨region, hregion, hcontains⟩ := prepareChanges_writes hCall.stackAvailable c hc a hcover
    have heq : region = Stack.region initial (mode.entry v keccak).minStackBytes := by simpa using hregion
    exact ⟨_, stack_mem_writeRegions initial v mode keccak, heq ▸ hcontains⟩


private theorem store_advance [bindings : Bindings] {initial s : RamState} {v : Variant} {keccak : Bool} {mode : Mode}
    {inputs : Array Input} {split : Nat} {p : BitVec 64} {bytes : List UInt8}
    {n len offset : Nat} {address : RamState → BitVec 64} {value : RamState → BitVec n}
    (hCall : ValidInvocation bindings v mode initial inputs split keccak)
    (step : StepEffect (StorePreReadable p address (n / 8)) (codeRange p bytes)
      (storeEffect p len address value)) (image : ImageAt p bytes)
    (hm : Component.mem (frameBase initial v mode keccak + BitVec.ofNat 64 offset) (n / 8) ∈
      prepareChanges initial v keccak mode)
    (ha : address s = stackPtr s + BitVec.ofNat 64 offset)
    (hrange : offset + n / 8 ≤ mode.frameSize v keccak + 8)
    (inv : Invariant initial v mode s keccak) (hs : stackPtr s = frameBase initial v mode keccak)
    (hp : s.RIP = p) :
    ∃ t, Advances (returnBoundary initial) 1 s t ∧ Invariant initial v mode t keccak ∧
      stackPtr t = frameBase initial v mode keccak ∧ t.RIP = p + BitVec.ofNat 64 len ∧
      AgreesExcept (prepareChanges initial v keccak mode) s t := by
  have addr : address s = frameBase initial v mode keccak + BitVec.ofNat 64 offset := ha.trans (congrArg (· + BitVec.ofNat 64 offset) hs)
  have pre : StorePreReadable p address (n / 8) s := by
    refine ⟨⟨hp, addr ▸ inv.frameReadable hCall.stackAvailable hrange⟩, ?_⟩
    intro i hi ht
    have ⟨j, hj, he⟩ := prepareChanges_cover hm (address := address s + BitVec.ofNat 64 i)
      (by rw [addr]; exact ⟨i, hi, rfl⟩)
    apply writeRegions_avoid hCall _ (stack_mem_writeRegions initial v mode keccak) _ _ (.inr ht)
    rw [he]
    apply frameAddress_contains hCall.stackAvailable (by rw [Mode.stackBudget mode v keccak]; omega)
    have hd : digestOffset mode + v.digestBytes ≤ mode.frameSize v keccak := by cases mode <;> cases keccak <;> cases v <;> decide +kernel
    omega
  obtain ⟨t, ht, it, st, et, agt⟩ := prepareAdvance hCall step image (by
    simp only [storeEffect_components, List.mem_cons, List.not_mem_nil, or_false]
    intro c hc
    rcases hc with rfl | rfl
    · simpa only [addr] using hm
    · simp [prepareChanges]) inv hs pre
  exact ⟨t, ht, it, st, et.rip, agt⟩


private theorem zero_step [bindings : Bindings] {initial s : RamState} {v : Variant} {keccak : Bool} {mode : Mode}
    {inputs : Array Input} {split i : Nat}
    (hCall : ValidInvocation bindings v mode initial inputs split keccak)
    (inv : Invariant initial v mode s keccak) (hs : stackPtr s = frameBase initial v mode keccak)
    (hp : s.RIP = zeroPC v i keccak mode) (hi : i < zeroCount v) (hMode : mode = .plain ∨ mode = .digest) :
    ∃ t, Advances (returnBoundary initial) 1 s t ∧ Invariant initial v mode t keccak ∧
      stackPtr t = frameBase initial v mode keccak ∧ t.RIP = zeroPC v (i + 1) keccak mode ∧
      AgreesExcept (prepareChanges initial v keccak mode) s t := by
  cases v
  case sha224 =>
    have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by change i < 4 at hi; omega
    rcases hi' with rfl | rfl | rfl | rfl
    · obtain ⟨t, ht, it, st, pt, ag⟩ := store_advance (n := 32) hCall
        (mov_m32_imm32_effect_step_of_readable (zeroPC .sha224 0 keccak mode)
          (.sib 4 none 0 (.d8 (BitVec.ofNat 8 (digestOffset mode + 24)))) (by rcases hMode with rfl | rfl <;> decide +kernel) (by rcases hMode with rfl | rfl <;> decide +kernel) (by rcases hMode with rfl | rfl <;> decide +kernel) 0)
        (by unfold ImageAt; rcases hMode with rfl | rfl <;> cases keccak <;> decide +kernel)
        (offset := digestOffset mode + 24) (by simp [prepareChanges, zeroCount, zeroOffset, zeroWidth, List.range_succ])
        (by rcases hMode with rfl | rfl <;> rfl) (by rcases hMode with rfl | rfl <;> cases keccak <;> decide +kernel) inv hs hp
      exact ⟨t, ht, it, st, pt.trans (by rcases hMode with rfl | rfl <;> cases keccak <;> decide +kernel), ag⟩
    · obtain ⟨t, ht, it, st, pt, ag⟩ := store_advance (n := 64) hCall
        (mov_m64_imm32_effect_step_of_readable (zeroPC .sha224 1 keccak mode) 0x48 (by unfold RexWPrefix; decide +kernel)
          (.sib 4 none 0 (.d8 (BitVec.ofNat 8 (digestOffset mode + 16)))) (by rcases hMode with rfl | rfl <;> decide +kernel) (by rcases hMode with rfl | rfl <;> decide +kernel) (by rcases hMode with rfl | rfl <;> decide +kernel) 0)
        (by unfold ImageAt; rcases hMode with rfl | rfl <;> cases keccak <;> decide +kernel)
        (offset := digestOffset mode + 16) (by simp [prepareChanges, zeroCount, zeroOffset, zeroWidth, List.range_succ])
        (by rcases hMode with rfl | rfl <;> rfl) (by rcases hMode with rfl | rfl <;> cases keccak <;> decide +kernel) inv hs hp
      exact ⟨t, ht, it, st, pt.trans (by rcases hMode with rfl | rfl <;> cases keccak <;> decide +kernel), ag⟩
    · obtain ⟨t, ht, it, st, pt, ag⟩ := store_advance (n := 64) hCall
        (mov_m64_imm32_effect_step_of_readable (zeroPC .sha224 2 keccak mode) 0x48 (by unfold RexWPrefix; decide +kernel)
          (.sib 4 none 0 (.d8 (BitVec.ofNat 8 (digestOffset mode + 8)))) (by rcases hMode with rfl | rfl <;> decide +kernel) (by rcases hMode with rfl | rfl <;> decide +kernel) (by rcases hMode with rfl | rfl <;> decide +kernel) 0)
        (by unfold ImageAt; rcases hMode with rfl | rfl <;> cases keccak <;> decide +kernel)
        (offset := digestOffset mode + 8) (by simp [prepareChanges, zeroCount, zeroOffset, zeroWidth, List.range_succ])
        (by rcases hMode with rfl | rfl <;> rfl) (by rcases hMode with rfl | rfl <;> cases keccak <;> decide +kernel) inv hs hp
      exact ⟨t, ht, it, st, pt.trans (by rcases hMode with rfl | rfl <;> cases keccak <;> decide +kernel), ag⟩
    · obtain ⟨t, ht, it, st, pt, ag⟩ := store_advance (n := 64) hCall
        (mov_m64_imm32_effect_step_of_readable (zeroPC .sha224 3 keccak mode) 0x48 (by unfold RexWPrefix; decide +kernel)
          (.sib 4 none 0 (if mode = .digest then .d8 8 else .none)) (by rcases hMode with rfl | rfl <;> decide +kernel) (by rcases hMode with rfl | rfl <;> decide +kernel) (by rcases hMode with rfl | rfl <;> decide +kernel) 0)
        (by unfold ImageAt; rcases hMode with rfl | rfl <;> cases keccak <;> decide +kernel)
        (offset := digestOffset mode + 0) (by simp [prepareChanges, zeroCount, zeroOffset, zeroWidth, List.range_succ])
        (by rcases hMode with rfl | rfl <;> rfl) (by rcases hMode with rfl | rfl <;> cases keccak <;> decide +kernel) inv hs hp
      exact ⟨t, ht, it, st, pt.trans (by rcases hMode with rfl | rfl <;> cases keccak <;> decide +kernel), ag⟩
  case sha256 =>
    have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by change i < 4 at hi; omega
    rcases hi' with rfl | rfl | rfl | rfl
    · obtain ⟨t, ht, it, st, pt, ag⟩ := store_advance (n := 64) hCall
        (mov_m64_imm32_effect_step_of_readable (zeroPC .sha256 0 keccak mode) 0x48 (by unfold RexWPrefix; decide +kernel)
          (.sib 4 none 0 (.d8 (BitVec.ofNat 8 (digestOffset mode + 24)))) (by rcases hMode with rfl | rfl <;> decide +kernel) (by rcases hMode with rfl | rfl <;> decide +kernel) (by rcases hMode with rfl | rfl <;> decide +kernel) 0)
        (by unfold ImageAt; rcases hMode with rfl | rfl <;> cases keccak <;> decide +kernel)
        (offset := digestOffset mode + 24) (by simp [prepareChanges, zeroCount, zeroOffset, zeroWidth, List.range_succ])
        (by rcases hMode with rfl | rfl <;> rfl) (by rcases hMode with rfl | rfl <;> cases keccak <;> decide +kernel) inv hs hp
      exact ⟨t, ht, it, st, pt.trans (by rcases hMode with rfl | rfl <;> cases keccak <;> decide +kernel), ag⟩
    · obtain ⟨t, ht, it, st, pt, ag⟩ := store_advance (n := 64) hCall
        (mov_m64_imm32_effect_step_of_readable (zeroPC .sha256 1 keccak mode) 0x48 (by unfold RexWPrefix; decide +kernel)
          (.sib 4 none 0 (.d8 (BitVec.ofNat 8 (digestOffset mode + 16)))) (by rcases hMode with rfl | rfl <;> decide +kernel) (by rcases hMode with rfl | rfl <;> decide +kernel) (by rcases hMode with rfl | rfl <;> decide +kernel) 0)
        (by unfold ImageAt; rcases hMode with rfl | rfl <;> cases keccak <;> decide +kernel)
        (offset := digestOffset mode + 16) (by simp [prepareChanges, zeroCount, zeroOffset, zeroWidth, List.range_succ])
        (by rcases hMode with rfl | rfl <;> rfl) (by rcases hMode with rfl | rfl <;> cases keccak <;> decide +kernel) inv hs hp
      exact ⟨t, ht, it, st, pt.trans (by rcases hMode with rfl | rfl <;> cases keccak <;> decide +kernel), ag⟩
    · obtain ⟨t, ht, it, st, pt, ag⟩ := store_advance (n := 64) hCall
        (mov_m64_imm32_effect_step_of_readable (zeroPC .sha256 2 keccak mode) 0x48 (by unfold RexWPrefix; decide +kernel)
          (.sib 4 none 0 (.d8 (BitVec.ofNat 8 (digestOffset mode + 8)))) (by rcases hMode with rfl | rfl <;> decide +kernel) (by rcases hMode with rfl | rfl <;> decide +kernel) (by rcases hMode with rfl | rfl <;> decide +kernel) 0)
        (by unfold ImageAt; rcases hMode with rfl | rfl <;> cases keccak <;> decide +kernel)
        (offset := digestOffset mode + 8) (by simp [prepareChanges, zeroCount, zeroOffset, zeroWidth, List.range_succ])
        (by rcases hMode with rfl | rfl <;> rfl) (by rcases hMode with rfl | rfl <;> cases keccak <;> decide +kernel) inv hs hp
      exact ⟨t, ht, it, st, pt.trans (by rcases hMode with rfl | rfl <;> cases keccak <;> decide +kernel), ag⟩
    · obtain ⟨t, ht, it, st, pt, ag⟩ := store_advance (n := 64) hCall
        (mov_m64_imm32_effect_step_of_readable (zeroPC .sha256 3 keccak mode) 0x48 (by unfold RexWPrefix; decide +kernel)
          (.sib 4 none 0 (if mode = .digest then .d8 8 else .none)) (by rcases hMode with rfl | rfl <;> decide +kernel) (by rcases hMode with rfl | rfl <;> decide +kernel) (by rcases hMode with rfl | rfl <;> decide +kernel) 0)
        (by unfold ImageAt; rcases hMode with rfl | rfl <;> cases keccak <;> decide +kernel)
        (offset := digestOffset mode + 0) (by simp [prepareChanges, zeroCount, zeroOffset, zeroWidth, List.range_succ])
        (by rcases hMode with rfl | rfl <;> rfl) (by rcases hMode with rfl | rfl <;> cases keccak <;> decide +kernel) inv hs hp
      exact ⟨t, ht, it, st, pt.trans (by rcases hMode with rfl | rfl <;> cases keccak <;> decide +kernel), ag⟩
  case sha384 =>
    have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by change i < 6 at hi; omega
    rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨t, ht, it, st, pt, ag⟩ := store_advance (n := 64) hCall
        (mov_m64_imm32_effect_step_of_readable (zeroPC .sha384 0 keccak mode) 0x48 (by unfold RexWPrefix; decide +kernel)
          (.sib 4 none 0 (.d8 (BitVec.ofNat 8 (digestOffset mode + 40)))) (by rcases hMode with rfl | rfl <;> decide +kernel) (by rcases hMode with rfl | rfl <;> decide +kernel) (by rcases hMode with rfl | rfl <;> decide +kernel) 0)
        (by unfold ImageAt; rcases hMode with rfl | rfl <;> cases keccak <;> decide +kernel)
        (offset := digestOffset mode + 40) (by simp [prepareChanges, zeroCount, zeroOffset, zeroWidth, List.range_succ])
        (by rcases hMode with rfl | rfl <;> rfl) (by rcases hMode with rfl | rfl <;> cases keccak <;> decide +kernel) inv hs hp
      exact ⟨t, ht, it, st, pt.trans (by rcases hMode with rfl | rfl <;> cases keccak <;> decide +kernel), ag⟩
    · obtain ⟨t, ht, it, st, pt, ag⟩ := store_advance (n := 64) hCall
        (mov_m64_imm32_effect_step_of_readable (zeroPC .sha384 1 keccak mode) 0x48 (by unfold RexWPrefix; decide +kernel)
          (.sib 4 none 0 (.d8 (BitVec.ofNat 8 (digestOffset mode + 32)))) (by rcases hMode with rfl | rfl <;> decide +kernel) (by rcases hMode with rfl | rfl <;> decide +kernel) (by rcases hMode with rfl | rfl <;> decide +kernel) 0)
        (by unfold ImageAt; rcases hMode with rfl | rfl <;> cases keccak <;> decide +kernel)
        (offset := digestOffset mode + 32) (by simp [prepareChanges, zeroCount, zeroOffset, zeroWidth, List.range_succ])
        (by rcases hMode with rfl | rfl <;> rfl) (by rcases hMode with rfl | rfl <;> cases keccak <;> decide +kernel) inv hs hp
      exact ⟨t, ht, it, st, pt.trans (by rcases hMode with rfl | rfl <;> cases keccak <;> decide +kernel), ag⟩
    · obtain ⟨t, ht, it, st, pt, ag⟩ := store_advance (n := 64) hCall
        (mov_m64_imm32_effect_step_of_readable (zeroPC .sha384 2 keccak mode) 0x48 (by unfold RexWPrefix; decide +kernel)
          (.sib 4 none 0 (.d8 (BitVec.ofNat 8 (digestOffset mode + 24)))) (by rcases hMode with rfl | rfl <;> decide +kernel) (by rcases hMode with rfl | rfl <;> decide +kernel) (by rcases hMode with rfl | rfl <;> decide +kernel) 0)
        (by unfold ImageAt; rcases hMode with rfl | rfl <;> cases keccak <;> decide +kernel)
        (offset := digestOffset mode + 24) (by simp [prepareChanges, zeroCount, zeroOffset, zeroWidth, List.range_succ])
        (by rcases hMode with rfl | rfl <;> rfl) (by rcases hMode with rfl | rfl <;> cases keccak <;> decide +kernel) inv hs hp
      exact ⟨t, ht, it, st, pt.trans (by rcases hMode with rfl | rfl <;> cases keccak <;> decide +kernel), ag⟩
    · obtain ⟨t, ht, it, st, pt, ag⟩ := store_advance (n := 64) hCall
        (mov_m64_imm32_effect_step_of_readable (zeroPC .sha384 3 keccak mode) 0x48 (by unfold RexWPrefix; decide +kernel)
          (.sib 4 none 0 (.d8 (BitVec.ofNat 8 (digestOffset mode + 16)))) (by rcases hMode with rfl | rfl <;> decide +kernel) (by rcases hMode with rfl | rfl <;> decide +kernel) (by rcases hMode with rfl | rfl <;> decide +kernel) 0)
        (by unfold ImageAt; rcases hMode with rfl | rfl <;> cases keccak <;> decide +kernel)
        (offset := digestOffset mode + 16) (by simp [prepareChanges, zeroCount, zeroOffset, zeroWidth, List.range_succ])
        (by rcases hMode with rfl | rfl <;> rfl) (by rcases hMode with rfl | rfl <;> cases keccak <;> decide +kernel) inv hs hp
      exact ⟨t, ht, it, st, pt.trans (by rcases hMode with rfl | rfl <;> cases keccak <;> decide +kernel), ag⟩
    · obtain ⟨t, ht, it, st, pt, ag⟩ := store_advance (n := 64) hCall
        (mov_m64_imm32_effect_step_of_readable (zeroPC .sha384 4 keccak mode) 0x48 (by unfold RexWPrefix; decide +kernel)
          (.sib 4 none 0 (.d8 (BitVec.ofNat 8 (digestOffset mode + 8)))) (by rcases hMode with rfl | rfl <;> decide +kernel) (by rcases hMode with rfl | rfl <;> decide +kernel) (by rcases hMode with rfl | rfl <;> decide +kernel) 0)
        (by unfold ImageAt; rcases hMode with rfl | rfl <;> cases keccak <;> decide +kernel)
        (offset := digestOffset mode + 8) (by simp [prepareChanges, zeroCount, zeroOffset, zeroWidth, List.range_succ])
        (by rcases hMode with rfl | rfl <;> rfl) (by rcases hMode with rfl | rfl <;> cases keccak <;> decide +kernel) inv hs hp
      exact ⟨t, ht, it, st, pt.trans (by rcases hMode with rfl | rfl <;> cases keccak <;> decide +kernel), ag⟩
    · obtain ⟨t, ht, it, st, pt, ag⟩ := store_advance (n := 64) hCall
        (mov_m64_imm32_effect_step_of_readable (zeroPC .sha384 5 keccak mode) 0x48 (by unfold RexWPrefix; decide +kernel)
          (.sib 4 none 0 (if mode = .digest then .d8 8 else .none)) (by rcases hMode with rfl | rfl <;> decide +kernel) (by rcases hMode with rfl | rfl <;> decide +kernel) (by rcases hMode with rfl | rfl <;> decide +kernel) 0)
        (by unfold ImageAt; rcases hMode with rfl | rfl <;> cases keccak <;> decide +kernel)
        (offset := digestOffset mode + 0) (by simp [prepareChanges, zeroCount, zeroOffset, zeroWidth, List.range_succ])
        (by rcases hMode with rfl | rfl <;> rfl) (by rcases hMode with rfl | rfl <;> cases keccak <;> decide +kernel) inv hs hp
      exact ⟨t, ht, it, st, pt.trans (by rcases hMode with rfl | rfl <;> cases keccak <;> decide +kernel), ag⟩
  case sha512 =>
    have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by change i < 8 at hi; omega
    rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨t, ht, it, st, pt, ag⟩ := store_advance (n := 64) hCall
        (mov_m64_imm32_effect_step_of_readable (zeroPC .sha512 0 keccak mode) 0x48 (by unfold RexWPrefix; decide +kernel)
          (.sib 4 none 0 (.d8 (BitVec.ofNat 8 (digestOffset mode + 56)))) (by rcases hMode with rfl | rfl <;> decide +kernel) (by rcases hMode with rfl | rfl <;> decide +kernel) (by rcases hMode with rfl | rfl <;> decide +kernel) 0)
        (by unfold ImageAt; rcases hMode with rfl | rfl <;> cases keccak <;> decide +kernel)
        (offset := digestOffset mode + 56) (by simp [prepareChanges, zeroCount, zeroOffset, zeroWidth, List.range_succ])
        (by rcases hMode with rfl | rfl <;> rfl) (by rcases hMode with rfl | rfl <;> cases keccak <;> decide +kernel) inv hs hp
      exact ⟨t, ht, it, st, pt.trans (by rcases hMode with rfl | rfl <;> cases keccak <;> decide +kernel), ag⟩
    · obtain ⟨t, ht, it, st, pt, ag⟩ := store_advance (n := 64) hCall
        (mov_m64_imm32_effect_step_of_readable (zeroPC .sha512 1 keccak mode) 0x48 (by unfold RexWPrefix; decide +kernel)
          (.sib 4 none 0 (.d8 (BitVec.ofNat 8 (digestOffset mode + 48)))) (by rcases hMode with rfl | rfl <;> decide +kernel) (by rcases hMode with rfl | rfl <;> decide +kernel) (by rcases hMode with rfl | rfl <;> decide +kernel) 0)
        (by unfold ImageAt; rcases hMode with rfl | rfl <;> cases keccak <;> decide +kernel)
        (offset := digestOffset mode + 48) (by simp [prepareChanges, zeroCount, zeroOffset, zeroWidth, List.range_succ])
        (by rcases hMode with rfl | rfl <;> rfl) (by rcases hMode with rfl | rfl <;> cases keccak <;> decide +kernel) inv hs hp
      exact ⟨t, ht, it, st, pt.trans (by rcases hMode with rfl | rfl <;> cases keccak <;> decide +kernel), ag⟩
    · obtain ⟨t, ht, it, st, pt, ag⟩ := store_advance (n := 64) hCall
        (mov_m64_imm32_effect_step_of_readable (zeroPC .sha512 2 keccak mode) 0x48 (by unfold RexWPrefix; decide +kernel)
          (.sib 4 none 0 (.d8 (BitVec.ofNat 8 (digestOffset mode + 40)))) (by rcases hMode with rfl | rfl <;> decide +kernel) (by rcases hMode with rfl | rfl <;> decide +kernel) (by rcases hMode with rfl | rfl <;> decide +kernel) 0)
        (by unfold ImageAt; rcases hMode with rfl | rfl <;> cases keccak <;> decide +kernel)
        (offset := digestOffset mode + 40) (by simp [prepareChanges, zeroCount, zeroOffset, zeroWidth, List.range_succ])
        (by rcases hMode with rfl | rfl <;> rfl) (by rcases hMode with rfl | rfl <;> cases keccak <;> decide +kernel) inv hs hp
      exact ⟨t, ht, it, st, pt.trans (by rcases hMode with rfl | rfl <;> cases keccak <;> decide +kernel), ag⟩
    · obtain ⟨t, ht, it, st, pt, ag⟩ := store_advance (n := 64) hCall
        (mov_m64_imm32_effect_step_of_readable (zeroPC .sha512 3 keccak mode) 0x48 (by unfold RexWPrefix; decide +kernel)
          (.sib 4 none 0 (.d8 (BitVec.ofNat 8 (digestOffset mode + 32)))) (by rcases hMode with rfl | rfl <;> decide +kernel) (by rcases hMode with rfl | rfl <;> decide +kernel) (by rcases hMode with rfl | rfl <;> decide +kernel) 0)
        (by unfold ImageAt; rcases hMode with rfl | rfl <;> cases keccak <;> decide +kernel)
        (offset := digestOffset mode + 32) (by simp [prepareChanges, zeroCount, zeroOffset, zeroWidth, List.range_succ])
        (by rcases hMode with rfl | rfl <;> rfl) (by rcases hMode with rfl | rfl <;> cases keccak <;> decide +kernel) inv hs hp
      exact ⟨t, ht, it, st, pt.trans (by rcases hMode with rfl | rfl <;> cases keccak <;> decide +kernel), ag⟩
    · obtain ⟨t, ht, it, st, pt, ag⟩ := store_advance (n := 64) hCall
        (mov_m64_imm32_effect_step_of_readable (zeroPC .sha512 4 keccak mode) 0x48 (by unfold RexWPrefix; decide +kernel)
          (.sib 4 none 0 (.d8 (BitVec.ofNat 8 (digestOffset mode + 24)))) (by rcases hMode with rfl | rfl <;> decide +kernel) (by rcases hMode with rfl | rfl <;> decide +kernel) (by rcases hMode with rfl | rfl <;> decide +kernel) 0)
        (by unfold ImageAt; rcases hMode with rfl | rfl <;> cases keccak <;> decide +kernel)
        (offset := digestOffset mode + 24) (by simp [prepareChanges, zeroCount, zeroOffset, zeroWidth, List.range_succ])
        (by rcases hMode with rfl | rfl <;> rfl) (by rcases hMode with rfl | rfl <;> cases keccak <;> decide +kernel) inv hs hp
      exact ⟨t, ht, it, st, pt.trans (by rcases hMode with rfl | rfl <;> cases keccak <;> decide +kernel), ag⟩
    · obtain ⟨t, ht, it, st, pt, ag⟩ := store_advance (n := 64) hCall
        (mov_m64_imm32_effect_step_of_readable (zeroPC .sha512 5 keccak mode) 0x48 (by unfold RexWPrefix; decide +kernel)
          (.sib 4 none 0 (.d8 (BitVec.ofNat 8 (digestOffset mode + 16)))) (by rcases hMode with rfl | rfl <;> decide +kernel) (by rcases hMode with rfl | rfl <;> decide +kernel) (by rcases hMode with rfl | rfl <;> decide +kernel) 0)
        (by unfold ImageAt; rcases hMode with rfl | rfl <;> cases keccak <;> decide +kernel)
        (offset := digestOffset mode + 16) (by simp [prepareChanges, zeroCount, zeroOffset, zeroWidth, List.range_succ])
        (by rcases hMode with rfl | rfl <;> rfl) (by rcases hMode with rfl | rfl <;> cases keccak <;> decide +kernel) inv hs hp
      exact ⟨t, ht, it, st, pt.trans (by rcases hMode with rfl | rfl <;> cases keccak <;> decide +kernel), ag⟩
    · obtain ⟨t, ht, it, st, pt, ag⟩ := store_advance (n := 64) hCall
        (mov_m64_imm32_effect_step_of_readable (zeroPC .sha512 6 keccak mode) 0x48 (by unfold RexWPrefix; decide +kernel)
          (.sib 4 none 0 (.d8 (BitVec.ofNat 8 (digestOffset mode + 8)))) (by rcases hMode with rfl | rfl <;> decide +kernel) (by rcases hMode with rfl | rfl <;> decide +kernel) (by rcases hMode with rfl | rfl <;> decide +kernel) 0)
        (by unfold ImageAt; rcases hMode with rfl | rfl <;> cases keccak <;> decide +kernel)
        (offset := digestOffset mode + 8) (by simp [prepareChanges, zeroCount, zeroOffset, zeroWidth, List.range_succ])
        (by rcases hMode with rfl | rfl <;> rfl) (by rcases hMode with rfl | rfl <;> cases keccak <;> decide +kernel) inv hs hp
      exact ⟨t, ht, it, st, pt.trans (by rcases hMode with rfl | rfl <;> cases keccak <;> decide +kernel), ag⟩
    · obtain ⟨t, ht, it, st, pt, ag⟩ := store_advance (n := 64) hCall
        (mov_m64_imm32_effect_step_of_readable (zeroPC .sha512 7 keccak mode) 0x48 (by unfold RexWPrefix; decide +kernel)
          (.sib 4 none 0 (if mode = .digest then .d8 8 else .none)) (by rcases hMode with rfl | rfl <;> decide +kernel) (by rcases hMode with rfl | rfl <;> decide +kernel) (by rcases hMode with rfl | rfl <;> decide +kernel) 0)
        (by unfold ImageAt; rcases hMode with rfl | rfl <;> cases keccak <;> decide +kernel)
        (offset := digestOffset mode + 0) (by simp [prepareChanges, zeroCount, zeroOffset, zeroWidth, List.range_succ])
        (by rcases hMode with rfl | rfl <;> rfl) (by rcases hMode with rfl | rfl <;> cases keccak <;> decide +kernel) inv hs hp
      exact ⟨t, ht, it, st, pt.trans (by rcases hMode with rfl | rfl <;> cases keccak <;> decide +kernel), ag⟩

private theorem zero_advance [bindings : Bindings] {initial s : RamState} {v : Variant} {keccak : Bool} {mode : Mode}
    {inputs : Array Input} {split k : Nat}
    (hCall : ValidInvocation bindings v mode initial inputs split keccak)
    (inv : Invariant initial v mode s keccak) (hs : stackPtr s = frameBase initial v mode keccak)
    (hp : s.RIP = startAddress mode v keccak) (hk : k ≤ zeroCount v) (hMode : mode = .plain ∨ mode = .digest) :
    ∃ t, Advances (returnBoundary initial) k s t ∧ Invariant initial v mode t keccak ∧
      stackPtr t = frameBase initial v mode keccak ∧ t.RIP = zeroPC v k keccak mode ∧
      AgreesExcept (prepareChanges initial v keccak mode) s t := by
  induction k with
  | zero =>
    exact ⟨s, (advances_zero _ _ _).mpr rfl, inv, hs,
      hp.trans (by cases mode <;> cases keccak <;> cases v <;> rfl), AgreesExcept.refl _ _⟩
  | succ k ih =>
    obtain ⟨u, hu, iu, su, pu, au⟩ := ih (by omega)
    obtain ⟨t, ht, it, st, pt, agt⟩ := zero_step hCall iu su pu (by omega) hMode
    exact ⟨t, hu.trans ht, it, st, pt,
      (au.trans agt).mono (by intro c hc; exact (List.mem_append.mp hc).elim id id)⟩

private theorem arguments_advance [bindings : Bindings] {initial s : RamState} {v : Variant} {keccak : Bool} {mode : Mode}
    {inputs : Array Input} {split : Nat}
    (hCall : ValidInvocation bindings v mode initial inputs split keccak)
    (inv : Invariant initial v mode s keccak) (hs : stackPtr s = frameBase initial v mode keccak)
    (hp : s.RIP = zeroPC v (zeroCount v) keccak mode)
    (hMode : mode = .plain ∨ mode = .digest)
    (hR12 : mode = .digest → s.regValue .r12 = statePointer initial v mode keccak) :
    ∃ t, Advances (returnBoundary initial) 2 s t ∧ Invariant initial v mode t keccak ∧
      stackPtr t = frameBase initial v mode keccak ∧ t.RIP = callAddress mode v keccak ∧
      t.regValue .rdi = statePointer initial v mode keccak ∧
      t.regValue .rsi = frameBase initial v mode keccak + BitVec.ofNat 64 (digestOffset mode) ∧
      AgreesExcept (prepareChanges initial v keccak mode) s t := by
  rcases hMode with rfl | rfl
  ·
    obtain ⟨u, hu, iu, su, eu, au⟩ := prepareAdvance hCall
      (lea_r64_effect_step (zeroPC v (zeroCount v) keccak .plain) 0x48 (by unfold RexWPrefix; decide +kernel)
        7 (plainStateAddr v) (by cases keccak <;> cases v <;> decide +kernel)
        (by cases keccak <;> cases v <;> decide +kernel) (by cases keccak <;> cases v <;> decide +kernel))
      (by unfold ImageAt; cases keccak <;> cases v <;> decide +kernel)
      (by simp [leaR64Effect_components, prepareChanges]; decide) inv hs hp
    have ru : u.regValue .rdi = statePointer initial v .plain keccak := by
      have hw := eu.writes
      change u.regValue .rdi = _ at hw
      rw [hw]
      unfold statePointer
      rw [← hs]
      cases v <;> rfl
    obtain ⟨t, ht, it, st, et, agt⟩ := prepareAdvance hCall
      (mov_r64_r64_effect_step (callAddress .plain v keccak - 3) 0x48 0xe6
        (by unfold RexWPrefix; decide +kernel) (by decide +kernel))
      (by unfold ImageAt; cases keccak <;> cases v <;> decide +kernel)
      (by simp [movR64R64Effect_components, prepareChanges]; decide)
      iu su (by cases keccak <;> cases v <;> exact eu.rip)
    refine ⟨t, hu.trans ht, it, st, et.rip.trans (by cases keccak <;> cases v <;> rfl), ?_, ?_,
      (au.trans agt).mono (by intro c hc; exact (List.mem_append.mp hc).elim id id)⟩
    · exact (et.agrees.read (r := 7) (n := 64) (by simp [movR64R64Effect_components]; decide)).trans ru
    · change t.regValue .rsi = frameBase initial v .plain keccak + 0#64
      rw [BitVec.add_zero]
      exact et.writes.trans su
  ·
    obtain ⟨u, hu, iu, su, eu, au⟩ := prepareAdvance hCall
      (lea_r64_effect_step (zeroPC v (zeroCount v) keccak .digest) 0x48
        (by unfold RexWPrefix; decide +kernel) 6 (.sib 4 none 0 (.d8 8))
        (by decide +kernel) (by decide +kernel) (by decide +kernel))
      (by unfold ImageAt; cases keccak <;> cases v <;> decide +kernel)
      (by simp [leaR64Effect_components, prepareChanges]; decide) inv hs hp
    have ru : u.regValue .rsi = frameBase initial v .digest keccak + 8 := by
      exact eu.writes.trans (congrArg (· + 8) hs)
    have r12 : u.regValue .r12 = statePointer initial v .digest keccak :=
      (au.read (r := 12) (n := 64) (by simp [prepareChanges])).trans (hR12 rfl)
    obtain ⟨t, ht, it, st, et, agt⟩ := prepareAdvance hCall
      (mov_r64_r64_effect_step (callAddress .digest v keccak - 3) 0x4c 0xe7
        (by unfold RexWPrefix; decide +kernel) (by decide +kernel))
      (by unfold ImageAt; cases keccak <;> cases v <;> decide +kernel)
      (by simp [movR64R64Effect_components, prepareChanges]; decide)
      iu su (by cases keccak <;> cases v <;> exact eu.rip)
    refine ⟨t, hu.trans ht, it, st, et.rip.trans (by cases keccak <;> cases v <;> rfl),
      et.writes.trans r12, ?_,
      (au.trans agt).mono (by intro c hc; exact (List.mem_append.mp hc).elim id id)⟩
    exact (et.agrees.read (r := 6) (n := 64)
      (by simp [movR64R64Effect_components]; decide)).trans ru
theorem prepare_advance [bindings : Bindings] {initial s : RamState} {v : Variant} {keccak : Bool} {mode : Mode}
    {inputs : Array Input} {split : Nat} {state : Incremental.State} {out : BitVec 64}
    (hCall : ValidInvocation bindings v mode initial inputs split keccak)
    (inv : Invariant initial v mode s keccak) (saved : SavedFrame initial s mode)
    (hp : s.RIP = startAddress mode v keccak) (hs : stackPtr s = frameBase initial v mode keccak)
    (hOutput : (outputOperand initial v mode keccak).read s = out)
    (hMetadata : (Operand.mem (statePointer initial v mode keccak + 200) : Operand 8).read s =
      BitVec.ofNat 8 state.cursor)
    (hLanes : Permutation.memoryLanes (statePointer initial v mode keccak) s = state.lanes)
    (hMode : mode = .plain ∨ mode = .digest := by exact Or.inl rfl)
    (hR12 : mode = .digest → s.regValue .r12 = statePointer initial v mode keccak := by intro h; cases h) :
    ∃ t, Advances (returnBoundary initial) (prepareSteps v) s t ∧
      Invariant initial v mode t keccak ∧ SavedFrame initial t mode ∧
      t.RIP = callAddress mode v keccak ∧ stackPtr t = frameBase initial v mode keccak ∧
      t.regValue .rdi = statePointer initial v mode keccak ∧
      t.regValue .rsi = frameBase initial v mode keccak + BitVec.ofNat 64 (digestOffset mode) ∧
      (outputOperand initial v mode keccak).read t = out ∧
      (Operand.mem (statePointer initial v mode keccak + 200) : Operand 8).read t =
        BitVec.ofNat 8 state.cursor ∧
      Permutation.memoryLanes (statePointer initial v mode keccak) t = state.lanes ∧
      MemoryWriteFrame s t #v[Stack.region initial (mode.entry v keccak).minStackBytes] ∧
      CalleeSavedRegistersUnchanged s t := by
  obtain ⟨u, hu, iu, su, pu, au⟩ := zero_advance hCall inv hs hp (Nat.le_refl (zeroCount v)) hMode
  obtain ⟨t, ht, it, st, pt, rt, ot, agt⟩ := arguments_advance hCall iu su pu hMode (fun h ↦
    (au.read (r := 12) (n := 64) (by simp [prepareChanges])).trans (hR12 h))
  have ag : AgreesExcept (prepareChanges initial v keccak mode) s t :=
    (au.trans agt).mono (by intro c hc; exact (List.mem_append.mp hc).elim id id)
  refine ⟨t, hu.trans ht, it, prepareChanges_saved saved ag, pt, st, rt, ot, ?_, ?_, ?_,
    ag.memoryWriteFrame (prepareChanges_writes hCall.stackAvailable), ?_⟩
  · rcases hMode with rfl | rfl
    · exact (prepareChanges_read (offset := Mode.plain.outputSlotOffset v keccak) (width := 64) ag
      (by cases keccak <;> cases v <;> decide +kernel) (by cases keccak <;> cases v <;> decide +kernel)).trans hOutput
    · exact (ag.read (r := 3) (n := 64) (by simp [prepareChanges])).trans hOutput
  · have he := prepareChanges_read (offset := mode.stateOffset v keccak + 200) (width := 8) ag
      (by cases mode <;> cases keccak <;> cases v <;> decide +kernel) (by cases mode <;> cases keccak <;> cases v <;> decide +kernel)
    have he' : (Operand.mem (statePointer initial v mode keccak + 200) : Operand 8).read t =
        (Operand.mem (statePointer initial v mode keccak + 200) : Operand 8).read s := by
      simpa only [statePointer, BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using he
    exact he'.trans hMetadata
  · rw [← hLanes]
    funext lane
    have hn := lane.isLt
    have he := prepareChanges_read (offset := mode.stateOffset v keccak + 8 * lane.val)
      (width := 64) ag (by rcases hMode with rfl | rfl <;> cases keccak <;> cases v <;> simp only [digestOffset, Mode.stateOffset, Variant.digestBytes, reduceCtorEq, Bool.false_eq_true, ↓reduceIte] <;> omega)
      (by cases mode <;> cases keccak <;> cases v <;> simp only [Mode.stateOffset, Bool.false_eq_true, ↓reduceIte] <;> omega)
    simpa only [Permutation.memoryLanes, statePointer,
      BitVec.ofNat_add, ← BitVec.add_assoc] using he

  · apply calleeSavedRegistersUnchanged_of_agreesExcept ag
    intro register hregister
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hregister
    rcases hregister with rfl | rfl | rfl | rfl | rfl | rfl <;> simp [prepareChanges] <;> decide +kernel

end Sha3.Proofs.Wrapper.Finish.Plain
