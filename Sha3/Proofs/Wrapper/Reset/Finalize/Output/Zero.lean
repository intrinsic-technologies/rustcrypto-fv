import Sha3.Proofs.Wrapper.Reset.Finalize.Output
import Sha3.Proofs.Wrapper.Finish.Plain.Prepare

namespace Sha3.Proofs.Wrapper.Reset.Output.Zero

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

abbrev zeroCount := Finish.Plain.zeroCount
abbrev zeroWidth := Finish.Plain.zeroWidth

def storeOffset (v : Variant) (i : Nat) : Nat :=
  tempOffset v + Finish.Plain.zeroOffset v i

def zeroPC (v : Variant) (mode : Mode) (keccak : Bool) (i : Nat) : BitVec 64 :=
  (mode.entry v keccak).entryAddress + BitVec.ofNat 64
    (Output.zeroOffset v + 9 * i - (if v = .sha224 ∧ 0 < i then 1 else 0) +
      (if v = .sha512 then 3 * min i 3 else 0))

def prepareChanges (initial : RamState) (v : Variant) (mode : Mode)
    (keccak : Bool := false) : List Component :=
  [.rip] ++ (List.range (zeroCount v)).map
    (fun i ↦ .mem (frameBase initial v mode keccak + BitVec.ofNat 64 (storeOffset v i))
      (zeroWidth v i))

theorem prepareChanges_noRsp (initial : RamState) (v : Variant) (mode : Mode) (keccak : Bool := false) :
    Component.reg 4 ∉ prepareChanges initial v mode keccak := by simp [prepareChanges]

theorem prepareChanges_cover {initial : RamState} {v : Variant} {keccak : Bool} {mode : Mode} {c : Component}
    (hc : c ∈ prepareChanges initial v mode keccak) {address : BitVec 64} (ha : c.Covers address) :
    ∃ i < (tempOffset v + v.digestBytes), address = frameBase initial v mode keccak + BitVec.ofNat 64 i := by
  simp only [prepareChanges, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_map, List.mem_range] at hc
  rcases hc with (rfl) | ⟨i, hi, rfl⟩
  all_goals try exact ha.elim
  obtain ⟨j, hj, rfl⟩ := ha
  refine ⟨storeOffset v i + j, ?_, ?_⟩
  · have h : ∀ i : Fin (zeroCount v), storeOffset v i + zeroWidth v i ≤ (tempOffset v + v.digestBytes) := by
      cases v <;> decide +kernel
    have hh : storeOffset v i + zeroWidth v i ≤ (tempOffset v + v.digestBytes) := h ⟨i, hi⟩
    omega
  · rw [BitVec.add_assoc, BitVec.ofNat_add]

theorem prepareChanges_writes {initial : RamState} {v : Variant} {keccak : Bool} {mode : Mode}
    (hmode : mode = .finalizeFixedReset ∨ mode = .digestFinalizeReset)
    (hs : Stack.Valid initial (mode.entry v keccak).minStackBytes) :
    WritesWithin (prepareChanges initial v mode keccak)
      #v[Stack.region initial (mode.entry v keccak).minStackBytes] := by
  intro c hc a ha
  obtain ⟨i, hi, rfl⟩ := prepareChanges_cover hc ha
  refine ⟨_, Vector.mem_iff_getElem.mpr ⟨0, by decide, rfl⟩, ?_⟩
  apply frameAddress_contains hs (by rw [Mode.stackBudget mode v keccak]; omega)
  have h : (tempOffset v + v.digestBytes) ≤ mode.frameSize v keccak := by rcases hmode with rfl | rfl <;> cases keccak <;> cases v <;> decide +kernel
  omega

private theorem prepareAdvance [bindings : Bindings] {initial s : RamState} {v : Variant} {keccak : Bool} {mode : Mode}
    {inputs : Array Input} {split : Nat} {p : BitVec 64} {bytes : List UInt8}
    {pre : RamState → Prop} {effect : RamState → Effect}
    (hmode : mode = .finalizeFixedReset ∨ mode = .digestFinalizeReset)
    (hCall : ValidInvocation bindings v mode initial inputs split keccak)
    (step : StepEffect pre (codeRange p bytes) effect) (image : ImageAt p bytes)
    (frame : ∀ c ∈ (effect s).components, c ∈ prepareChanges initial v mode keccak)
    (inv : Invariant initial v mode s keccak) (hs : stackPtr s = frameBase initial v mode keccak)
    (hp : pre s) :
    ∃ t, Advances (returnBoundary initial) 1 s t ∧ Invariant initial v mode t keccak ∧
      stackPtr t = frameBase initial v mode keccak ∧ (effect s).Holds s t ∧
      AgreesExcept (prepareChanges initial v mode keccak) s t := by
  obtain ⟨t, ht, hr, he⟩ := step s inv.ready (image.code inv.loaded) hp
  have ha := he.agrees.mono frame
  have htsp : stackPtr t = frameBase initial v mode keccak :=
    (ha.read (r := 4) (n := 64) (prepareChanges_noRsp initial v mode keccak)).trans hs
  refine ⟨t, Advances.of_step ht (.inr ?_), inv.of_agreesExcept hCall hr ha ?_ (by simp [prepareChanges]), htsp, he, ha⟩
  · change stackPtr t ≠ _
    rw [htsp]
    rw [frameBase]
    exact Finish.stackSub_ne_returnBoundary initial _ (by rcases hmode with rfl | rfl <;> cases keccak <;> cases v <;> decide +kernel)
  · intro c hc a hcover
    obtain ⟨region, hregion, hcontains⟩ := prepareChanges_writes hmode hCall.stackAvailable c hc a hcover
    have heq : region = Stack.region initial (mode.entry v keccak).minStackBytes := by simpa using hregion
    exact ⟨_, stack_mem_writeRegions initial v mode keccak, heq ▸ hcontains⟩


private theorem store_advance [bindings : Bindings] {initial s : RamState} {v : Variant} {keccak : Bool} {mode : Mode}
    {inputs : Array Input} {split : Nat} {p : BitVec 64} {bytes : List UInt8}
    {n len offset : Nat} {address : RamState → BitVec 64} {value : RamState → BitVec n}
    (hmode : mode = .finalizeFixedReset ∨ mode = .digestFinalizeReset)
    (hCall : ValidInvocation bindings v mode initial inputs split keccak)
    (step : StepEffect (StorePreReadable p address (n / 8)) (codeRange p bytes)
      (storeEffect p len address value)) (image : ImageAt p bytes)
    (hm : Component.mem (frameBase initial v mode keccak + BitVec.ofNat 64 offset) (n / 8) ∈
      prepareChanges initial v mode keccak)
    (ha : address s = stackPtr s + BitVec.ofNat 64 offset)
    (hrange : offset + n / 8 ≤ mode.frameSize v keccak + 8)
    (inv : Invariant initial v mode s keccak) (hs : stackPtr s = frameBase initial v mode keccak)
    (hp : s.RIP = p) :
    ∃ t, Advances (returnBoundary initial) 1 s t ∧ Invariant initial v mode t keccak ∧
      stackPtr t = frameBase initial v mode keccak ∧ t.RIP = p + BitVec.ofNat 64 len ∧
      AgreesExcept (prepareChanges initial v mode keccak) s t := by
  have addr : address s = frameBase initial v mode keccak + BitVec.ofNat 64 offset := ha.trans (congrArg (· + BitVec.ofNat 64 offset) hs)
  have pre : StorePreReadable p address (n / 8) s := by
    refine ⟨⟨hp, addr ▸ inv.frameReadable hCall.stackAvailable hrange⟩, ?_⟩
    intro i hi ht
    have ⟨j, hj, he⟩ := prepareChanges_cover hm (address := address s + BitVec.ofNat 64 i)
      (by rw [addr]; exact ⟨i, hi, rfl⟩)
    apply writeRegions_avoid hCall _ (stack_mem_writeRegions initial v mode keccak) _ _ (.inr ht)
    rw [he]
    apply frameAddress_contains hCall.stackAvailable (by rw [Mode.stackBudget mode v keccak]; omega)
    have hd : (tempOffset v + v.digestBytes) ≤ mode.frameSize v keccak := by rcases hmode with rfl | rfl <;> cases keccak <;> cases v <;> decide +kernel
    omega
  obtain ⟨t, ht, it, st, et, agt⟩ := prepareAdvance hmode hCall step image (by
    simp only [storeEffect_components, List.mem_cons, List.not_mem_nil, or_false]
    intro c hc
    rcases hc with rfl | rfl
    · simpa only [addr] using hm
    · simp [prepareChanges]) inv hs pre
  exact ⟨t, ht, it, st, et.rip, agt⟩



theorem zero_step [bindings : Bindings] {initial s : RamState} {v : Variant}
    {mode : Mode} {keccak : Bool} {inputs : Array Input} {split i : Nat}
    (hm : mode = .finalizeFixedReset ∨ mode = .digestFinalizeReset)
    (hCall : ValidInvocation bindings v mode initial inputs split keccak)
    (inv : Invariant initial v mode s keccak)
    (hs : stackPtr s = frameBase initial v mode keccak)
    (hp : s.RIP = zeroPC v mode keccak i) (hi : i < zeroCount v) :
    ∃ t, Advances (returnBoundary initial) 1 s t ∧ Invariant initial v mode t keccak ∧
      stackPtr t = frameBase initial v mode keccak ∧ t.RIP = zeroPC v mode keccak (i + 1) ∧
      AgreesExcept (prepareChanges initial v mode keccak) s t := by
  cases v
  case sha224 =>
    have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by change i < 4 at hi; omega
    rcases hi' with rfl | rfl | rfl | rfl
    · obtain ⟨t, ht, it, st, pt, ag⟩ := store_advance (n := 32) hm hCall
        (mov_m32_imm32_effect_step_of_readable (zeroPC .sha224 mode keccak 0) (.sib 4 none 0 (.d8 80)) (by decide +kernel) (by decide +kernel) (by decide +kernel) 0)
        (by rcases hm with rfl | rfl <;> cases keccak <;> unfold ImageAt <;> decide +kernel)
        (offset := 80) (by simp [prepareChanges, zeroCount, storeOffset, zeroWidth,
          Finish.Plain.zeroCount, Finish.Plain.zeroOffset, Finish.Plain.digestOffset, Finish.Plain.zeroWidth,
          tempOffset, List.range_succ])
        (by rfl) (by rcases hm with rfl | rfl <;> cases keccak <;> decide +kernel) inv hs hp
      exact ⟨t, ht, it, st, pt.trans (by
        rcases hm with rfl | rfl <;> cases keccak <;> decide +kernel), ag⟩
    · obtain ⟨t, ht, it, st, pt, ag⟩ := store_advance (n := 64) hm hCall
        (mov_m64_imm32_effect_step_of_readable (zeroPC .sha224 mode keccak 1) 0x48 (by unfold RexWPrefix; decide +kernel)
          (.sib 4 none 0 (.d8 72)) (by decide +kernel) (by decide +kernel) (by decide +kernel) 0)
        (by rcases hm with rfl | rfl <;> cases keccak <;> unfold ImageAt <;> decide +kernel)
        (offset := 72) (by simp [prepareChanges, zeroCount, storeOffset, zeroWidth,
          Finish.Plain.zeroCount, Finish.Plain.zeroOffset, Finish.Plain.digestOffset, Finish.Plain.zeroWidth,
          tempOffset, List.range_succ])
        (by rfl) (by rcases hm with rfl | rfl <;> cases keccak <;> decide +kernel) inv hs hp
      exact ⟨t, ht, it, st, pt.trans (by
        rcases hm with rfl | rfl <;> cases keccak <;> decide +kernel), ag⟩
    · obtain ⟨t, ht, it, st, pt, ag⟩ := store_advance (n := 64) hm hCall
        (mov_m64_imm32_effect_step_of_readable (zeroPC .sha224 mode keccak 2) 0x48 (by unfold RexWPrefix; decide +kernel)
          (.sib 4 none 0 (.d8 64)) (by decide +kernel) (by decide +kernel) (by decide +kernel) 0)
        (by rcases hm with rfl | rfl <;> cases keccak <;> unfold ImageAt <;> decide +kernel)
        (offset := 64) (by simp [prepareChanges, zeroCount, storeOffset, zeroWidth,
          Finish.Plain.zeroCount, Finish.Plain.zeroOffset, Finish.Plain.digestOffset, Finish.Plain.zeroWidth,
          tempOffset, List.range_succ])
        (by rfl) (by rcases hm with rfl | rfl <;> cases keccak <;> decide +kernel) inv hs hp
      exact ⟨t, ht, it, st, pt.trans (by
        rcases hm with rfl | rfl <;> cases keccak <;> decide +kernel), ag⟩
    · obtain ⟨t, ht, it, st, pt, ag⟩ := store_advance (n := 64) hm hCall
        (mov_m64_imm32_effect_step_of_readable (zeroPC .sha224 mode keccak 3) 0x48 (by unfold RexWPrefix; decide +kernel)
          (.sib 4 none 0 (.d8 56)) (by decide +kernel) (by decide +kernel) (by decide +kernel) 0)
        (by rcases hm with rfl | rfl <;> cases keccak <;> unfold ImageAt <;> decide +kernel)
        (offset := 56) (by simp [prepareChanges, zeroCount, storeOffset, zeroWidth,
          Finish.Plain.zeroCount, Finish.Plain.zeroOffset, Finish.Plain.digestOffset, Finish.Plain.zeroWidth,
          tempOffset, List.range_succ])
        (by rfl) (by rcases hm with rfl | rfl <;> cases keccak <;> decide +kernel) inv hs hp
      exact ⟨t, ht, it, st, pt.trans (by
        rcases hm with rfl | rfl <;> cases keccak <;> decide +kernel), ag⟩
  case sha256 =>
    have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by change i < 4 at hi; omega
    rcases hi' with rfl | rfl | rfl | rfl
    · obtain ⟨t, ht, it, st, pt, ag⟩ := store_advance (n := 64) hm hCall
        (mov_m64_imm32_effect_step_of_readable (zeroPC .sha256 mode keccak 0) 0x48 (by unfold RexWPrefix; decide +kernel)
          (.sib 4 none 0 (.d8 80)) (by decide +kernel) (by decide +kernel) (by decide +kernel) 0)
        (by rcases hm with rfl | rfl <;> cases keccak <;> unfold ImageAt <;> decide +kernel)
        (offset := 80) (by simp [prepareChanges, zeroCount, storeOffset, zeroWidth,
          Finish.Plain.zeroCount, Finish.Plain.zeroOffset, Finish.Plain.digestOffset, Finish.Plain.zeroWidth,
          tempOffset, List.range_succ])
        (by rfl) (by rcases hm with rfl | rfl <;> cases keccak <;> decide +kernel) inv hs hp
      exact ⟨t, ht, it, st, pt.trans (by
        rcases hm with rfl | rfl <;> cases keccak <;> decide +kernel), ag⟩
    · obtain ⟨t, ht, it, st, pt, ag⟩ := store_advance (n := 64) hm hCall
        (mov_m64_imm32_effect_step_of_readable (zeroPC .sha256 mode keccak 1) 0x48 (by unfold RexWPrefix; decide +kernel)
          (.sib 4 none 0 (.d8 72)) (by decide +kernel) (by decide +kernel) (by decide +kernel) 0)
        (by rcases hm with rfl | rfl <;> cases keccak <;> unfold ImageAt <;> decide +kernel)
        (offset := 72) (by simp [prepareChanges, zeroCount, storeOffset, zeroWidth,
          Finish.Plain.zeroCount, Finish.Plain.zeroOffset, Finish.Plain.digestOffset, Finish.Plain.zeroWidth,
          tempOffset, List.range_succ])
        (by rfl) (by rcases hm with rfl | rfl <;> cases keccak <;> decide +kernel) inv hs hp
      exact ⟨t, ht, it, st, pt.trans (by
        rcases hm with rfl | rfl <;> cases keccak <;> decide +kernel), ag⟩
    · obtain ⟨t, ht, it, st, pt, ag⟩ := store_advance (n := 64) hm hCall
        (mov_m64_imm32_effect_step_of_readable (zeroPC .sha256 mode keccak 2) 0x48 (by unfold RexWPrefix; decide +kernel)
          (.sib 4 none 0 (.d8 64)) (by decide +kernel) (by decide +kernel) (by decide +kernel) 0)
        (by rcases hm with rfl | rfl <;> cases keccak <;> unfold ImageAt <;> decide +kernel)
        (offset := 64) (by simp [prepareChanges, zeroCount, storeOffset, zeroWidth,
          Finish.Plain.zeroCount, Finish.Plain.zeroOffset, Finish.Plain.digestOffset, Finish.Plain.zeroWidth,
          tempOffset, List.range_succ])
        (by rfl) (by rcases hm with rfl | rfl <;> cases keccak <;> decide +kernel) inv hs hp
      exact ⟨t, ht, it, st, pt.trans (by
        rcases hm with rfl | rfl <;> cases keccak <;> decide +kernel), ag⟩
    · obtain ⟨t, ht, it, st, pt, ag⟩ := store_advance (n := 64) hm hCall
        (mov_m64_imm32_effect_step_of_readable (zeroPC .sha256 mode keccak 3) 0x48 (by unfold RexWPrefix; decide +kernel)
          (.sib 4 none 0 (.d8 56)) (by decide +kernel) (by decide +kernel) (by decide +kernel) 0)
        (by rcases hm with rfl | rfl <;> cases keccak <;> unfold ImageAt <;> decide +kernel)
        (offset := 56) (by simp [prepareChanges, zeroCount, storeOffset, zeroWidth,
          Finish.Plain.zeroCount, Finish.Plain.zeroOffset, Finish.Plain.digestOffset, Finish.Plain.zeroWidth,
          tempOffset, List.range_succ])
        (by rfl) (by rcases hm with rfl | rfl <;> cases keccak <;> decide +kernel) inv hs hp
      exact ⟨t, ht, it, st, pt.trans (by
        rcases hm with rfl | rfl <;> cases keccak <;> decide +kernel), ag⟩
  case sha384 =>
    have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 := by change i < 6 at hi; omega
    rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨t, ht, it, st, pt, ag⟩ := store_advance (n := 64) hm hCall
        (mov_m64_imm32_effect_step_of_readable (zeroPC .sha384 mode keccak 0) 0x48 (by unfold RexWPrefix; decide +kernel)
          (.sib 4 none 0 (.d8 112)) (by decide +kernel) (by decide +kernel) (by decide +kernel) 0)
        (by rcases hm with rfl | rfl <;> cases keccak <;> unfold ImageAt <;> decide +kernel)
        (offset := 112) (by simp [prepareChanges, zeroCount, storeOffset, zeroWidth,
          Finish.Plain.zeroCount, Finish.Plain.zeroOffset, Finish.Plain.digestOffset, Finish.Plain.zeroWidth,
          tempOffset, List.range_succ])
        (by rfl) (by rcases hm with rfl | rfl <;> cases keccak <;> decide +kernel) inv hs hp
      exact ⟨t, ht, it, st, pt.trans (by
        rcases hm with rfl | rfl <;> cases keccak <;> decide +kernel), ag⟩
    · obtain ⟨t, ht, it, st, pt, ag⟩ := store_advance (n := 64) hm hCall
        (mov_m64_imm32_effect_step_of_readable (zeroPC .sha384 mode keccak 1) 0x48 (by unfold RexWPrefix; decide +kernel)
          (.sib 4 none 0 (.d8 104)) (by decide +kernel) (by decide +kernel) (by decide +kernel) 0)
        (by rcases hm with rfl | rfl <;> cases keccak <;> unfold ImageAt <;> decide +kernel)
        (offset := 104) (by simp [prepareChanges, zeroCount, storeOffset, zeroWidth,
          Finish.Plain.zeroCount, Finish.Plain.zeroOffset, Finish.Plain.digestOffset, Finish.Plain.zeroWidth,
          tempOffset, List.range_succ])
        (by rfl) (by rcases hm with rfl | rfl <;> cases keccak <;> decide +kernel) inv hs hp
      exact ⟨t, ht, it, st, pt.trans (by
        rcases hm with rfl | rfl <;> cases keccak <;> decide +kernel), ag⟩
    · obtain ⟨t, ht, it, st, pt, ag⟩ := store_advance (n := 64) hm hCall
        (mov_m64_imm32_effect_step_of_readable (zeroPC .sha384 mode keccak 2) 0x48 (by unfold RexWPrefix; decide +kernel)
          (.sib 4 none 0 (.d8 96)) (by decide +kernel) (by decide +kernel) (by decide +kernel) 0)
        (by rcases hm with rfl | rfl <;> cases keccak <;> unfold ImageAt <;> decide +kernel)
        (offset := 96) (by simp [prepareChanges, zeroCount, storeOffset, zeroWidth,
          Finish.Plain.zeroCount, Finish.Plain.zeroOffset, Finish.Plain.digestOffset, Finish.Plain.zeroWidth,
          tempOffset, List.range_succ])
        (by rfl) (by rcases hm with rfl | rfl <;> cases keccak <;> decide +kernel) inv hs hp
      exact ⟨t, ht, it, st, pt.trans (by
        rcases hm with rfl | rfl <;> cases keccak <;> decide +kernel), ag⟩
    · obtain ⟨t, ht, it, st, pt, ag⟩ := store_advance (n := 64) hm hCall
        (mov_m64_imm32_effect_step_of_readable (zeroPC .sha384 mode keccak 3) 0x48 (by unfold RexWPrefix; decide +kernel)
          (.sib 4 none 0 (.d8 88)) (by decide +kernel) (by decide +kernel) (by decide +kernel) 0)
        (by rcases hm with rfl | rfl <;> cases keccak <;> unfold ImageAt <;> decide +kernel)
        (offset := 88) (by simp [prepareChanges, zeroCount, storeOffset, zeroWidth,
          Finish.Plain.zeroCount, Finish.Plain.zeroOffset, Finish.Plain.digestOffset, Finish.Plain.zeroWidth,
          tempOffset, List.range_succ])
        (by rfl) (by rcases hm with rfl | rfl <;> cases keccak <;> decide +kernel) inv hs hp
      exact ⟨t, ht, it, st, pt.trans (by
        rcases hm with rfl | rfl <;> cases keccak <;> decide +kernel), ag⟩
    · obtain ⟨t, ht, it, st, pt, ag⟩ := store_advance (n := 64) hm hCall
        (mov_m64_imm32_effect_step_of_readable (zeroPC .sha384 mode keccak 4) 0x48 (by unfold RexWPrefix; decide +kernel)
          (.sib 4 none 0 (.d8 80)) (by decide +kernel) (by decide +kernel) (by decide +kernel) 0)
        (by rcases hm with rfl | rfl <;> cases keccak <;> unfold ImageAt <;> decide +kernel)
        (offset := 80) (by simp [prepareChanges, zeroCount, storeOffset, zeroWidth,
          Finish.Plain.zeroCount, Finish.Plain.zeroOffset, Finish.Plain.digestOffset, Finish.Plain.zeroWidth,
          tempOffset, List.range_succ])
        (by rfl) (by rcases hm with rfl | rfl <;> cases keccak <;> decide +kernel) inv hs hp
      exact ⟨t, ht, it, st, pt.trans (by
        rcases hm with rfl | rfl <;> cases keccak <;> decide +kernel), ag⟩
    · obtain ⟨t, ht, it, st, pt, ag⟩ := store_advance (n := 64) hm hCall
        (mov_m64_imm32_effect_step_of_readable (zeroPC .sha384 mode keccak 5) 0x48 (by unfold RexWPrefix; decide +kernel)
          (.sib 4 none 0 (.d8 72)) (by decide +kernel) (by decide +kernel) (by decide +kernel) 0)
        (by rcases hm with rfl | rfl <;> cases keccak <;> unfold ImageAt <;> decide +kernel)
        (offset := 72) (by simp [prepareChanges, zeroCount, storeOffset, zeroWidth,
          Finish.Plain.zeroCount, Finish.Plain.zeroOffset, Finish.Plain.digestOffset, Finish.Plain.zeroWidth,
          tempOffset, List.range_succ])
        (by rfl) (by rcases hm with rfl | rfl <;> cases keccak <;> decide +kernel) inv hs hp
      exact ⟨t, ht, it, st, pt.trans (by
        rcases hm with rfl | rfl <;> cases keccak <;> decide +kernel), ag⟩
  case sha512 =>
    have hi' : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by change i < 8 at hi; omega
    rcases hi' with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · obtain ⟨t, ht, it, st, pt, ag⟩ := store_advance (n := 64) hm hCall
        (mov_m64_imm32_effect_step_of_readable (zeroPC .sha512 mode keccak 0) 0x48 (by unfold RexWPrefix; decide +kernel)
          (.sib 4 none 0 (.d32 144)) (by decide +kernel) (by decide +kernel) (by decide +kernel) 0)
        (by rcases hm with rfl | rfl <;> cases keccak <;> unfold ImageAt <;> decide +kernel)
        (offset := 144) (by simp [prepareChanges, zeroCount, storeOffset, zeroWidth,
          Finish.Plain.zeroCount, Finish.Plain.zeroOffset, Finish.Plain.digestOffset, Finish.Plain.zeroWidth,
          tempOffset, List.range_succ])
        (by rfl) (by rcases hm with rfl | rfl <;> cases keccak <;> decide +kernel) inv hs hp
      exact ⟨t, ht, it, st, pt.trans (by
        rcases hm with rfl | rfl <;> cases keccak <;> decide +kernel), ag⟩
    · obtain ⟨t, ht, it, st, pt, ag⟩ := store_advance (n := 64) hm hCall
        (mov_m64_imm32_effect_step_of_readable (zeroPC .sha512 mode keccak 1) 0x48 (by unfold RexWPrefix; decide +kernel)
          (.sib 4 none 0 (.d32 136)) (by decide +kernel) (by decide +kernel) (by decide +kernel) 0)
        (by rcases hm with rfl | rfl <;> cases keccak <;> unfold ImageAt <;> decide +kernel)
        (offset := 136) (by simp [prepareChanges, zeroCount, storeOffset, zeroWidth,
          Finish.Plain.zeroCount, Finish.Plain.zeroOffset, Finish.Plain.digestOffset, Finish.Plain.zeroWidth,
          tempOffset, List.range_succ])
        (by rfl) (by rcases hm with rfl | rfl <;> cases keccak <;> decide +kernel) inv hs hp
      exact ⟨t, ht, it, st, pt.trans (by
        rcases hm with rfl | rfl <;> cases keccak <;> decide +kernel), ag⟩
    · obtain ⟨t, ht, it, st, pt, ag⟩ := store_advance (n := 64) hm hCall
        (mov_m64_imm32_effect_step_of_readable (zeroPC .sha512 mode keccak 2) 0x48 (by unfold RexWPrefix; decide +kernel)
          (.sib 4 none 0 (.d32 128)) (by decide +kernel) (by decide +kernel) (by decide +kernel) 0)
        (by rcases hm with rfl | rfl <;> cases keccak <;> unfold ImageAt <;> decide +kernel)
        (offset := 128) (by simp [prepareChanges, zeroCount, storeOffset, zeroWidth,
          Finish.Plain.zeroCount, Finish.Plain.zeroOffset, Finish.Plain.digestOffset, Finish.Plain.zeroWidth,
          tempOffset, List.range_succ])
        (by rfl) (by rcases hm with rfl | rfl <;> cases keccak <;> decide +kernel) inv hs hp
      exact ⟨t, ht, it, st, pt.trans (by
        rcases hm with rfl | rfl <;> cases keccak <;> decide +kernel), ag⟩
    · obtain ⟨t, ht, it, st, pt, ag⟩ := store_advance (n := 64) hm hCall
        (mov_m64_imm32_effect_step_of_readable (zeroPC .sha512 mode keccak 3) 0x48 (by unfold RexWPrefix; decide +kernel)
          (.sib 4 none 0 (.d8 120)) (by decide +kernel) (by decide +kernel) (by decide +kernel) 0)
        (by rcases hm with rfl | rfl <;> cases keccak <;> unfold ImageAt <;> decide +kernel)
        (offset := 120) (by simp [prepareChanges, zeroCount, storeOffset, zeroWidth,
          Finish.Plain.zeroCount, Finish.Plain.zeroOffset, Finish.Plain.digestOffset, Finish.Plain.zeroWidth,
          tempOffset, List.range_succ])
        (by rfl) (by rcases hm with rfl | rfl <;> cases keccak <;> decide +kernel) inv hs hp
      exact ⟨t, ht, it, st, pt.trans (by
        rcases hm with rfl | rfl <;> cases keccak <;> decide +kernel), ag⟩
    · obtain ⟨t, ht, it, st, pt, ag⟩ := store_advance (n := 64) hm hCall
        (mov_m64_imm32_effect_step_of_readable (zeroPC .sha512 mode keccak 4) 0x48 (by unfold RexWPrefix; decide +kernel)
          (.sib 4 none 0 (.d8 112)) (by decide +kernel) (by decide +kernel) (by decide +kernel) 0)
        (by rcases hm with rfl | rfl <;> cases keccak <;> unfold ImageAt <;> decide +kernel)
        (offset := 112) (by simp [prepareChanges, zeroCount, storeOffset, zeroWidth,
          Finish.Plain.zeroCount, Finish.Plain.zeroOffset, Finish.Plain.digestOffset, Finish.Plain.zeroWidth,
          tempOffset, List.range_succ])
        (by rfl) (by rcases hm with rfl | rfl <;> cases keccak <;> decide +kernel) inv hs hp
      exact ⟨t, ht, it, st, pt.trans (by
        rcases hm with rfl | rfl <;> cases keccak <;> decide +kernel), ag⟩
    · obtain ⟨t, ht, it, st, pt, ag⟩ := store_advance (n := 64) hm hCall
        (mov_m64_imm32_effect_step_of_readable (zeroPC .sha512 mode keccak 5) 0x48 (by unfold RexWPrefix; decide +kernel)
          (.sib 4 none 0 (.d8 104)) (by decide +kernel) (by decide +kernel) (by decide +kernel) 0)
        (by rcases hm with rfl | rfl <;> cases keccak <;> unfold ImageAt <;> decide +kernel)
        (offset := 104) (by simp [prepareChanges, zeroCount, storeOffset, zeroWidth,
          Finish.Plain.zeroCount, Finish.Plain.zeroOffset, Finish.Plain.digestOffset, Finish.Plain.zeroWidth,
          tempOffset, List.range_succ])
        (by rfl) (by rcases hm with rfl | rfl <;> cases keccak <;> decide +kernel) inv hs hp
      exact ⟨t, ht, it, st, pt.trans (by
        rcases hm with rfl | rfl <;> cases keccak <;> decide +kernel), ag⟩
    · obtain ⟨t, ht, it, st, pt, ag⟩ := store_advance (n := 64) hm hCall
        (mov_m64_imm32_effect_step_of_readable (zeroPC .sha512 mode keccak 6) 0x48 (by unfold RexWPrefix; decide +kernel)
          (.sib 4 none 0 (.d8 96)) (by decide +kernel) (by decide +kernel) (by decide +kernel) 0)
        (by rcases hm with rfl | rfl <;> cases keccak <;> unfold ImageAt <;> decide +kernel)
        (offset := 96) (by simp [prepareChanges, zeroCount, storeOffset, zeroWidth,
          Finish.Plain.zeroCount, Finish.Plain.zeroOffset, Finish.Plain.digestOffset, Finish.Plain.zeroWidth,
          tempOffset, List.range_succ])
        (by rfl) (by rcases hm with rfl | rfl <;> cases keccak <;> decide +kernel) inv hs hp
      exact ⟨t, ht, it, st, pt.trans (by
        rcases hm with rfl | rfl <;> cases keccak <;> decide +kernel), ag⟩
    · obtain ⟨t, ht, it, st, pt, ag⟩ := store_advance (n := 64) hm hCall
        (mov_m64_imm32_effect_step_of_readable (zeroPC .sha512 mode keccak 7) 0x48 (by unfold RexWPrefix; decide +kernel)
          (.sib 4 none 0 (.d8 88)) (by decide +kernel) (by decide +kernel) (by decide +kernel) 0)
        (by rcases hm with rfl | rfl <;> cases keccak <;> unfold ImageAt <;> decide +kernel)
        (offset := 88) (by simp [prepareChanges, zeroCount, storeOffset, zeroWidth,
          Finish.Plain.zeroCount, Finish.Plain.zeroOffset, Finish.Plain.digestOffset, Finish.Plain.zeroWidth,
          tempOffset, List.range_succ])
        (by rfl) (by rcases hm with rfl | rfl <;> cases keccak <;> decide +kernel) inv hs hp
      exact ⟨t, ht, it, st, pt.trans (by
        rcases hm with rfl | rfl <;> cases keccak <;> decide +kernel), ag⟩

theorem zero_advance [bindings : Bindings] {initial s : RamState} {v : Variant}
    {mode : Mode} {keccak : Bool} {inputs : Array Input} {split k : Nat}
    (hm : mode = .finalizeFixedReset ∨ mode = .digestFinalizeReset)
    (hCall : ValidInvocation bindings v mode initial inputs split keccak)
    (inv : Invariant initial v mode s keccak)
    (hs : stackPtr s = frameBase initial v mode keccak)
    (hp : s.RIP = zeroPC v mode keccak 0) (hk : k ≤ zeroCount v) :
    ∃ t, Advances (returnBoundary initial) k s t ∧ Invariant initial v mode t keccak ∧
      stackPtr t = frameBase initial v mode keccak ∧ t.RIP = zeroPC v mode keccak k ∧
      AgreesExcept (prepareChanges initial v mode keccak) s t := by
  induction k with
  | zero =>
    exact ⟨s, (advances_zero _ _ _).mpr rfl, inv, hs, hp, AgreesExcept.refl _ _⟩
  | succ k ih =>
    obtain ⟨u, hu, iu, su, pu, au⟩ := ih (by omega)
    obtain ⟨t, ht, it, st, pt, agt⟩ := zero_step hm hCall iu su pu (by omega)
    exact ⟨t, hu.trans ht, it, st, pt,
      (au.trans agt).mono (by intro c hc; exact (List.mem_append.mp hc).elim id id)⟩

theorem prepareChanges_saved {initial s t : RamState} {v : Variant} {mode : Mode}
    {keccak : Bool} (hm : mode = .finalizeFixedReset ∨ mode = .digestFinalizeReset)
    (saved : SavedFrame initial s mode)
    (ag : AgreesExcept (prepareChanges initial v mode keccak) s t) :
    SavedFrame initial t mode := by
  apply saved.of_localFrame (v := v) (mode := mode) (keccak := keccak) ag
  intro c hc a ha
  obtain ⟨i, hi, rfl⟩ := prepareChanges_cover hc ha
  refine ⟨8 + i, ?_, ?_⟩
  · have hb : tempOffset v + v.digestBytes + 8 * mode.pushCount false ≤
        mode.frameSize v keccak := by
      rcases hm with rfl | rfl <;> cases keccak <;> cases v <;> decide +kernel
    have hc : 8 ≤ 8 * mode.pushCount false := by
      rcases hm with rfl | rfl <;> decide +kernel
    omega
  · rw [BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.ofNat_eq_ofNat, BitVec.sub_add_cancel]

theorem prepareChanges_cover_temp {initial : RamState} {v : Variant} {mode : Mode}
    {keccak : Bool} {c : Component} (hc : c ∈ prepareChanges initial v mode keccak)
    {address : BitVec 64} (ha : c.Covers address) :
    ∃ i < v.digestBytes, address = tempPointer initial v mode keccak false + BitVec.ofNat 64 i := by
  simp only [prepareChanges, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
    List.mem_map, List.mem_range] at hc
  rcases hc with rfl | ⟨i, hi, rfl⟩
  · exact ha.elim
  obtain ⟨j, hj, rfl⟩ := ha
  refine ⟨Finish.Plain.zeroOffset v i + j, ?_, ?_⟩
  · have hb : ∀ i : Fin (zeroCount v),
        Finish.Plain.zeroOffset v i + zeroWidth v i ≤ v.digestBytes := by
      cases v <;> decide +kernel
    have h : Finish.Plain.zeroOffset v i + zeroWidth v i ≤ v.digestBytes := hb ⟨i, hi⟩
    omega
  · simp only [storeOffset, tempPointer, BitVec.ofNat_add, BitVec.add_assoc]

theorem prepareChanges_read {initial s t : RamState} {v : Variant} {mode : Mode}
    {keccak : Bool} {offset width : Nat}
    (ag : AgreesExcept (prepareChanges initial v mode keccak) s t)
    (hlo : offset + width / 8 ≤ tempOffset v ∨ tempOffset v + v.digestBytes ≤ offset)
    (hhi : offset + width / 8 < 2^64) :
    (Operand.mem (frameBase initial v mode keccak + BitVec.ofNat 64 offset) : Operand width).read t =
      (Operand.mem (frameBase initial v mode keccak + BitVec.ofNat 64 offset) : Operand width).read s := by
  apply memLoad_congr
  intro j hj
  simp only [memByte, PhysicalMemory.read]
  rw [ag.byte (by
    intro c hc hcover
    obtain ⟨i, hi, he⟩ := prepareChanges_cover_temp hc hcover
    have hd : tempOffset v + v.digestBytes ≤ 2^64 := by cases v <;> decide +kernel
    have apart := RangeApart.offsets (frameBase initial v mode keccak)
      (a := tempOffset v) (b := offset) (len := v.digestBytes) (count := width / 8)
      hd (by omega) hlo.symm
    exact apart i hi j hj he.symm)]

theorem zero_steps [bindings : Bindings] {initial s : RamState} {v : Variant}
    {mode : Mode} {keccak : Bool} {inputs : Array Input} {split : Nat}
    (hm : mode = .finalizeFixedReset ∨ mode = .digestFinalizeReset)
    (hCall : ValidInvocation bindings v mode initial inputs split keccak)
    (inv : Invariant initial v mode s keccak) (saved : SavedFrame initial s mode)
    (hs : stackPtr s = frameBase initial v mode keccak)
    (hp : s.RIP = Reset.preparePC v true keccak false mode) :
    ∃ t, Advances (returnBoundary initial) (zeroCount v) s t ∧
      Invariant initial v mode t keccak ∧ SavedFrame initial t mode ∧
      stackPtr t = frameBase initial v mode keccak ∧
      t.RIP = Output.preparePC v mode keccak false ∧
      AgreesExcept (prepareChanges initial v mode keccak) s t := by
  have hp' : s.RIP = zeroPC v mode keccak 0 := hp.trans (by
    rcases hm with rfl | rfl <;> cases v <;> cases keccak <;> decide +kernel)
  obtain ⟨t, ht, it, st, pt, ag⟩ := zero_advance hm hCall inv hs hp' (Nat.le_refl _)
  refine ⟨t, ht, it, prepareChanges_saved hm saved ag, st, pt.trans ?_, ag⟩
  rcases hm with rfl | rfl <;> cases v <;> cases keccak <;> decide +kernel

def fullPrepareChanges : List Component := [.reg 13, .reg 7, .reg 2, .reg 6, .flags, .rip]

theorem prepare_full_zero [bindings : Bindings] (mode : Mode)
    {initial s : RamState} {inputs : Array Input} {split : Nat}
    (hm : mode = .finalizeFixedReset ∨ mode = .digestFinalizeReset)
    (hCall : ValidInvocation bindings .sha256 mode initial inputs split true true)
    (inv : Invariant initial .sha256 mode s true true)
    (hp : s.RIP = fullCopyPC mode 0xa4)
    (hs : stackPtr s = frameBase initial .sha256 mode true true) :
    ∃ t, Advances (returnBoundary initial) 4 s t ∧
      Invariant initial .sha256 mode t true true ∧
      t.RIP = fullCopyPC mode 0xb6 ∧
      t.regValue .r13 = tempPointer initial .sha256 mode true true ∧
      t.regValue .rdi = tempPointer initial .sha256 mode true true ∧
      t.regValue .rdx = 200 ∧ t.regValue .rsi = 0 ∧
      AgreesExcept fullPrepareChanges s t := by
  have hsp : s.GPR[4] ≠ (returnBoundary initial).rsp := by
    change stackPtr s ≠ _
    rw [hs, frameBase]
    apply Finish.stackSub_ne_returnBoundary
    rcases hm with rfl | rfl <;> decide +kernel
  obtain ⟨a, ha, ia, spa, ea, aga⟩ := advanceNoMemory hCall
    (lea_r64_effect_step (fullCopyPC mode 0xa4) 0x4c (by unfold RexWPrefix; decide +kernel)
      5 (.sib 4 none 0 (.d32 440)) (by decide +kernel) rfl rfl)
    (by rcases hm with rfl | rfl <;> unfold ImageAt <;> decide +kernel)
    (changes := fullPrepareChanges) (by simp only [leaR64Effect_components]; decide +kernel)
    (by simp [fullPrepareChanges, Component.Covers]) (by simp [fullPrepareChanges]) inv hsp hp
  have ipa : a.RIP = fullCopyPC mode 0xac := ea.rip.trans (by
    rcases hm with rfl | rfl <;> rfl)
  have ra : a.regValue .r13 = tempPointer initial .sha256 mode true true := by
    exact ea.writes.trans (congrArg (fun p : BitVec 64 ↦ p + 440) hs)
  obtain ⟨b, hb, ib, spb, eb, agb⟩ := advanceNoMemory hCall
    (mov_r32_imm32_effect_step (fullCopyPC mode 0xac) 0xba (by decide +kernel) 200)
    (by rcases hm with rfl | rfl <;> unfold ImageAt <;> decide +kernel)
    (changes := fullPrepareChanges) (by simp only [movR32Imm32Effect_components]; decide +kernel)
    (by simp [fullPrepareChanges, Component.Covers]) (by simp [fullPrepareChanges]) ia spa ipa
  have ipb : b.RIP = fullCopyPC mode 0xb1 := eb.rip.trans (by
    rcases hm with rfl | rfl <;> rfl)
  have rb : b.regValue .r13 = tempPointer initial .sha256 mode true true :=
    (eb.agrees.read (r := 13) (n := 64) (by
      simp only [movR32Imm32Effect_components]; decide +kernel)).trans ra
  obtain ⟨c, hc, ic, spc, ec, agc⟩ := advanceNoMemory hCall
    (mov_r64_r64_effect_step (fullCopyPC mode 0xb1) 0x4c 0xef
      (by unfold RexWPrefix; decide +kernel) (by decide +kernel))
    (by rcases hm with rfl | rfl <;> unfold ImageAt <;> decide +kernel)
    (changes := fullPrepareChanges) (by simp only [movR64R64Effect_components]; decide +kernel)
    (by simp [fullPrepareChanges, Component.Covers]) (by simp [fullPrepareChanges]) ib spb ipb
  have ipc : c.RIP = fullCopyPC mode 0xb4 := ec.rip.trans (by
    rcases hm with rfl | rfl <;> rfl)
  obtain ⟨t, ht, it, _, et, agt⟩ := advanceNoMemory hCall
    (xor_r32_r32_effect_step (fullCopyPC mode 0xb4) 0xf6 (by decide +kernel))
    (by rcases hm with rfl | rfl <;> unfold ImageAt <;> decide +kernel)
    (changes := fullPrepareChanges) (by simp only [xorR32R32Effect_components]; decide +kernel)
    (by simp [fullPrepareChanges, Component.Covers]) (by simp [fullPrepareChanges]) ic spc ipc
  refine ⟨t, ha.trans (hb.trans (hc.trans ht)), it, et.rip.trans ?_, ?_, ?_, ?_, ?_,
    (((aga.trans agb).trans agc).trans agt).mono ?_⟩
  · rcases hm with rfl | rfl <;> rfl
  · exact (et.agrees.read (r := 13) (n := 64) (by
      simp only [xorR32R32Effect_components]; decide +kernel)).trans
      ((ec.agrees.read (r := 13) (n := 64) (by
        simp only [movR64R64Effect_components]; decide +kernel)).trans rb)
  · exact (et.agrees.read (r := 7) (n := 64) (by
      simp only [xorR32R32Effect_components]; decide +kernel)).trans (ec.writes.trans rb)
  · exact (et.agrees.read (r := 2) (n := 64) (by
      simp only [xorR32R32Effect_components]; decide +kernel)).trans
      ((ec.agrees.read (r := 2) (n := 64) (by
        simp only [movR64R64Effect_components]; decide +kernel)).trans eb.writes)
  · have hw := et.writes
    change t.regValue .rsi = _ at hw
    apply hw.trans
    change (((Operand.reg 6 : Operand 32).read c) ^^^
      ((Operand.reg 6 : Operand 32).read c)).setWidth 64 = (0 : BitVec 64)
    rw [BitVec.xor_self]
    rfl
  · intro q hq
    simp only [List.mem_append] at hq
    rcases hq with ((hq | hq) | hq) | hq <;> exact hq

def fullMemsetDisp (mode : Mode) : BitVec 32 :=
  (0x200188 - (fullCopyPC mode 0xb6 + 6)).setWidth 32

theorem full_zero_call [bindings : Bindings] (mode : Mode)
    {initial s : RamState} {inputs : Array Input} {split : Nat}
    (hm : mode = .finalizeFixedReset ∨ mode = .digestFinalizeReset)
    (hCall : ValidInvocation bindings .sha256 mode initial inputs split true true)
    (inv : Invariant initial .sha256 mode s true true)
    (hp : s.RIP = fullCopyPC mode 0xb6)
    (hs : stackPtr s = frameBase initial .sha256 mode true true) :
    ∃ t, Advances (returnBoundary initial) 1 s t ∧
      Invariant initial .sha256 mode t true true ∧
      t.RIP = 0x106a20 ∧
      stackPtr t = frameBase initial .sha256 mode true true - 8 ∧
      stackTop t = Output.preparePC .sha256 mode true true ∧
      AgreesExcept [.reg 4, .mem (frameBase initial .sha256 mode true true - 8) 8, .rip] s t := by
  obtain ⟨t, ht, it, pt, st, rt, ag⟩ := initial_memset_call
    (returnBoundary initial) (fullCopyPC mode 0xb6) (fullMemsetDisp mode) hCall
    (by rw [Mode.stackBudget mode .sha256 true true]; omega)
    (by rcases hm with rfl | rfl <;> unfold ImageAt <;> decide +kernel)
    (by rcases hm with rfl | rfl <;> decide +kernel) inv hp hs
    (by
      rw [frameBase, BitVec.sub_sub]
      apply Finish.stackSub_ne_returnBoundary
      rcases hm with rfl | rfl <;> decide +kernel)
  exact ⟨t, ht, it, pt, st, rt.trans (by
    rcases hm with rfl | rfl <;> rfl), ag⟩

theorem full_zero_pre [bindings : Bindings] (mode : Mode)
    {initial s : RamState} {inputs : Array Input} {split : Nat}
    (hm : mode = .finalizeFixedReset ∨ mode = .digestFinalizeReset)
    (hCall : ValidInvocation bindings .sha256 mode initial inputs split true true)
    (inv : Invariant initial .sha256 mode s true true)
    (hp : s.RIP = 0x106a20)
    (hs : stackPtr s = frameBase initial .sha256 mode true true - 8)
    (hr : stackTop s = Output.preparePC .sha256 mode true true)
    (hd : s.regValue .rdi = tempPointer initial .sha256 mode true true)
    (hl : s.regValue .rdx = 200) (hz : s.regValue .rsi = 0) :
    Memset.Pre (returnBoundary initial) s 200 := by
  have size : mode.frameSize .sha256 true true = 696 := by
    rcases hm with rfl | rfl <;> rfl
  have budget : 704 ≤ (mode.entry .sha256 true true).minStackBytes := by
    rw [Mode.stackBudget mode .sha256 true true, size]; omega
  have ptr : tempPointer initial .sha256 mode true true = initial.regValue .rsp - 256 := by
    simp only [tempPointer, tempOffset, ↓reduceIte, frameBase, size]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have stk : stackPtr s = initial.regValue .rsp - 704 := by
    rw [hs, frameBase, size]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have ptrNat : (tempPointer initial .sha256 mode true true).toNat =
      (initial.regValue .rsp).toNat - 256 := by
    rw [ptr]
    exact stack_sub_toNat (offset := 256) hCall.stackAvailable.2.2.1 (by omega)
  have stkNat : (stackPtr s).toNat = (initial.regValue .rsp).toNat - 704 := by
    rw [stk]
    exact stack_sub_toNat hCall.stackAvailable.2.2.1 budget
  have upper : (initial.regValue .rsp).toNat < 2^32 := by
    have h := stack_sub_low hCall.stackAvailable budget
    change (initial.regValue .rsp - BitVec.ofNat 64 704).toNat + 704 < 2^32 at h
    rw [stack_sub_toNat hCall.stackAvailable.2.2.1 budget] at h
    have low := hCall.stackAvailable.2.2.1
    change (mode.entry .sha256 true true).minStackBytes ≤ (initial.regValue .rsp).toNat at low
    omega
  have lower := hCall.stackAvailable.2.2.1
  have readable {offset count : Nat} (hb : offset ≤ (mode.entry .sha256 true true).minStackBytes)
      (hc : count ≤ offset) :
      MemReadable s (initial.regValue .rsp - BitVec.ofNat 64 offset) count := by
    have low := stack_sub_low hCall.stackAvailable hb
    change (initial.regValue .rsp - BitVec.ofNat 64 offset).toNat + offset < 2^32 at low
    refine ⟨by omega, ?_⟩
    intro i hi
    obtain ⟨b, hb⟩ := stack_sub_allocated hCall.stackAvailable hb (by omega : i < offset)
    exact inv.grows _ (by rw [hb]; rfl)
  have subset : ∀ address : BitVec 64,
      (MemoryRegion.mk (tempPointer initial .sha256 mode true true).toNat 200).Contains address.toNat →
      (Stack.region initial (mode.entry .sha256 true true).minStackBytes).Contains address.toNat := by
    intro address ha
    change _ ≤ address.toNat ∧ address.toNat < _ + 200 at ha
    rw [ptrNat] at ha
    dsimp only at ha
    simp only [Stack.region, Stack.returnAddressBytes, MemoryRegion.Contains]
    change (mode.entry .sha256 true true).minStackBytes ≤ (initial.regValue .rsp).toNat at lower
    omega
  refine ⟨hp, hl, hz, ?_, inv.direction, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change (s.regValue .rdi).toNat % 8 = 0
    rw [hd, ptrNat]
    have align := hCall.stackAvailable.2.2.2
    change (initial.regValue .rsp).toNat % 16 = 8 at align
    change (mode.entry .sha256 true true).minStackBytes ≤ (initial.regValue .rsp).toNat at lower
    omega
  · change MemReadable s (s.regValue .rdi) 200
    rw [hd, ptr]
    exact readable (offset := 256) (by omega) (by omega)
  · change (MemoryRegion.mk (s.regValue .rdi).toNat 200).Avoids InPageTables
    rw [hd]
    intro address ha ht
    exact writeRegions_avoid hCall _ (stack_mem_writeRegions initial .sha256 mode true true)
      address (subset address ha) (.inr ht)
  · change (MemoryRegion.mk (s.regValue .rdi).toNat 200).Avoids InProgram
    rw [hd]
    intro address ha ht
    exact writeRegions_avoid hCall _ (stack_mem_writeRegions initial .sha256 mode true true)
      address (subset address ha) (.inl ht)
  · rw [stk]
    exact readable (offset := 704) budget (by omega)
  · rw [hr]
    rcases hm with rfl | rfl <;> decide +kernel
  · change RangeApart (s.regValue .rdi) 200 (stackPtr s) 8
    rw [hd]
    apply RangeApart.of_toNat
    · rw [ptrNat]
      change (initial.regValue .rsp).toNat < 2^32 at upper
      omega
    · rw [stkNat]
      change (initial.regValue .rsp).toNat < 2^32 at upper
      omega
    · rw [ptrNat, stkNat]
      change (mode.entry .sha256 true true).minStackBytes ≤ (initial.regValue .rsp).toNat at lower
      exact .inr (by omega)
  · rw [stk]
    exact Finish.stackSub_ne_returnBoundary initial 704 (by decide +kernel)
  · right
    rw [hs, BitVec.sub_add_cancel, frameBase, size]
    exact Finish.stackSub_ne_returnBoundary initial 696 (by decide +kernel)

def fullChanges (initial : RamState) (mode : Mode) : List Component :=
  fullPrepareChanges ++
    [.reg 4, .mem (frameBase initial .sha256 mode true true - 8) 8, .rip] ++
    Memset.clobbers (tempPointer initial .sha256 mode true true) 200

theorem fullChanges_local (initial : RamState) (mode : Mode)
    (hm : mode = .finalizeFixedReset ∨ mode = .digestFinalizeReset) :
    ∀ c ∈ fullChanges initial mode, ∀ address, c.Covers address →
      (Component.mem (frameBase initial .sha256 mode true true - 8)
        (mode.frameSize .sha256 true true - (8 * mode.pushCount true - 8))).Covers address := by
  intro c hc address ha
  simp only [fullChanges, fullPrepareChanges, Memset.clobbers, List.mem_append,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with ((rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl)) |
    (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> try exact ha.elim
  · obtain ⟨i, hi, rfl⟩ := ha
    refine ⟨i, ?_, rfl⟩
    rcases hm with rfl | rfl <;> change i < 656 <;> omega
  · obtain ⟨i, hi, rfl⟩ := ha
    refine ⟨448 + i, ?_, ?_⟩
    · rcases hm with rfl | rfl <;> change 448 + i < 656 <;> omega
    · simp only [tempPointer, tempOffset, ↓reduceIte, BitVec.ofNat_add,
        BitVec.ofNat_eq_ofNat, BitVec.sub_eq_add_neg, BitVec.add_assoc]
      congr 1
      rw [← BitVec.add_assoc]
      apply congrArg (fun x : BitVec 64 ↦ x + BitVec.ofNat 64 i)
      decide +kernel

theorem full_zero_steps [bindings : Bindings] (mode : Mode)
    {initial s : RamState} {inputs : Array Input} {split : Nat}
    (hm : mode = .finalizeFixedReset ∨ mode = .digestFinalizeReset)
    (hCall : ValidInvocation bindings .sha256 mode initial inputs split true true)
    (hstride : UnitStringStride bindings)
    (inv : Invariant initial .sha256 mode s true true)
    (saved : SavedFrame initial s mode true)
    (hp : s.RIP = Reset.preparePC .sha256 true true true mode)
    (hs : stackPtr s = frameBase initial .sha256 mode true true) :
    ∃ t, Advances (returnBoundary initial) 50 s t ∧
      Invariant initial .sha256 mode t true true ∧ SavedFrame initial t mode true ∧
      t.RIP = Output.preparePC .sha256 mode true true ∧
      stackPtr t = frameBase initial .sha256 mode true true ∧
      t.regValue .r13 = tempPointer initial .sha256 mode true true ∧
      AgreesExcept (fullChanges initial mode) s t := by
  obtain ⟨a, ha, ia, pa, r13a, rda, rla, rza, aga⟩ := prepare_full_zero mode hm hCall inv
    (hp.trans (by rcases hm with rfl | rfl <;> rfl)) hs
  have sa : stackPtr a = frameBase initial .sha256 mode true true :=
    (aga.read (r := 4) (n := 64) (by simp [fullPrepareChanges])).trans hs
  obtain ⟨b, hb, ib, pb, sb, rb, agb⟩ := full_zero_call mode hm hCall ia pa sa
  have regs (r : BitVec 5) (hr : r ≠ 4) :
      (Operand.reg r : Operand 64).read b = (Operand.reg r : Operand 64).read a :=
    agb.read (by simp only [List.mem_cons, List.not_mem_nil, or_false,
      Component.reg.injEq, reduceCtorEq, or_false]; exact hr)
  have db : b.regValue .rdi = tempPointer initial .sha256 mode true true :=
    (regs 7 (by decide)).trans rda
  have pre := full_zero_pre mode hm hCall ib pb sb rb db
    ((regs 2 (by decide)).trans rla) ((regs 6 (by decide)).trans rza)
  obtain ⟨t, ht, done⟩ := Memset.memset200_steps hstride (returnBoundary initial) b ib.ready ib.code pre
  have agt : AgreesExcept (Memset.clobbers (tempPointer initial .sha256 mode true true) 200) b t := by
    simpa only [show (Operand.reg 7 : Operand 64).read b =
      tempPointer initial .sha256 mode true true from db] using done.agrees
  have ag : AgreesExcept (fullChanges initial mode) s t := (aga.trans agb).trans agt
  have it : Invariant initial .sha256 mode t true true :=
    ib.of_agreesExcept hCall done.ready agt (hd := by simp [Memset.clobbers]) (by
      apply Memset.clobbers_writesWithin
      intro i hi
      refine ⟨_, stack_mem_writeRegions initial .sha256 mode true true, ?_⟩
      simp only [tempPointer, tempOffset, ↓reduceIte, BitVec.add_assoc, ← BitVec.ofNat_add]
      apply frameAddress_contains hCall.stackAvailable
        (by rw [Mode.stackBudget mode .sha256 true true]; omega)
      rcases hm with rfl | rfl <;> change 440 + i < 704 <;> omega)
  refine ⟨t, ha.trans (hb.trans ht), it,
    saved.of_localFrame ag (fullChanges_local initial mode hm), done.rip.trans rb,
    done.rsp.trans ?_, ?_, ag⟩
  · rw [sb, BitVec.sub_add_cancel]
  · exact (agt.read (r := 13) (n := 64) (by simp [Memset.clobbers])).trans
      ((regs 13 (by decide)).trans r13a)

theorem fullChanges_read {initial s t : RamState} {mode : Mode} {offset width : Nat}
    (ag : AgreesExcept (fullChanges initial mode) s t)
    (hbefore : offset + width / 8 ≤ 440) :
    (Operand.mem (frameBase initial .sha256 mode true true + BitVec.ofNat 64 offset) : Operand width).read t =
      (Operand.mem (frameBase initial .sha256 mode true true + BitVec.ofNat 64 offset) : Operand width).read s := by
  apply memLoad_congr
  intro j hj
  simp only [memByte, PhysicalMemory.read]
  rw [ag.byte (by
    intro c hc hcover
    simp only [fullChanges, fullPrepareChanges, Memset.clobbers, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with ((rfl | rfl | rfl | rfl | rfl | rfl) | (rfl | rfl | rfl)) |
      (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;> try exact hcover.elim
    · obtain ⟨i, hi, he⟩ := hcover
      have apart := RangeApart.offsets (frameBase initial .sha256 mode true true - 8)
        (a := 0) (b := 8 + offset) (len := 8) (count := width / 8)
        (by omega) (by omega) (.inl (by omega))
      apply apart i hi j hj
      simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
        ← BitVec.add_assoc, BitVec.sub_add_cancel] using he.symm
    · obtain ⟨i, hi, he⟩ := hcover
      have apart := RangeApart.offsets (frameBase initial .sha256 mode true true)
        (a := 440) (b := offset) (len := 200) (count := width / 8)
        (by omega) (by omega) (.inr hbefore)
      exact apart i hi j hj he.symm)]

end Sha3.Proofs.Wrapper.Reset.Output.Zero
