import Md5.Proofs.Buffered.FinalizeReset.Prepare.Geometry
import Md5.Proofs.Buffered.FinalizeReset.Export.Bytes

namespace Md5.Proofs.Buffered.FinalizeReset.Prepare

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem setup_rsp {variant : Variant} {s t : RamState} (h : (setupEffect s variant).Holds s t) :
    stackPtr t = stackPtr s := h.agrees.read (n := 64) (r := 4) (by
  simp [setupEffect, Effect.components, Write.component, Operand.component])

theorem copy_byte {variant : Variant} {s t : RamState} (h : (copyEffect s variant).Holds s t)
    (offset : Nat) (ho : offset < 232 ∨ 248 ≤ offset) (hb : offset < variant.stackBytes) :
    t.external[stackPtr s + BitVec.ofNat 64 offset]? =
      s.external[stackPtr s + BitVec.ofNat 64 offset]? := by
  have hsize := variant.stackBytes_bounds
  apply h.agrees.byte
  intro c hc hcov
  simp only [copyEffect, Effect.components, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, Write.component, Operand.component,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact hcov.elim
  all_goals obtain ⟨j, hj, he⟩ := hcov
  · exact RangeApart.offsets (stackPtr s) (a := offset) (len := 1) (b := 240)
      (count := 8) (by omega) (by decide) (by omega) 0 (by decide) j hj
      (by simpa using he)
  · exact RangeApart.offsets (stackPtr s) (a := offset) (len := 1) (b := 232)
      (count := 8) (by omega) (by decide) (by omega) 0 (by decide) j hj
      (by simpa using he)

theorem setup_byte {variant : Variant} {s t : RamState} {n : Nat}
    (hp : (.reg 15 : Operand 64).read s = BitVec.ofNat 64 n) (hn : n < 64)
    (h : (setupEffect s variant).Holds s t) (offset : Nat)
    (ho : offset ≠ n + 8) (hb : offset < variant.stackBytes) :
    t.external[stackPtr s + BitVec.ofNat 64 offset]? =
      s.external[stackPtr s + BitVec.ofNat 64 offset]? := by
  have hsize := variant.stackBytes_bounds
  apply h.agrees.byte
  intro c hc hcov
  simp only [setupEffect, Effect.components, List.map_cons, List.map_nil,
    List.cons_append, List.nil_append, Write.component, Operand.component,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact hcov.elim
  obtain ⟨j, hj, he⟩ := hcov
  rw [hp] at he
  have he' : stackPtr s + BitVec.ofNat 64 offset =
      stackPtr s + BitVec.ofNat 64 (n + 8) + BitVec.ofNat 64 j := by
    simpa [BitVec.ofNat_add, BitVec.add_assoc] using he
  exact RangeApart.offsets (stackPtr s) (a := offset) (len := 1) (b := n + 8)
    (count := 1) (by omega) (by omega) (by omega) 0 (by decide) j hj
    (by simpa only [BitVec.add_zero] using he')

theorem memset_byte {variant : Variant} [Bindings] {boundary : ReturnBoundary} {ret : BitVec 64}
    {s t : RamState} {base : BitVec 64} {n : Nat}
    (hs : Storage s variant) (hsp : stackPtr s = base)
    (hdi : rdi.read s = base + BitVec.ofNat 64 (n + 9))
    (hlen : (MemoryRoutines.rdx.read s).toNat = 63 - n) (hn : n < 64)
    (h : MemsetSiteResult boundary ret s t) (offset : Nat)
    (ho : offset < n + 9 ∨ 72 ≤ offset) (hb : offset < variant.stackBytes) :
    t.external[base + BitVec.ofNat 64 offset]? =
      s.external[base + BitVec.ofNat 64 offset]? := by
  have hsize := variant.stackBytes_bounds
  apply h.agrees.byte
  intro c hc hcov
  simp only [callSiteChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  all_goals try exact hcov.elim
  · obtain ⟨j, hj, he⟩ := hcov
    rw [hdi] at he
    rw [hlen] at hj
    exact RangeApart.offsets base (a := offset) (len := 1) (b := n + 9)
      (count := 63 - n) (by omega) (by omega) (by omega) 0 (by decide) j hj
      (by simpa only [BitVec.add_zero] using he)
  · obtain ⟨j, hj, he⟩ := hcov
    rw [← hsp] at he
    have he' := congrArg BitVec.toNat he
    rw [Export.stackAddress_toNat hs _ (by omega),
      toNat_add_ofNat _ _ (by
        rw [pushAddress_toNat hs]
        have hh : (stackPtr s).toNat + variant.stackBytes < 2^32 := hs.stackHigh
        omega), pushAddress_toNat hs] at he'
    have := hs.stackLow
    omega

theorem copy_agrees_prepare {variant : Variant} {s t : RamState} (h : (copyEffect s variant).Holds s t) :
    AgreesExcept (prepareChanges s) s t := by
  have hsize := variant.stackBytes_bounds
  apply h.agrees.widen
  · intro c hc hm
    simp only [copyEffect, Effect.components, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, Write.component, Operand.component,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [Component.isMem, prepareChanges]
  · intro x c hc hcov
    simp only [copyEffect, Effect.components, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, Write.component, Operand.component,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hcov.elim
    · exact ⟨.mem (stackPtr s + 0xe8) 16, by simp [prepareChanges],
        Export.covers_shift (offset := 8) (by simpa [BitVec.add_assoc] using hcov)
          (by decide)⟩
    · exact ⟨.mem (stackPtr s + 0xe8) 16, by simp [prepareChanges],
        Export.covers_shift (offset := 0) (by simpa only [BitVec.add_zero] using hcov)
          (by decide)⟩

theorem setup_agrees_prepare {variant : Variant} {initial s t : RamState} {n : Nat}
    (hsp : stackPtr s = stackPtr initial)
    (hp : (.reg 15 : Operand 64).read s = BitVec.ofNat 64 n) (hn : n < 64)
    (h : (setupEffect s variant).Holds s t) : AgreesExcept (prepareChanges initial) s t := by
  have hsize := variant.stackBytes_bounds
  apply h.agrees.widen
  · intro c hc hm
    simp only [setupEffect, Effect.components, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, Write.component, Operand.component,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [Component.isMem, prepareChanges]
  · intro x c hc hcov
    simp only [setupEffect, Effect.components, List.map_cons, List.map_nil,
      List.cons_append, List.nil_append, Write.component, Operand.component,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hcov.elim
    refine ⟨.mem (context initial) 64, by simp [prepareChanges], ?_⟩
    apply Export.covers_shift (offset := n) (len := 1) _ (by omega)
    change Component.Covers (.mem (stackPtr s + (.reg 15 : Operand 64).read s + 8) 1) x
      at hcov
    rw [hp, hsp] at hcov
    have he : stackPtr initial + BitVec.ofNat 64 n + 8 =
        context initial + BitVec.ofNat 64 n := by
      simp only [context, BitVec.add_assoc]
      rw [BitVec.add_comm (BitVec.ofNat 64 n)]
    rwa [he] at hcov

theorem memset_agrees_prepare [Bindings] {boundary : ReturnBoundary} {ret : BitVec 64}
    {initial s t : RamState} {n : Nat}
    (hsp : stackPtr s = stackPtr initial)
    (hdi : rdi.read s = stackPtr initial + BitVec.ofNat 64 (n + 9))
    (hlen : (MemoryRoutines.rdx.read s).toNat = 63 - n) (hn : n < 64)
    (h : MemsetSiteResult boundary ret s t) :
    AgreesExcept (prepareChanges initial) s t := by
  apply h.agrees.widen
  · intro c hc hm
    simp only [callSiteChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    all_goals simp_all [Component.isMem, prepareChanges]
  · intro x c hc hcov
    simp only [callSiteChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl
    all_goals try exact hcov.elim
    · refine ⟨.mem (context initial) 64, by simp [prepareChanges], ?_⟩
      apply Export.covers_shift (offset := n + 1) (len := 63 - n) _ (by omega)
      change Component.Covers (.mem (rdi.read s) (MemoryRoutines.rdx.read s).toNat) x
        at hcov
      rw [hdi, hlen] at hcov
      have he : stackPtr initial + BitVec.ofNat 64 (n + 9) =
          context initial + BitVec.ofNat 64 (n + 1) := by
        simp only [context, BitVec.ofNat_add, BitVec.add_assoc]
        rw [← BitVec.add_assoc (8 : BitVec 64), BitVec.add_comm (8 : BitVec 64),
          BitVec.add_assoc]
        rfl
      rwa [he] at hcov
    · exact ⟨.mem (stackPtr initial - 8) 8, by simp [prepareChanges],
        by simpa only [pushAddr, hsp] using hcov⟩

theorem prepare_agrees_reset {s t : RamState} (h : AgreesExcept (prepareChanges s) s t) :
    AgreesExcept (changes s) s t := by
  apply h.widen
  · intro c hc hm
    simp only [prepareChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp_all [Component.isMem, changes]
  · intro x c hc hcov
    simp only [prepareChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hcov.elim
    · refine ⟨.mem (stackPtr s - 320) 320, by simp [changes], ?_⟩
      apply Export.covers_shift (offset := 312) (len := 8) _ (by decide)
      have he : stackPtr s - 320 + BitVec.ofNat 64 312 = stackPtr s - 8 := by
        simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
        rfl
      rwa [he]
    · exact ⟨.mem (stackPtr s + 8) 152, by simp [changes],
        Export.covers_shift (offset := 0) (by simpa [context] using hcov) (by decide)⟩
    · exact ⟨.mem (stackPtr s + 0xe8) 16, by simp [changes], hcov⟩

end Md5.Proofs.Buffered.FinalizeReset.Prepare
