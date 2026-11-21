import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.PreviousCopy.Execution
import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.PreviousCopy.State

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Expand

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Spec.Program Hkdf.Proofs.Common Hkdf.Proofs.Common.Machine
open PreviousCopy (CopyPre copyBytes copyEffect copyRun hmac_after_copy)

private theorem copy_components (s : RamState) :
    (copyEffect s).components =
      [.reg 1, .reg 0, .reg 3, .mem (rspOf s + 296) 8, .mem (rspOf s + 288) 8,
        .mem (rspOf s + 280) 8, .mem (rspOf s + 272) 8, .mem (rspOf s + 335) 1,
        .flags, .rip] := by
  simp only [copyEffect, Effect.components, List.map_cons, List.map_nil, Write.component_reg,
    Write.component_mem, Nat.reduceDiv, List.cons_append, List.nil_append]

private theorem copy_words {s t : RamState} (effect : (copyEffect s).Holds s t) :
    ∀ j < 4, memLoad t.external (rspOf s + 272 + BitVec.ofNat 64 (8 * j)) 64 =
      memLoad s.external (rspOf s + 456 + BitVec.ofNat 64 (8 * j)) 64 := by
  intro j hj
  have writes := effect.writes
  simp only [copyEffect, Write.AllHold, Operand.read] at writes
  obtain ⟨_, _, _, w3, w2, w1, w0, _⟩ := writes
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
  all_goals simp only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
    BitVec.add_assoc, BitVec.reduceAdd]
  · exact w0
  · exact w1
  · exact w2
  · exact w3

private theorem copy_tail {s t : RamState} {previous : ByteArray}
    (pre : CopyPre s) (effect : (copyEffect s).Holds s t)
    (digest : (⟨(rspOf s + 456).toNat, 32⟩ : MemoryRegion).HasBytes s.external previous) :
    (⟨(rspOf s + 272).toNat, 32⟩ : MemoryRegion).HasBytes t.external previous := by
  have size : previous.size = 32 := digest.1
  have wordAccessible (j : Nat) (hj : j < 4) :
      MemReadable s (rspOf s + 456 + BitVec.ofNat 64 (8 * j)) 8 ∧
      MemWritable s (rspOf s + 272 + BitVec.ofNat 64 (8 * j)) 8 := by
    rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
    all_goals simp only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero,
      BitVec.add_assoc, BitVec.reduceAdd]
    · exact ⟨pre.readable 456 (by decide), pre.writable 272 (by decide)⟩
    · exact ⟨pre.readable 464 (by decide), pre.writable 280 (by decide)⟩
    · exact ⟨pre.readable 472 (by decide), pre.writable 288 (by decide)⟩
    · exact ⟨pre.readable 480 (by decide), pre.writable 296 (by decide)⟩
  refine ⟨size, ?_⟩
  intro i
  have hi : i.val < 32 := size ▸ i.isLt
  have available := wordAccessible (i.val / 8) (by omega)
  have destination := Bytes.of_memLoad (n := 64)
    (available.2.readable.of_holds effect).mem (i.val % 8) (by omega)
  have source := Bytes.of_memLoad (n := 64) available.1.mem (i.val % 8) (by omega)
  rw [copy_words effect (i.val / 8) (by omega)] at destination
  have bytes := destination.trans source.symm
  have offset (p : BitVec 64) : p + BitVec.ofNat 64 (8 * (i.val / 8)) +
      BitVec.ofNat 64 (i.val % 8) = BitVec.ofNat 64 (p.toNat + i.val) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 8 * (i.val / 8) + i.val % 8 = i.val by omega,
      BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rw [offset, offset] at bytes
  exact bytes.trans (digest.2 i)

private theorem copy_length {s t : RamState} (pre : CopyPre s)
    (effect : (copyEffect s).Holds s t) :
    t.external[rspOf s + 335]? = some 32 := by
  have ⟨_, _, _, _, _, _, _, stored⟩ := effect.writes
  change memLoad t.external (rspOf s + 335) 8 = 32#8 at stored
  have byte := Bytes.of_memLoad (n := 8) (pre.lengthWritable.readable.of_holds effect).mem 0 (by decide)
  have normalized : t.external[rspOf s + 335]? =
      some (storedByte (memLoad t.external (rspOf s + 335) 8) 0) := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using byte
  rw [stored] at normalized
  exact normalized

private theorem copy_preserved {s t : RamState} (effect : (copyEffect s).Holds s t)
    (i : Nat) (lo : 64 ≤ i) (hi : i < 144) :
    t.external[rspOf s + 272 + BitVec.ofNat 64 i]? =
      s.external[rspOf s + 272 + BitVec.ofNat 64 i]? := by
  have addr : rspOf s + 272 + BitVec.ofNat 64 i = rspOf s + BitVec.ofNat 64 336 +
      BitVec.ofNat 64 (i - 64) := by
    change rspOf s + BitVec.ofNat 64 272 + BitVec.ofNat 64 i = _
    simp only [BitVec.add_assoc, ← BitVec.ofNat_add,
      show 272 + i = 336 + (i - 64) by omega]
  rw [addr]
  apply effect.agrees.byte
  intro c hc
  have apart (off len : Nat) (bound : off + len ≤ 336)
      (covered : (Component.mem (rspOf s + BitVec.ofNat 64 off) len).Covers
        (rspOf s + BitVec.ofNat 64 336 + BitVec.ofNat 64 (i - 64))) : False := by
    obtain ⟨j, hj, equality⟩ := covered
    exact RangeApart.offsets (rspOf s) (a := 336) (b := off) (len := 80) (count := len)
      (by decide) (by omega) (.inr bound) (i - 64) (by omega) j hj equality
  simp only [copy_components, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact id
  · exact id
  · exact id
  · exact apart 296 8 (by decide)
  · exact apart 288 8 (by decide)
  · exact apart 280 8 (by decide)
  · exact apart 272 8 (by decide)
  · exact apart 335 1 (by decide)
  · exact id
  · exact id

theorem previousCopy [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {key previous : ByteArray} (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (outside : ¬ InProgram boundary.rip) (pre : CopyPre s)
    (hmac : HmacAt s (rspOf s + 272) key ByteArray.empty)
    (digest : (⟨(rspOf s + 456).toNat, 32⟩ : MemoryRegion).HasBytes s.external previous) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ t.RIP = 0x10f6c3 ∧
      HmacAt t (rspOf t + 272) key previous ∧
      AgreesExcept [.reg 1, .reg 0, .reg 3, .mem (rspOf s + 296) 8, .mem (rspOf s + 288) 8,
        .mem (rspOf s + 280) 8, .mem (rspOf s + 272) 8, .mem (rspOf s + 335) 1,
        .flags, .rip] s t := by
  obtain ⟨fuel, t, run, readyT, _, effect⟩ := copyRun boundary outside s ready
    (programText_slice (programLoaded_codeIn loaded) 0xf682 copyBytes (by decide) (by decide +kernel)) pre
  have frame : AgreesExcept [.reg 1, .reg 0, .reg 3, .mem (rspOf s + 296) 8, .mem (rspOf s + 288) 8,
      .mem (rspOf s + 280) 8, .mem (rspOf s + 272) 8, .mem (rspOf s + 335) 1,
      .flags, .rip] s t := copy_components s ▸ effect.agrees
  have sp : rspOf t = rspOf s := frame.read (n := 64) (r := 4) (by simp)
  refine ⟨fuel, t, run, readyT, effect.rip, ?_, frame⟩
  rw [sp]
  exact hmac_after_copy hmac (copy_tail pre effect digest) (by
    rw [BitVec.add_assoc]
    exact copy_length pre effect) (copy_preserved effect)

end Hkdf.Proofs.NewExpand.Expand
