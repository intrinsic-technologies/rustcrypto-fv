import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Finalize.Serialize.Machine
import Hkdf.Proofs.Common.Memory
import Hkdf.Proofs.Common.SHA256.Words
import Hkdf.Proofs.Common.SHA256.Mathematics.Padding.Serialization

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Expand.Finalize.Serialize

open Prelude X86 X86.Machine X86.UserProcess X86Proofs Hkdf.Spec.Program
open Hkdf.Proofs.Common.Machine Hkdf.Proofs.Common.SHA256
open Hkdf.Proofs.Common.SHA256.Compression (bswap32)

theorem payload {outer : Bool} {s t : RamState} {hash : Array UInt32}
    (pre : Pre outer s)
    (hashWords : HashStateAt s (rspOf s + BitVec.ofNat 64 (source outer)) hash)
    (h : (effect outer s).Holds s t) :
    (⟨(rspOf s + BitVec.ofNat 64 (destination outer)).toNat, 32⟩ : MemoryRegion).HasBytes
      t.external (serializeHash hash) := by
  have allocated : ∀ i < 32,
      (t.external[rspOf s + BitVec.ofNat 64 (destination outer) + BitVec.ofNat 64 i]?).isSome := by
    intro i hi
    have hw := (pre.writable (i / 4) (by omega)).toMemReadable.of_holds h
    have byte := hw.mem (i % 4) (by omega)
    simpa only [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_assoc,
      show 4 * (i / 4) + i % 4 = i by omega] using byte
  have words : ∀ i < 8, memLoad t.external
      (rspOf s + BitVec.ofNat 64 (destination outer) + BitVec.ofNat 64 (4 * i)) 32 =
        bswap32 hash[i]!.toBitVec := by
    intro i hi
    have load : memLoad s.external (rspOf s + BitVec.ofNat 64 (source outer + 4 * i)) 32 =
        hash[i]!.toBitVec := by
      apply memLoad32_of_loadBytes4 (pre.readable i hi).mem
      simpa only [BitVec.ofNat_add, BitVec.add_assoc] using hashWords.2 i hi
    have stored := word h i hi
    rw [load] at stored
    simpa only [BitVec.ofNat_add, BitVec.add_assoc] using stored
  have bytes := Hkdf.Proofs.Common.Memory.bigEndian_bytes allocated words
  refine ⟨by simp only [MemoryRegion.HasLength, serializeHash_size, hashWords.1], ?_⟩
  intro i
  have hi : i.val < 32 := by simpa only [serializeHash_size, hashWords.1] using i.isLt
  change t.external[BitVec.ofNat 64
    ((rspOf s + BitVec.ofNat 64 (destination outer)).toNat + i.val)]? = _
  rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, serializeHash_getElem]
  exact bytes i.val hi

theorem execute [Bindings] {s : RamState} {boundary : ReturnBoundary} {hash : Array UInt32}
    (outer : Bool) (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (outside : ¬ InProgram boundary.rip) (pre : Pre outer s)
    (words : HashStateAt s (rspOf s + BitVec.ofNat 64 (source outer)) hash) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ (effect outer s).Holds s t ∧
      (⟨(rspOf s + BitVec.ofNat 64 (destination outer)).toNat, 32⟩ : MemoryRegion).HasBytes
        t.external (serializeHash hash) := by
  have continues (offset : Nat) (hi : offset ≤ 113) :
      start outer + BitVec.ofNat 64 offset ≠ boundary.rip := by
    apply boundary_ne_program outside
    cases outer
    · change InProgram ((Extracted.textAddress + BitVec.ofNat 64 0xf3bd) + BitVec.ofNat 64 offset)
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact inProgram_of_textOffset _ (by omega)
    · change InProgram ((Extracted.textAddress + BitVec.ofNat 64 0xf4cb) + BitVec.ofNat 64 offset)
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact inProgram_of_textOffset _ (by omega)
  obtain ⟨fuel, t, advance, ready', _, h⟩ :=
    run outer boundary continues s ready (code loaded outer) pre
  exact ⟨fuel, t, advance, ready', h, payload pre words h⟩

end Hkdf.Proofs.NewExpand.Expand.Finalize.Serialize
