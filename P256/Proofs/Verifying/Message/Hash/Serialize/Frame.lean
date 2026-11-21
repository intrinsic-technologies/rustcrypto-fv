import P256.Proofs.Verifying.Message.Hash.Serialize.Machine
import P256.Proofs.Program.Memory
import X86Proofs.Program.ReadWrite.WriteFrame

set_option autoImplicit false

namespace P256.Proofs.Verifying.Message.Hash.Serialize

open Prelude X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program

theorem writesWithin {s : RamState} {region : MemoryRegion}
    (bounded : region.Bounded) (start : region.start ≤ (rspOf s + 424).toNat)
    (finish : (rspOf s + 424).toNat + 32 ≤ region.start + region.size) :
    WritesWithin (effect s).components #v[region] := by
  have covers (offset : Nat) (bound : offset + 4 ≤ 32) (a : BitVec 64)
      (covered : (Component.mem (rspOf s + 424 + BitVec.ofNat 64 offset) 4).Covers a) :
      region.Contains a.toNat := by
    obtain ⟨i, hi, rfl⟩ := covered
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact memoryRegion_contains_add bounded start finish (by omega)
  intro c hc a ha
  refine ⟨region, by simp, ?_⟩
  simp only [effect, Effect.components, Write.component, Operand.component,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append, List.append_nil,
    List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  · exact covers 0 (by decide) a (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using ha)
  · exact covers 4 (by decide) a (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using ha)
  · exact covers 8 (by decide) a (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using ha)
  · exact covers 12 (by decide) a (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using ha)
  · exact covers 16 (by decide) a (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using ha)
  · exact covers 20 (by decide) a (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using ha)
  · exact covers 24 (by decide) a (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using ha)
  · exact covers 28 (by decide) a (by simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using ha)

theorem memory_frame {s t : RamState} {region : MemoryRegion}
    (bounded : region.Bounded) (start : region.start ≤ (rspOf s + 424).toNat)
    (finish : (rspOf s + 424).toNat + 32 ≤ region.start + region.size)
    (h : (effect s).Holds s t) : MemoryWriteFrame s t #v[region] :=
  h.agrees.memoryWriteFrame (writesWithin bounded start finish)

theorem register_frame {s t : RamState} (h : (effect s).Holds s t)
    {r : BitVec 5} (preserved : r ∉ ([0,1,2,6,7,8,9,10] : List (BitVec 5))) :
    (Operand.reg r : Operand 64).read t = (Operand.reg r : Operand 64).read s := by
  apply h.agrees.read
  simpa [effect, Effect.components, Write.component, Operand.component] using preserved

theorem flags_frame {s t : RamState} (h : (effect s).Holds s t) :
    t.RFLAGS = s.RFLAGS := by
  apply h.agrees.rflags <;>
    simp [effect, Effect.components, Write.component, Operand.component]

end P256.Proofs.Verifying.Message.Hash.Serialize
