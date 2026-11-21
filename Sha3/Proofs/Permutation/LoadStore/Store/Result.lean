import Sha3.Proofs.Permutation.LoadStore.Store.Basic
import Sha3.Proofs.Permutation.LoadStore.Store.Restore

namespace Sha3.Proofs.Permutation.Store

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program Keccak

theorem effect_components (copy : Copy) (sp pointer : BitVec 64) (s : RamState) :
    (effect copy sp pointer s).components =
      (List.range 25).map (fun i ↦ Component.mem (pointer + BitVec.ofNat 64 (8 * i)) 8) ++
        [.reg 0, .reg 2, .reg 6, .rip] := by
  simp [effect, Effect.components, List.range_succ]

theorem effect_covers {copy : Copy} {sp pointer address : BitVec 64} {s : RamState} {c : Component}
    (hc : c ∈ (effect copy sp pointer s).components) (hcover : c.Covers address) :
    ∃ i < 200, address = pointer + BitVec.ofNat 64 i := by
  rw [effect_components] at hc
  rcases List.mem_append.mp hc with hm | hr
  · obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hm
    obtain ⟨j, hj, rfl⟩ := hcover
    have hi' : i < 25 := List.mem_range.mp hi
    refine ⟨8 * i + j, by omega, ?_⟩
    rw [BitVec.ofNat_add, BitVec.add_assoc]
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl <;> exact hcover.elim

theorem effect_lanes {copy : Copy} {sp pointer : BitVec 64} {s t : RamState}
    (he : (effect copy sp pointer s).Holds s t) :
    memoryLanes pointer t = readLanes sp s := by
  refine funext (fun (i : Fin 25) ↦ ?_)
  apply Write.allHold_iff.mp he.writes
    ⟨(Operand.mem (pointer + BitVec.ofNat 64 (8 * i.val)) : Operand 64), readLanes sp s i⟩
  finite_cases i <;> simp (config := { decide := true }) [effect]

theorem effect_frame_byte {copy : Copy} {sp pointer : BitVec 64} {s t : RamState}
    (hap : RangeApart pointer 200 sp 272) (he : (effect copy sp pointer s).Holds s t)
    (i : Nat) (hi : i < 272) :
    t.external[sp + BitVec.ofNat 64 i]? = s.external[sp + BitVec.ofNat 64 i]? := by
  apply he.agrees.byte
  intro c hc hcover
  obtain ⟨j, hj, heq⟩ := effect_covers hc hcover
  exact hap j hj i hi heq.symm

theorem effect_frame_read {copy : Copy} {sp pointer : BitVec 64} {s t : RamState}
    (hap : RangeApart pointer 200 sp 272) (he : (effect copy sp pointer s).Holds s t)
    (offset : Nat) (hoff : offset + 8 ≤ 272) :
    (Operand.mem (sp + BitVec.ofNat 64 offset) : Operand 64).read t =
      (Operand.mem (sp + BitVec.ofNat 64 offset) : Operand 64).read s := by
  apply memLoad_congr
  intro i hi
  have hb := effect_frame_byte hap he (offset + i) (by omega)
  simp only [BitVec.ofNat_add, ← BitVec.add_assoc] at hb
  exact congrArg (fun x : Option UInt8 ↦ x.getD 0) hb

theorem effect_stack {copy : Copy} {sp pointer : BitVec 64} {s t : RamState}
    (he : (effect copy sp pointer s).Holds s t) : t.regValue .rsp = s.regValue .rsp := by
  exact he.agrees.read (n := 64) (r := 4) (by
    simp [effect_components])

theorem effect_memoryWriteFrame {copy : Copy} {initial s t : RamState}
    (hlow : (initial.regValue .rdi).toNat + 200 ≤ 2^32)
    (he : (effect copy (frameBase initial) (initial.regValue .rdi) s).Holds s t) :
    MemoryWriteFrame s t (writeRegions initial) := by
  intro address hout
  apply he.agrees.byte
  intro c hc hcover
  obtain ⟨i, hi, rfl⟩ := effect_covers hc hcover
  apply hout ⟨(initial.regValue .rdi).toNat, 200⟩ (by simp [writeRegions])
  change (initial.regValue .rdi).toNat ≤ _ ∧ _ < (initial.regValue .rdi).toNat + 200
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  omega

theorem effect_callFrame {copy : Copy} {initial s t : RamState}
    (hp : Pre copy (frameBase initial) (initial.regValue .rdi) s)
    (hf : CallFrame initial s)
    (he : (effect copy (frameBase initial) (initial.regValue .rdi) s).Holds s t) :
    CallFrame initial t := by
  refine ⟨(effect_stack he).trans hf.stack, ?_, ?_, ?_,
    memoryWriteFrame_trans hf.memory (effect_memoryWriteFrame hp.outputRead.low he),
    (fun x hx ↦ he.agrees.grow x (hf.grows x hx)), (he.agrees.scalarFrame_eq (by simp [effect, Effect.components, x86_compose])).trans hf.rest⟩
  · exact (effect_frame_read hp.apart he 160 (by decide)).trans hf.pointer
  · intro i
    exact (effect_frame_read hp.apart he (216 + 8 * i.val) (by omega)).trans (hf.saved i)
  · have hb := effect_frame_read hp.apart he 264 (by decide)
    have heq : frameBase initial + BitVec.ofNat 64 264 = initial.regValue .rsp :=
      BitVec.sub_add_cancel _ _
    rw [heq] at hb
    exact hb.trans hf.returnSlot

theorem effect_restore_readable {copy : Copy} {initial s t : RamState}
    (hp : Pre copy (frameBase initial) (initial.regValue .rdi) s)
    (he : (effect copy (frameBase initial) (initial.regValue .rdi) s).Holds s t)
    (i : Fin 7) : MemReadable t (restoreSlot initial i.val) 8 := by
  have hr : MemReadable t (frameBase initial) 272 :=
    ⟨hp.frameRead.low, fun j hj ↦ he.agrees.grow _ (hp.frameRead.mem j hj)⟩
  refine ⟨?_, ?_⟩
  · have := hr.low
    have := i.isLt
    simp only [restoreSlot, BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  · intro j hj
    have hb := he.agrees.grow _ (hp.frameRead.mem (216 + 8 * i.val + j) (by omega))
    simpa only [restoreSlot, BitVec.ofNat_add, ← BitVec.add_assoc] using hb

theorem restorePre_of_effect {copy : Copy} {initial s t : RamState} {a : Lanes}
    (hp : Pre copy (frameBase initial) (initial.regValue .rdi) s)
    (hi : RoundInvariant copy initial 24 a s)
    (he : (effect copy (frameBase initial) (initial.regValue .rdi) s).Holds s t)
    (htarget : (stackTop initial).toNat < 2^32) : RestorePre copy initial a t :=
  ⟨effect_callFrame hp hi.frame he, he.rip, (effect_lanes he).trans hi.lanes,
    effect_restore_readable hp he, htarget⟩

end Sha3.Proofs.Permutation.Store
