import Hkdf.Proofs.Key.Hash.State
import Hkdf.Proofs.Key.Hash.Serialize
import Hkdf.Proofs.Key.Memory

set_option autoImplicit false

namespace Hkdf.Proofs.Key.Hash

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Spec.Program
open Hkdf.Proofs.Common.SHA256
open Hkdf.Proofs.Common.HMAC

set_option maxHeartbeats 800000 in
theorem finish [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {key : ByteArray} (ctx : Context initial boundary key)
    (state : Working initial boundary s) (rip : s.RIP = 0x1165c9)
    (hashWords : HashStateAt s (rspOf s + 128)
      (compressBlocks Hkdf.Proofs.NIST.SHA256.initialHash (bytePadding key)))
    (large : 64 < key.size) : ∃ t, Key.Ready initial boundary key t := by
  have pre : Serialize.Pre s := by
    refine ⟨rip, ?_, ?_, ?_⟩
    · intro slot member
      rw [stack_address state.rsp]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp only [BitVec.ofNat_eq_ofNat, BitVec.reduceSub]
      all_goals exact stack_readable ctx state.toState (by decide) (by decide)
    · intro slot member
      rw [stack_address state.rsp]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp only [BitVec.ofNat_eq_ofNat, BitVec.reduceSub]
      all_goals
        refine (fun (writable : MemWritable s _ 4) =>
          ⟨⟨writable.low, writable.mem⟩, writable.tables⟩)
          (stack_writable4 ctx state.toState ?_ ?_) <;> decide
    · intro slot member pc len lower upper
      rw [stack_address state.rsp]
      have address : BitVec.ofNat 64 pc =
          Extracted.textAddress + BitVec.ofNat 64 (pc - 0x100000) := by
        change BitVec.ofNat 64 pc = BitVec.ofNat 64 0x100000 + _
        rw [← BitVec.ofNat_add]
        exact congrArg (BitVec.ofNat 64) (by omega)
      rw [address]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp only [BitVec.ofNat_eq_ofNat, BitVec.reduceSub]
      all_goals exact stack_codeApart ctx (by decide) (by decide) (by omega)
  have outside : ∀ ip : Nat, 0x1165c9 ≤ ip → ip ≤ 0x116639 →
      (BitVec.ofNat 64 ip) ≠ boundary.rip := by
    intro ip lower upper
    apply Hkdf.Proofs.Common.Machine.boundary_ne_program ctx.outerBoundary
    have address : BitVec.ofNat 64 ip =
        Extracted.textAddress + BitVec.ofNat 64 (ip - 0x100000) := by
      change BitVec.ofNat 64 ip = BitVec.ofNat 64 0x100000 + _
      rw [← BitVec.ofNat_add]
      exact congrArg (BitVec.ofNat 64) (by omega)
    rw [address]
    exact Hkdf.Proofs.Common.Machine.inProgram_of_textOffset _ (by omega)
  obtain ⟨fuel, t, run, ready, _, effect⟩ := Serialize.run boundary outside s
    (Hkdf.Proofs.Common.Machine.supportedMachine_readyToStep state.machine)
    (Serialize.code state.loaded) pre
  have footprint : ∀ c ∈ (Serialize.effect s).components, ∀ a, c.Covers a →
      (Component.mem (rspOf s) 32).Covers a := by
    intro c member a covered
    simp only [Serialize.effect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, or_assoc] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact covered.elim
    all_goals obtain ⟨i, hi, rfl⟩ := covered
    · exact ⟨0 + i, by omega, by
        simp only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc]⟩
    · exact ⟨4 + i, by omega, by
        simp only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc]⟩
    · exact ⟨8 + i, by omega, by
        simp only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc]⟩
    · exact ⟨12 + i, by omega, by
        simp only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc]⟩
    · exact ⟨16 + i, by omega, by
        simp only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc]⟩
    · exact ⟨20 + i, by omega, by
        simp only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc]⟩
    · exact ⟨24 + i, by omega, by
        simp only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc]⟩
    · exact ⟨28 + i, by omega, by
        simp only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc]⟩
  have writes : LocalWrites initial (Serialize.effect s).components := by
    intro c member a covered
    have byte := footprint c member a covered
    rw [show rspOf s = blockAddress initial from state.rsp] at byte
    exact local_memory (by decide) (by decide) a byte
  have running := state.toRunning.of_agrees run ready effect.agrees (writes.within ctx)
    (by
      intro region member address contains inside
      exact ctx.avoids region (by simpa [writeRegions] using member)
        address contains (.inl inside))
    (by simp [Serialize.effect, Effect.components, Write.component, Operand.component])
  have saved := state.saved.of_agrees (by
    intro i hi
    exact effect.agrees.memory _ (fun c hc => writes.saved c hc _ ⟨i, hi, rfl⟩))
  have current : Key.State initial boundary t :=
    ⟨running, saved,
      (effect.agrees.read (n := 64) (r := 5) (by
        simp [Serialize.effect, Effect.components, Write.component, Operand.component])).trans state.rbp,
      (effect.agrees.mxcsr (by simp [Serialize.effect, Effect.components])).trans state.mxcsr,
      (effect.agrees.fcw (by simp [Serialize.effect, Effect.components])).trans state.fcw⟩
  have bounds := stack_bounds ctx.toCalleePre
  have blockNat : (blockAddress initial).toNat = (stackPtr initial).toNat - 376 :=
    stack_sub_toNat ctx.toCalleePre (by decide)
  have blockBound : (blockAddress initial).toNat + 64 < 2^32 := by omega
  have frame : MemoryWriteFrame s t #v[(⟨(blockAddress initial).toNat, 32⟩ : MemoryRegion)] := by
    apply effect.agrees.memoryWriteFrame
    intro c member a covered
    obtain ⟨i, hi, address⟩ := footprint c member a covered
    rw [address, show rspOf s = blockAddress initial from state.rsp]
    refine ⟨(⟨(blockAddress initial).toNat, 32⟩ : MemoryRegion), by simp, ?_⟩
    exact Hkdf.Proofs.Common.Machine.memoryRegion_contains_add
      (show (⟨(blockAddress initial).toNat, 32⟩ : MemoryRegion).Bounded from by
        change (blockAddress initial).toNat + 32 < 2^32
        omega) (Nat.le_refl _) (Nat.le_refl _) hi
  have zerosBefore : (⟨(blockAddress initial).toNat + 32, 32⟩ : MemoryRegion).HasBytes
      s.external ⟨Array.replicate 32 0⟩ := by
    refine ⟨rfl, ?_⟩
    intro i
    have byte := state.zeroBlock.2 ⟨32 + i.val, by
      have := i.isLt
      simp only [ByteArray.size, Array.size_replicate] at this ⊢
      omega⟩
    simpa only [Nat.add_assoc, ByteArray.getElem_eq_getElem_data, Array.getElem_replicate] using byte
  have zeros := Hkdf.Proofs.Common.CallFrame.frame_hasBytes frame (by
      intro written member
      have eq : written = (⟨(blockAddress initial).toNat, 32⟩ : MemoryRegion) := by
        simpa using member
      subst written
      intro a left right
      change (blockAddress initial).toNat + 32 ≤ a ∧ a < (blockAddress initial).toNat + 32 + 32 at left
      change (blockAddress initial).toNat ≤ a ∧ a < (blockAddress initial).toNat + 32 at right
      omega)
    (by change (blockAddress initial).toNat + 32 + 32 ≤ 2^64; omega) zerosBefore
  have digest := Serialize.payload_hashBytes pre hashWords effect
  rw [show rspOf s = blockAddress initial from state.rsp] at digest
  have normalized : keyBlock key = Standards.NIST.SHA2.SHA256.hashBytes key ++
      ⟨Array.replicate 32 0⟩ := by
    simp only [keyBlock, large, ↓reduceIte, sha256_hashBytes_size]
  refine ⟨t, current, effect.rip, ?_, ?_, ?_⟩
  · exact (Serialize.rsp_unchanged effect).trans state.rsp
  · exact (effect.agrees.read (n := 64) (r := 3) (by
      simp [Serialize.effect, Effect.components, Write.component, Operand.component])).trans state.outputPointer
  · refine ⟨keyBlock_size key, ?_⟩
    intro index
    obtain ⟨i, indexBound⟩ := index
    have hi : i < 64 := by simpa only [keyBlock_size] using indexBound
    simp only [normalized]
    by_cases first : i < 32
    · rw [ByteArray.getElem_append_left (by simpa only [sha256_hashBytes_size] using first)]
      exact digest.2 ⟨i, by simpa only [sha256_hashBytes_size] using first⟩
    · rw [ByteArray.getElem_append_right (by rw [sha256_hashBytes_size]; omega)]
      have byte := zeros.2 ⟨i - 32, by
        simp only [ByteArray.size, Array.size_replicate]
        omega⟩
      simpa only [sha256_hashBytes_size,
        show (blockAddress initial).toNat + 32 + (i - 32) =
          (blockAddress initial).toNat + i by omega] using byte

end Hkdf.Proofs.Key.Hash
