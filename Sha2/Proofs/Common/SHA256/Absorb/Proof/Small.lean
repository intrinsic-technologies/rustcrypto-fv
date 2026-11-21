import Sha2.Proofs.Common.SHA256.Absorb.Proof.Small.Transport
import Sha2.Proofs.Common.SHA256.Absorb.Proof.Select
import Sha2.Proofs.Common.SHA256.Absorb.Proof.CallFrame
import Sha2.Proofs.Common.SHA256.Absorb.Proof.Hasher

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Absorb

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

theorem small [Bindings] {l : Layout} {initial before s : RamState} {n reserve : Nat}
    {regions : Vector MemoryRegion n} {prior : ByteArray} {input : Input}
    (ctx : Context l initial regions reserve)
    (state : Preserved l initial before s regions)
    (data : Prepared l (l.sp initial) prior input {s with RIP := l.entry})
    (rip : s.RIP = l.pc .smallSetup)
    (small : input.bytes.size < 64 - prior.size % 64)
    (apart : input.region.Disjoint (Stack.region initial reserve)) :
    ∃ t, Finished l initial before t regions prior input := by
  let start : Preserved l initial s s regions := Preserved.initial state.state state.rsp
  have buffer {t : RamState} (kept : Preserved l initial s t regions) :
      ∀ r ∈ l.bufferSource, Blocks.readReg t r = l.buffer (l.sp initial) := by
    intro r member
    exact (kept.frame.registers (r.setWidth 5)
      (by simpa only [BitVec.toNat_setWidth_of_le (by decide : 4 ≤ 5)] using r.isLt)
      (ctx.flow.bufferSaved r member).1).trans (data.bufferRegister r member)
  obtain ⟨u, stateU, setup⟩ := run_stage ctx start .smallSetup rfl rip (buffer start)
    (by intro h; cases h)
  have memoryU : u.external = s.external := setup.agrees.external
    (by simp [Stage.effect, Effect.components, Write.component, Operand.component, Component.Covers])
  have positionS : Blocks.readReg s l.registers.tail = BitVec.ofNat 64 (prior.size % 64) :=
    data.position
  have outputU : u.regValue .rdi = l.buffer (l.sp initial) +
      BitVec.ofNat 64 (prior.size % 64) := setup.writes.1.trans (congrArg (l.buffer (l.sp initial) + ·) positionS)
  have countU : u.regValue .rdx = BitVec.ofNat 64 input.bytes.size :=
    setup.writes.2.2.trans data.length
  have sourceU : u.regValue .rsi = input.address := setup.writes.2.1.trans data.source
  have inputRegion : registerRegion u .rsi input.bytes.size = input.region := by
    simp only [registerRegion, sourceU, Input.region]
  have bytesU : input.region.HasBytes u.external input.bytes := by
    rw [memoryU]; exact data.bytes
  have sliced := Common.Memory.input_slice bytesU data.bounded apart
    (offset := 0) (count := input.bytes.size) (by omega)
  simp only [BitVec.add_zero, Nat.zero_add,
    ByteArray.extract_zero_size] at sliced
  change input.region.HasBytes u.external input.bytes ∧ input.region.Bounded ∧
    input.region.Disjoint (Stack.region initial reserve) at sliced
  have targetRegister : ∀ r, l.smallCall.encoding = .register r →
      Blocks.readReg u r = 0x10dd60 := by
    intro r encoding
    have targets := ctx.targets.copies l.smallCall (by simp)
    rw [encoding] at targets
    exact (stateU.frame.registers (r.setWidth 5)
      (by simpa only [BitVec.toNat_setWidth_of_le (by decide : 4 ≤ 5)] using r.isLt)
      targets.2).trans (data.copyRegister l.smallCall (by simp) r encoding)
  obtain ⟨v, stateV, post, copied, copyFrame⟩ := copy ctx stateU l.smallCall (by simp)
    setup.rip outputU countU (by omega) (inputRegion ▸ sliced.1)
    (inputRegion ▸ sliced.2.1) (inputRegion ▸ sliced.2.2) targetRegister
    (by rw [ctx.flow.smallReturn]; exact ctx.code.inside .smallLength)
  have fullPost := post
  obtain ⟨_, _, called, callEffect, callResult, _⟩ := fullPost
  have nonvolatile (r : BitVec 4) (member : r ∈ [l.registers.length, l.registers.tail]) :
      Blocks.readReg v r = Blocks.readReg s r := by
    have nv := ctx.flow.nonvolatile r (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at member ⊢
      rcases member with rfl | rfl <;> simp)
    exact (call_result_register callEffect callResult
      (by simpa only [BitVec.toNat_setWidth_of_le (by decide : 4 ≤ 5)] using r.isLt)
      (nonvolatile_extended nv)).trans (smallSetup_register setup nv)
  have lengthV : Blocks.readReg v l.registers.length = BitVec.ofNat 64 input.bytes.size :=
    (nonvolatile _ (by simp)).trans data.length
  have tailV : Blocks.readReg v l.registers.tail = BitVec.ofNat 64 (prior.size % 64) :=
    (nonvolatile _ (by simp)).trans data.position
  obtain ⟨w, stateW, length⟩ := run_stage ctx stateV .smallLength rfl
    (post.1.trans ctx.flow.smallReturn) (buffer stateV) (by intro h; cases h)
  have memoryW : w.external = v.external := length.agrees.external
    (by simp [Stage.effect, Common.Instructions.AddByte.addR8R8Effect,
      Effect.components, Write.component, Operand.component, Component.Covers])
  have lengthW : (.reg (l.registers.length.setWidth 5) : Operand 8).read w =
      BitVec.ofNat 8 (prior.size % 64 + input.bytes.size) := by
    have write := length.writes
    change (.reg (l.registers.length.setWidth 5) : Operand 64).read w =
      mergeGPR 8
        ((.reg (l.registers.length.setWidth 5) : Operand 8).read v +
          (.reg (l.registers.tail.setWidth 5) : Operand 8).read v)
        ((.reg (l.registers.length.setWidth 5) : Operand 64).read v) at write
    change ((.reg (l.registers.length.setWidth 5) : Operand 64).read w).setWidth 8 = _
    rw [write, Wrapper.Absorb.mergeGPR8_low]
    change (Blocks.readReg v l.registers.length).setWidth 8 +
      (Blocks.readReg v l.registers.tail).setWidth 8 = _
    rw [lengthV, tailV, BitVec.setWidth_ofNat_of_le (by decide),
      BitVec.setWidth_ofNat_of_le (by decide), ← BitVec.ofNat_add, Nat.add_comm]
  obtain ⟨t, stateT, store⟩ := run_stage ctx stateW .smallStore rfl length.rip (buffer stateW)
    (by intro h; cases h)
  have oldTail : (⟨(l.buffer (l.sp initial)).toNat, (remainderBytes prior).size⟩ : MemoryRegion).HasBytes
      u.external (remainderBytes prior) := by
    rw [memoryU]
    simpa only [remainderBytes_size] using data.hasher.tailBytes
  have joined := ctx.append_buffer_copy (front := remainderBytes prior) (back := input.bytes)
    (by simpa only [remainderBytes_size] using (by omega : prior.size % 64 + input.bytes.size ≤ 64))
    oldTail (by simpa only [registerRegion, outputU, remainderBytes_size] using copied)
    (by simpa only [registerRegion, outputU, remainderBytes_size] using copyFrame)
  have tails : (⟨(l.buffer (l.sp initial)).toNat,
      (remainderBytes prior ++ input.bytes).size⟩ : MemoryRegion).HasBytes
      t.external (remainderBytes prior ++ input.bytes) := by
    refine ⟨rfl, ?_⟩
    intro i
    have hi : i.val < prior.size % 64 + input.bytes.size := by
      simpa only [ByteArray.size_append, remainderBytes_size] using i.isLt
    have keep := stage_buffer_byte .smallStore store (by omega : i.val < 104) (fun _ => by omega) (by simp)
    have original := joined.2 i
    change v.external[BitVec.ofNat 64 ((l.buffer (l.sp initial)).toNat + i.val)]? = _ at original
    change t.external[BitVec.ofNat 64 ((l.buffer (l.sp initial)).toNat + i.val)]? = _
    simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at original ⊢
    exact keep.trans (by rw [memoryW]; exact original)
  have untouched (i : Nat) (bound : i < 104)
      (outside : 64 ≤ i) :
      t.external[l.buffer (l.sp initial) + BitVec.ofNat 64 i]? =
        s.external[l.buffer (l.sp initial) + BitVec.ofNat 64 i]? := by
    have copiedKept := ctx.buffer_frame_byte
      (by simpa only [registerRegion, outputU] using copyFrame)
      (by omega) bound (Or.inr (by omega))
    exact (stage_buffer_byte .smallStore store bound (fun _ => by omega) (by simp)).trans
      (by rw [memoryW]; exact copiedKept.trans (by rw [memoryU]))
  have hash : HashStateAt t (l.buffer (l.sp initial) + 64)
      (compressBlocks l.initialHash prior) := by
    apply Wrapper.hashState_of_bytes data.hasher.hashWords
    intro i hi
    simpa only [BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.ofNat_eq_ofNat]
      using untouched (64 + i) (by omega) (by omega)
  have blocks : memLoad t.external (l.buffer (l.sp initial) + 96) 64 =
      BitVec.ofNat 64 (prior.size / 64) := by
    rw [← data.hasher.blocks]
    apply memLoad_congr
    intro i hi
    apply congrArg (fun byte : Option UInt8 => byte.getD 0)
    simpa only [BitVec.add_assoc, ← BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, PhysicalMemory.read]
      using untouched (96 + i) (by omega) (by omega)
  have tail : t.external[l.buffer (l.sp initial) + 63]? =
      some (UInt8.ofNat (prior.size % 64 + input.bytes.size)) := by
    have stored : memLoad t.external (l.buffer (l.sp initial) + 63) 8 =
        (.reg (l.registers.length.setWidth 5) : Operand 8).read w := store.writes
    have readable := (ctx.buffer_writable stateT.state (offset := 63) (len := 1)
      (by decide) (by decide)).toMemReadable
    have byte := byte_of_memLoad8 readable (stored.trans lengthW)
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : prior.size % 64 + input.bytes.size < 2^8)] using byte
  refine ⟨t, ⟨⟨stateT.state, stateT.rsp, state.frame.trans stateT.frame⟩, ?_,
    hasher_append_short small hash tails tail blocks, ?_⟩⟩
  · simpa only [ite_eq_left small, Stage.effect] using store.rip
  · intro large
    omega

end Sha2.Proofs.Common.SHA256.Absorb
