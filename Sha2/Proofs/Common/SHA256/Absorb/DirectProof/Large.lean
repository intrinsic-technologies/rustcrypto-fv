import Sha2.Proofs.Common.SHA256.Absorb.DirectProof.Bytes
import Sha2.Proofs.Common.SHA256.Absorb.DirectProof.Compression
import Sha2.Proofs.Common.SHA256.Absorb.DirectProof.InputBytes
import Sha2.Proofs.Wrapper.Absorb.Arithmetic

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Absorb.Direct

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

theorem large [Bindings] {l : Layout} {initial before s : RamState} {n reserve : Nat}
    {regions : Vector MemoryRegion n} {data : Input}
    (ctx : Context l initial regions reserve) (input : Preserved l initial before s regions)
    (rip : s.RIP = l.pc .bulkSetup) (hasher : HasherAt s (l.buffer (l.sp initial)) ByteArray.empty l.initialHash)
    (source : s.regValue .rsi = data.address)
    (length : s.regValue .r14 = BitVec.ofNat 64 data.bytes.size)
    (bytes : data.region.HasBytes s.external data.bytes) (bounded : data.region.Bounded)
    (apart : data.region.Disjoint (Stack.region initial reserve)) :
    ∃ t, Finished l initial before t regions data := by
  have low : data.address.toNat+data.bytes.size<2^32 := bounded
  have lengthNat : (s.regValue .r14).toNat=data.bytes.size := by
    rw [length,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have localInput := Preserved.initial input.state input.rsp
  obtain ⟨u,inputU,setup⟩ := run_stage ctx localInput .bulkSetup rip
  have setupFrame := ctx.store_frame .bulkSetup (.inr (.inr rfl)) setup
  simp only [ite_true] at setupFrame
  have outputU : u.regValue .rdi = l.buffer (l.sp initial)+64 := setup.writes.1
  have countU : u.regValue .rdx = BitVec.ofNat 64 (data.bytes.size/64) :=
    setup.writes.2.1.trans ((Wrapper.Absorb.block_count _).trans (by rw [lengthNat]))
  have sourceU : u.regValue .rsi=data.address :=
    (setup.agrees.read (n := 64) (r := 6)
      (by simp [Stage.effect,Effect.components,Write.component,Operand.component])).trans source
  have tailU : u.regValue .r14=BitVec.ofNat 64 (data.bytes.size%64) :=
    setup.writes.2.2.2.1.trans ((Wrapper.Absorb.tail_length _).trans (by rw [lengthNat]))
  have sourceTailU : u.regValue .r15=data.address+BitVec.ofNat 64 (64*(data.bytes.size/64)) := by
    have value : u.regValue .r15 = s.regValue .rsi+(s.regValue .r14 &&& 0x7fffffffffffffc0) :=
      setup.writes.2.2.1
    rw [value,source,BitVec.and_comm,
      Wrapper.Absorb.full_length _ (by rw [lengthNat]; omega),lengthNat]
  have counterU : memLoad u.external (l.buffer (l.sp initial)+96) 64 =
      BitVec.ofNat 64 (data.bytes.size/64) :=
    setup.writes.2.2.2.2.trans ((Wrapper.Absorb.block_count _).trans (by rw [lengthNat]))
  have initialWords : HashStateAt u (l.buffer (l.sp initial)+64) l.initialHash := by
    apply Wrapper.hashState_of_bytes (s := s)
      (by simpa [compressBlocks,compressBlocksFrom] using hasher.hashWords)
    exact ctx.frame_keeps_buffer input.state (written := 96) (width := 8)
      (by simpa only [BitVec.ofNat_eq_ofNat] using setupFrame)
      (offset := 64) (len := 32) (by decide) (by decide : 96+8≤104) (.inl (by decide))
  have bytesU := Preserved.input_bytes ctx inputU bytes bounded apart
  obtain ⟨fullBytes,fullBounded,fullApart⟩ := Common.Memory.input_slice bytesU bounded apart
    (offset := 0) (count := 64*(data.bytes.size/64)) (by omega)
  have fullRegion : registerRegion u .rsi (64*(data.bytes.size/64)) =
      (⟨(data.address+BitVec.ofNat 64 0).toNat,64*(data.bytes.size/64)⟩ : MemoryRegion) := by
    simp only [registerRegion,sourceU,BitVec.add_zero]
  obtain ⟨v,inputV,ripV,wordsV,postV,compressFrame⟩ := compress ctx inputU setup.rip outputU countU
    (fullRegion ▸ fullBytes) (fullRegion ▸ fullBounded) (fullRegion ▸ fullApart) initialWords
  have fullPostV := postV
  obtain ⟨_,_,called,effectCall,result⟩ := fullPostV
  have tailV : v.regValue .r14=BitVec.ofNat 64 (data.bytes.size%64) :=
    (call_result_register effectCall result.toCalleeResult (r := 14) (by decide) (by decide)).trans tailU
  have sourceTailV : v.regValue .r15=data.address+BitVec.ofNat 64 (64*(data.bytes.size/64)) :=
    (call_result_register effectCall result.toCalleeResult (r := 15) (by decide) (by decide)).trans sourceTailU
  have counterV : memLoad v.external (l.buffer (l.sp initial)+96) 64 =
      BitVec.ofNat 64 (data.bytes.size/64) := by
    rw [← counterU]
    apply memLoad_congr
    intro i hi
    apply congrArg (fun b : Option UInt8 => b.getD 0)
    exact ctx.frame_keeps_buffer inputU.state (written := 64) (width := 32)
      (by simpa only [BitVec.ofNat_eq_ofNat] using compressFrame)
      (offset := 96) (len := 8) (by decide) (by decide) (.inr (by decide)) i hi
  obtain ⟨w,inputW,store⟩ := run_stage ctx inputV .bulkTail ripV
  have storeFrame := ctx.store_frame .bulkTail (.inr (.inl rfl)) store
  simp only [ite_eq_right (show Stage.bulkTail ≠ Stage.bulkSetup by decide)] at storeFrame
  have sourceTailW : w.regValue .r15=data.address+BitVec.ofNat 64 (64*(data.bytes.size/64)) :=
    (store.agrees.read (n := 64) (r := 15)
      (by simp [Stage.effect,Effect.components,Write.component,Operand.component])).trans sourceTailV
  have tailW : w.regValue .r14=BitVec.ofNat 64 (data.bytes.size%64) :=
    (store.agrees.read (n := 64) (r := 14)
      (by simp [Stage.effect,Effect.components,Write.component,Operand.component])).trans tailV
  have wordsW : HashStateAt w (l.buffer (l.sp initial)+64)
      (compressBlocks l.initialHash (fullBlocks data.bytes)) := by
    apply Wrapper.hashState_of_bytes (s := v) (by
      simpa only [fullBlocks,Nat.zero_add] using wordsV)
    exact ctx.frame_keeps_buffer inputV.state (written := 63) (width := 1)
      (by simpa only [BitVec.ofNat_eq_ofNat] using storeFrame)
      (offset := 64) (len := 32) (by decide) (by decide : 63+1≤104) (.inr (by decide))
  have counterW : memLoad w.external (l.buffer (l.sp initial)+96) 64 =
      BitVec.ofNat 64 (data.bytes.size/64) := by
    rw [← counterV]
    apply memLoad_congr
    intro i hi
    apply congrArg (fun b : Option UInt8 => b.getD 0)
    exact ctx.frame_keeps_buffer inputV.state (written := 63) (width := 1)
      (by simpa only [BitVec.ofNat_eq_ofNat] using storeFrame)
      (offset := 96) (len := 8) (by decide) (by decide : 63+1≤104) (.inr (by decide)) i hi
  have tailByteW : w.external[l.buffer (l.sp initial)+63]?=some (UInt8.ofNat (data.bytes.size%64)) := by
    have stored : memLoad w.external (l.buffer (l.sp initial)+63) 8=(v.regValue .r14).setWidth 8 := store.writes
    have read := ctx.readable inputW.state (offset := 63) (len := 1) (by decide)
    have byte := Bytes.of_memLoad (n := 8) read.mem 0 (by decide)
    simp only [BitVec.ofNat_eq_ofNat] at stored
    rw [stored,tailV] at byte
    have bound := Nat.mod_lt data.bytes.size (by decide : 0<64)
    simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_zero,storedByte,Nat.mul_zero,Nat.shiftRight_zero,
      BitVec.toNat_setWidth,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : data.bytes.size%64<2^64),
      Nat.mod_eq_of_lt (by omega : data.bytes.size%64<2^8)] using byte
  obtain ⟨x,inputX,tailSetup⟩ := run_stage ctx inputW .tailSetup store.rip
  have memoryX := tailSetup.agrees.external
    (by simp [Stage.effect,Effect.components,Write.component,Operand.component,Component.Covers])
  have outputX : x.regValue .rdi=l.buffer (l.sp initial) := tailSetup.writes.1
  have sourceX : x.regValue .rsi=data.address+BitVec.ofNat 64 (64*(data.bytes.size/64)) :=
    tailSetup.writes.2.1.trans sourceTailW
  have countX : x.regValue .rdx=BitVec.ofNat 64 (data.bytes.size%64) := tailSetup.writes.2.2.trans tailW
  have bytesX := Preserved.input_bytes ctx inputX bytes bounded apart
  obtain ⟨tailBytes,tailBounded,tailApart⟩ := Common.Memory.input_slice bytesX bounded apart
    (offset := 64*(data.bytes.size/64)) (count := data.bytes.size%64) (by omega)
  have tailRegion : registerRegion x .rsi (data.bytes.size%64) =
      (⟨(data.address+BitVec.ofNat 64 (64*(data.bytes.size/64))).toNat,data.bytes.size%64⟩ : MemoryRegion) := by
    simp only [registerRegion,sourceX]
  obtain ⟨t,inputT,postT,copied,copyFrame⟩ := copy ctx inputX l.tailCall (by simp) tailSetup.rip outputX countX
    (by omega) (tailRegion ▸ tailBytes) (tailRegion ▸ tailBounded) (tailRegion ▸ tailApart)
    (by rw [ctx.flow.tailReturn]; exact ctx.code.exitInside)
  have wordsT : HashStateAt t (l.buffer (l.sp initial)+64)
      (compressBlocks l.initialHash data.bytes) := by
    apply Wrapper.hashState_of_bytes (s := w)
      (by simpa only [compressBlocks_fullBlocks] using wordsW)
    intro i hi
    exact (ctx.frame_keeps_buffer inputX.state (written := 0) (width := data.bytes.size%64)
      (by simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_zero] using copyFrame)
      (offset := 64) (len := 32) (by decide) (by omega) (.inr (by omega)) i hi).trans
      (by simp [memoryX])
  have counterT : memLoad t.external (l.buffer (l.sp initial)+96) 64 =
      BitVec.ofNat 64 (data.bytes.size/64) := by
    rw [← counterW]
    apply memLoad_congr
    intro i hi
    apply congrArg (fun b : Option UInt8 => b.getD 0)
    exact (ctx.frame_keeps_buffer inputX.state (written := 0) (width := data.bytes.size%64)
      (by simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_zero] using copyFrame)
      (offset := 96) (len := 8) (by decide) (by omega) (.inr (by omega)) i hi).trans
      (by simp [memoryX,PhysicalMemory.read])
  have tailT : t.external[l.buffer (l.sp initial)+63]?=some (UInt8.ofNat (data.bytes.size%64)) := by
    have kept := ctx.frame_keeps_buffer inputX.state (written := 0) (width := data.bytes.size%64)
      (by simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_zero] using copyFrame)
      (offset := 63) (len := 1) (by decide) (by omega) (.inr (by omega)) 0 (by decide)
    have bound := Nat.mod_lt data.bytes.size (by decide : 0<64)
    have same : t.external[l.buffer (l.sp initial)+63]? =
        w.external[l.buffer (l.sp initial)+63]? := by simpa [memoryX] using kept
    exact same.trans tailByteW
  refine ⟨t,⟨inputT.state,postT.1.trans ctx.flow.tailReturn,inputT.rsp,
    ⟨wordsT,?_,tailT,counterT⟩,memoryWriteFrame_trans input.memory inputT.memory,
    fun r small kept => (inputT.registers r small kept).trans (input.registers r small kept)⟩⟩
  have endEq : 64*(data.bytes.size/64)+data.bytes.size%64=data.bytes.size := by omega
  simpa only [remainderBytes,endEq] using copied

end Sha2.Proofs.Common.SHA256.Absorb.Direct
