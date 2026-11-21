import Sha2.Proofs.Common.SHA256.Absorb.DirectProof.Bytes
import Sha2.Proofs.Wrapper.Absorb.Mathematics

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Absorb.Direct

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

theorem small [Bindings] {l : Layout} {initial before s : RamState} {n reserve : Nat}
    {regions : Vector MemoryRegion n} {data : Input}
    (ctx : Context l initial regions reserve) (input : Preserved l initial before s regions)
    (rip : s.RIP = l.pc .smallSetup) (hasher : HasherAt s (l.buffer (l.sp initial)) ByteArray.empty l.initialHash)
    (source : s.regValue .rsi = data.address)
    (length : s.regValue .r14 = BitVec.ofNat 64 data.bytes.size)
    (bytes : data.region.HasBytes s.external data.bytes) (bounded : data.region.Bounded)
    (apart : data.region.Disjoint (Stack.region initial reserve)) (small : data.bytes.size ≤ 63) :
    ∃ t, Finished l initial before t regions data := by
  obtain ⟨u,inputU,setup⟩ := run_stage ctx input .smallSetup rip
  have memoryU := setup.agrees.external
    (by simp [Stage.effect,Effect.components,Write.component,Operand.component,Component.Covers])
  have outputU : u.regValue .rdi = l.buffer (l.sp initial) := setup.writes.1
  have countU : u.regValue .rdx = BitVec.ofNat 64 data.bytes.size := setup.writes.2.trans length
  have sourceU : u.regValue .rsi = data.address :=
    (setup.agrees.read (n := 64) (r := 6)
      (by simp [Stage.effect,Effect.components,Write.component,Operand.component])).trans source
  have inputRegion : registerRegion u .rsi data.bytes.size = data.region := by
    simp only [registerRegion,sourceU,Input.region]
  have bytesU : data.region.HasBytes u.external data.bytes := by rw [memoryU]; exact bytes
  obtain ⟨v,inputV,post,copied,copyFrame⟩ := copy ctx inputU l.smallCall (by simp) setup.rip outputU countU small
    (inputRegion ▸ bytesU) (inputRegion ▸ bounded) (inputRegion ▸ apart)
    (by rw [ctx.flow.smallReturn]; exact ctx.code.inside .smallStore)
  have fullPost := post
  obtain ⟨_,_,called,effectCall,result,_⟩ := fullPost
  have lengthV : v.regValue .r14 = BitVec.ofNat 64 data.bytes.size :=
    (call_result_register effectCall result (r := 14) (by decide) (by decide)).trans
      ((setup.agrees.read (n := 64) (r := 14)
        (by simp [Stage.effect,Effect.components,Write.component,Operand.component])).trans length)

  obtain ⟨t,inputT,store⟩ := run_stage ctx inputV .smallStore (post.1.trans ctx.flow.smallReturn)
  have storeFrame := ctx.store_frame .smallStore (.inl rfl) store
  simp only [ite_eq_right (show Stage.smallStore ≠ Stage.bulkSetup by decide)] at storeFrame
  have copiedKept := ctx.frame_keeps_buffer inputV.state (written := 63) (width := 1)
    (by simpa only [BitVec.ofNat_eq_ofNat] using storeFrame)
    (offset := 0) (len := data.bytes.size) (by omega) (by decide : 63+1≤104) (.inl (by omega))
  have tailBytes : (⟨(l.buffer (l.sp initial)).toNat,data.bytes.size⟩ : MemoryRegion).HasBytes
      t.external data.bytes := by
    refine ⟨rfl,?_⟩
    intro i
    have h := copiedKept i.val i.isLt
    simp only [BitVec.add_zero] at h
    simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_zero,BitVec.ofNat_add,
      BitVec.ofNat_toNat,BitVec.setWidth_eq] using h.trans (by
        simpa only [BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq] using copied.2 i)
  have hashCopied := ctx.frame_keeps_buffer inputU.state (written := 0) (width := data.bytes.size)
    (by simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_zero] using copyFrame)
    (offset := 64) (len := 32) (by decide) (by omega) (.inr (by omega))
  have hashStored := ctx.frame_keeps_buffer inputV.state (written := 63) (width := 1)
    (by simpa only [BitVec.ofNat_eq_ofNat] using storeFrame)
    (offset := 64) (len := 32) (by decide) (by decide : 63+1≤104) (.inr (by decide))
  have words : HashStateAt t (l.buffer (l.sp initial)+64) l.initialHash := by
    apply Wrapper.hashState_of_bytes (s := s) (by simpa [compressBlocks,compressBlocksFrom] using hasher.hashWords)
    intro i hi
    exact (hashStored i hi).trans ((hashCopied i hi).trans (by rw [memoryU]))
  have blocksCopied := ctx.frame_keeps_buffer inputU.state (written := 0) (width := data.bytes.size)
    (by simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_zero] using copyFrame)
    (offset := 96) (len := 8) (by decide) (by omega) (.inr (by omega))
  have blocksStored := ctx.frame_keeps_buffer inputV.state (written := 63) (width := 1)
    (by simpa only [BitVec.ofNat_eq_ofNat] using storeFrame)
    (offset := 96) (len := 8) (by decide) (by decide : 63+1≤104) (.inr (by decide))
  have blocks : memLoad t.external (l.buffer (l.sp initial)+96) 64 = 0 := by
    have original : memLoad s.external (l.buffer (l.sp initial)+96) 64 = 0 := hasher.blocks
    rw [← original]
    apply memLoad_congr
    intro i hi
    apply congrArg (fun b : Option UInt8 => b.getD 0)
    exact (blocksStored i hi).trans ((blocksCopied i hi).trans (by simp [memoryU,PhysicalMemory.read]))
  have tail : t.external[l.buffer (l.sp initial)+63]? = some (UInt8.ofNat data.bytes.size) := by
    have stored : memLoad t.external (l.buffer (l.sp initial)+63) 8 =
        (v.regValue .r14).setWidth 8 := store.writes
    have read := ctx.readable inputT.state (offset := 63) (len := 1) (by decide)
    have byte := Bytes.of_memLoad (n := 8) read.mem 0 (by decide)
    simp only [BitVec.ofNat_eq_ofNat] at stored
    rw [stored,lengthV] at byte
    simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_zero,storedByte,Nat.mul_zero,Nat.shiftRight_zero,
      BitVec.toNat_setWidth,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : data.bytes.size<2^64),
      Nat.mod_eq_of_lt (by omega : data.bytes.size<2^8)] using byte
  refine ⟨t,⟨inputT.state,store.rip,inputT.rsp,?_,inputT.memory,inputT.registers⟩⟩
  refine ⟨?_,?_,?_,?_⟩
  · rw [Wrapper.Absorb.compressBlocks_short _ _ (by omega)]
    exact words
  · simpa only [Nat.mod_eq_of_lt (by omega : data.bytes.size<64),
      Wrapper.Absorb.remainderBytes_short data.bytes (by omega)] using tailBytes
  · simpa only [Nat.mod_eq_of_lt (by omega : data.bytes.size<64)] using tail
  · simpa [Nat.div_eq_of_lt (by omega : data.bytes.size<64)] using blocks

end Sha2.Proofs.Common.SHA256.Absorb.Direct
