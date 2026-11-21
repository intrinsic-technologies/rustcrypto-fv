import AesGcm.Proofs.Machine.Entry.InPlaceEncrypt.CoreResult
import AesGcm.Proofs.Machine.Entry.InPlaceEncrypt.Finish
import AesGcm.Proofs.Machine.Runtime.MemorySlices
import AesGcm.Proofs.Machine.Runtime.Root.Program
import AesGcm.Proofs.Machine.Runtime.StackGeometry

namespace AesGcm.Proofs.Machine.Entry.InPlaceEncrypt

open AesGcm.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

set_option maxHeartbeats 1000000 in
set_option maxRecDepth 2048 in
theorem exec_of_corePost {initial : RamState} {key : Vector UInt8 16} {nonce : Vector UInt8 12}
    {aad bytes ciphertext : ByteArray} {capacity : Nat} {ret : BitVec 64} {tag : Vector UInt8 16}
    (hCall : ValidCall initial key nonce aad bytes capacity)
    (args : Values Value Reg.count) (mem : Ram)
    (hCore : corePost initial ret bytes capacity ciphertext tag args mem) :
    let fr := entryActivation initial ret
    let fit := fr.r9.toNat + 16 ≤ capacity
    let size := if fit then bytes.size + 16 else bytes.size
    ∃ output, LIR.program.Exec (dialect Extracted.programImage) ⟨⟨.l101409, args, mem⟩, []⟩ output ∧
      output.tag = some ⟨64, fr.ret⟩ ∧
      Atom.All Extracted.programImage output.values output.store
        (LIR.Aes128gcmEncryptInPlace.frameInfo.doneAtoms fr) ∧
      output.values[0] = ⟨64, if fit then 0 else 1⟩ ∧
      RamWriteFrame fr.original output.store [fr.region, span fr.r8 size] ∧
      (span fr.r8 size).HasBytes output.store
        (if fit then ciphertext ++ ⟨tag.toArray⟩ else ciphertext) := by
  let fr := entryActivation initial ret
  obtain ⟨atoms, types, cap, before, status, cipher, tagBytes⟩ := hCore
  change RamWriteFrame fr.original mem [fr.region, span fr.r8 bytes.size] at before
  change (span fr.r8 bytes.size).HasBytes mem ciphertext at cipher
  rcases atoms with ⟨sp, df, len, _, _, buf, _, mx, ft, fc, s3, s12, s13, s14, s15, s5,
    readRet, retSlot, retLow, stack, room, _⟩
  change args[4] = ⟨64, fr.rsp - 472⟩ at sp
  change args[3] = ⟨64, fr.r9⟩ at len
  change args[14] = ⟨64, fr.r8⟩ at buf
  change fr.low.toNat + 2848 ≤ fr.rsp.toNat at room
  change Writable Extracted.programImage mem (fr.rsp - 2848) 2848 at stack
  change Readable mem fr.rsp 8 at readRet
  change memLoad mem fr.rsp 64 = fr.ret at retSlot
  have hsp : args[4].get 64 = fr.rsp - 472 := by rw [sp]; rfl
  have hlen : args[3].get 64 = fr.r9 := by rw [len]; rfl
  have hbuf : args[14].get 64 = fr.r8 := by rw [buf]; rfl
  have hs (k : BitVec 64) (d : BitVec 64) (h : k + d = 472) :
      args[4].get 64 + k = fr.rsp - d := by rw [hsp]; bv_omega
  have hs0 : args[4].get 64 + 472 = fr.rsp := by rw [hsp]; bv_omega
  have hs32 := hs 32 440 (by decide)
  have hsRet := hs 424 48 (by decide)
  have stackRead : Readable mem (args[4].get 64) 480 := by
    have hr : Readable mem (args[4].get 64) 472 := by
      rw [hsp]
      exact stack.readable.of_offsets (addr_sub _ _) (addr_sub _ _) (by decide)
    apply readable_append hr (k := 8)
    rwa [show args[4].get 64 + BitVec.ofNat 64 472 = fr.rsp from hs0]
  have scratch : Writable Extracted.programImage mem (args[4].get 64 + 32) 16 := by
    rw [hs32]
    exact stack.of_offsets (addr_sub _ _) (addr_sub _ _) (by decide)
  have valid : ValidOutput (span fr.r8 capacity) fr.original :=
    hCall.elim (fun h => h.outputInMemory.1) (fun h => h.2.outputInMemory)
  have separation := hCall.elim (fun h => h.separation) (fun h => h.2.separation)
  have avoids : (span fr.r8 capacity).Avoids
      (fun a => InProgram a ∨ pageTables.Contains a.toNat) :=
    separation.2.2.2 _ (List.mem_cons_of_mem _ List.mem_cons_self)
  have apart : (span fr.r8 capacity).Disjoint
      (Stack.region initial aes128gcmEncryptInPlace.minStackBytes 16) :=
    separation.1 (InPlace.outputRegion initial capacity) (by simp)
  have bounded : fr.r8.toNat + capacity < 2^32 := valid.2.1
  have sizeLe : bytes.size ≤ capacity := by
    rcases hCall with h | ⟨rfl, _⟩
    · exact h.outputInMemory.2.1
    · exact Nat.zero_le _
  have lengthFits (h : fr.r9.toNat + 16 ≤ capacity) : fr.r9.toNat = bytes.size := by
    rcases hCall with hc | ⟨_, hc⟩
    · exact hc.lengthArgumentMatchesBuffer
    · have over : capacity < fr.r9.toNat := hc.lengthArgumentExceedsCapacity
      omega
  have addr (h : fr.r9.toNat + 16 ≤ capacity) :
      (fr.r8 + fr.r9).toNat = fr.r8.toNat + bytes.size := by
    rw [BitVec.toNat_add, lengthFits h, Nat.mod_eq_of_lt (by omega)]
  have stackRange (x : Nat) (hlo : fr.low.toNat ≤ x) (hhi : x < fr.rsp.toNat + 16) :
      (Stack.region initial aes128gcmEncryptInPlace.minStackBytes 16).Contains x := by
    have low : fr.low.toNat = fr.rsp.toNat - aes128gcmEncryptInPlace.minStackBytes :=
      Activation.ofEntry_low_toNat
    change fr.rsp.toNat - aes128gcmEncryptInPlace.minStackBytes ≤ x ∧
      x < fr.rsp.toNat - aes128gcmEncryptInPlace.minStackBytes +
        (fr.rsp.toNat + 16 - (fr.rsp.toNat - aes128gcmEncryptInPlace.minStackBytes))
    omega
  have off440 : (args[4].get 64 + 32).toNat = fr.rsp.toNat - 440 := by
    rw [hs32]
    exact stack_sub_toNat fr room (by decide : 440 ≤ 2848)
  have off48 : (args[4].get 64 + 424).toNat = fr.rsp.toNat - 48 := by
    rw [hsRet]
    exact stack_sub_toNat fr room (by decide : 48 ≤ 2848)
  have fitEq : ((args[3].get 64).toNat + 16 ≤ (args[5].get 64).toNat) ↔
      fr.r9.toNat + 16 ≤ capacity := by rw [hlen, cap]
  have tagWrite (h : (args[3].get 64).toNat + 16 ≤ (args[5].get 64).toNat) :
      Writable Extracted.programImage mem (args[14].get 64 + args[3].get 64) 16 := by
    have hf := fitEq.mp h
    rw [hbuf, hlen]
    apply Writable.of_frame (m := mem) _ before
    apply Writable.of_avoids valid.2.1 valid.2.2 avoids
      (fun x hx => Or.inl ⟨x.2, hx⟩) (fun _ hh => Or.inr (not_pageTableEntriesApart_frames hh))
    · change fr.r8.toNat ≤ _
      rw [addr hf]
      omega
    · change _ ≤ fr.r8.toNat + capacity
      rw [addr hf, ← lengthFits hf]
      omega
    · decide
  have tagApart (h : (args[3].get 64).toNat + 16 ≤ (args[5].get 64).toNat) :
      (span (args[14].get 64 + args[3].get 64) 16).Disjoint (span (args[4].get 64 + 424) 56) := by
    intro x hx hy
    have hf := fitEq.mp h
    change (args[14].get 64 + args[3].get 64).toNat ≤ x ∧
      x < (args[14].get 64 + args[3].get 64).toNat + 16 at hx
    change (args[4].get 64 + 424).toNat ≤ x ∧ x < (args[4].get 64 + 424).toNat + 56 at hy
    rw [hbuf, hlen, addr hf, ← lengthFits hf] at hx
    rw [off48] at hy
    exact apart x ⟨by dsimp [span]; omega, by dsimp [span]; omega⟩ (stackRange x (by omega) (by omega))
  obtain ⟨out, run, outMem, outRet, o4, o0, o3, o12, o13, o14, o15, o5, keep, _, writes⟩ :=
    finish_exec false Extracted.programImage fnCode_sub_programImage args mem types stackRead
      (by
        change (memLoad mem (args[4].get 64 + 472) 64).toNat < 2^32
        rwa [hs0, retSlot])
      (by
        rw [memLoad_8]
        change (mem[args[4].get 64 + 15]?.getD 0).toBitVec = 0
        rw [status]
        rfl)
      scratch tagWrite tagApart
  refine ⟨out, run, ?_, ?_, ?_, ?_, ?_⟩
  · change out.tag = some ⟨64, fr.ret⟩
    simpa only [show BitVec.ofNat 64 (frameBytes false) = 472 by rfl, hs0, retSlot] using outRet
  · have endSp : args[4].get 64 + BitVec.ofNat 64 (frameBytes false + 8) = fr.rsp + 8 := by
      rw [hsp]
      change fr.rsp - 472 + 480 = _
      bv_omega
    rw [endSp] at o4
    refine ⟨o4, (keep 22 (by decide)).trans df, ?_, ?_, ?_, ?_, ?_, ?_,
      (keep 39 (by decide)).trans mx, (keep 50 (by decide)).trans ft,
      (keep 51 (by decide)).trans fc, trivial⟩
    · rw [hs _ 48 (by decide)] at o3
      exact o3.trans (congrArg (Value.mk 64) s3)
    · rw [hs _ 8 (by decide)] at o5
      exact o5.trans (congrArg (Value.mk 64) s5)
    · rw [hs _ 40 (by decide)] at o12
      exact o12.trans (congrArg (Value.mk 64) s12)
    · rw [hs _ 32 (by decide)] at o13
      exact o13.trans (congrArg (Value.mk 64) s13)
    · rw [hs _ 24 (by decide)] at o14
      exact o14.trans (congrArg (Value.mk 64) s14)
    · rw [hs _ 16 (by decide)] at o15
      exact o15.trans (congrArg (Value.mk 64) s15)
  · simpa only [fitEq] using o0
  · let n := if fr.r9.toNat + 16 ≤ capacity then bytes.size + 16 else bytes.size
    change RamWriteFrame fr.original out.store [fr.region, span fr.r8 n]
    have hw : RamWriteFrame fr.original mem [fr.region, span fr.r8 n] := by
      apply (RamWriteFrame.refl _ _).trans before
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · exact ⟨_, List.mem_cons_self, Nat.le_refl _, Nat.le_refl _⟩
      · refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Nat.le_refl _, ?_⟩
        change fr.r8.toNat + bytes.size ≤ fr.r8.toNat + n
        dsimp [n]
        split <;> omega
    apply hw.trans writes
    intro r hr
    simp only [tailFootprint, fitEq, List.mem_cons] at hr
    rcases hr with rfl | hr
    · refine ⟨_, List.mem_cons_self, ?_, ?_⟩ <;>
        simp only [Activation.region, span, off440] <;> omega
    · split at hr
      next hf =>
        rcases List.mem_singleton.mp hr with rfl
        refine ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, ?_, ?_⟩ <;>
          simp only [span, hbuf, hlen, addr hf, n, hf, ↓reduceIte] <;> omega
      next => exact False.elim (List.not_mem_nil hr)
  · have hc : (span fr.r8 bytes.size).HasBytes out.store ciphertext := by
      apply hasBytes_of_frame writes cipher (by change fr.r8.toNat + bytes.size ≤ 2^64; omega)
      intro r hr x hx hy
      simp only [tailFootprint, fitEq, List.mem_cons] at hr
      rcases hr with rfl | hr
      · simp only [MemoryRegion.Contains, span, off440] at hx hy
        exact apart x ⟨hx.1, by change x < fr.r8.toNat + capacity; omega⟩
          (stackRange x (by omega) (by omega))
      · split at hr
        next hf =>
          rcases List.mem_singleton.mp hr with rfl
          simp only [MemoryRegion.Contains, span, hbuf, hlen, addr hf] at hx hy
          omega
        next => exact False.elim (List.not_mem_nil hr)
    change (span fr.r8 (if fr.r9.toNat + 16 ≤ capacity then bytes.size + 16 else bytes.size)).HasBytes
      out.store (if fr.r9.toNat + 16 ≤ capacity then ciphertext ++ ⟨tag.toArray⟩ else ciphertext)
    split
    next hf =>
      have ht := tailMemory_tag args mem _ tagBytes (fitEq.mpr hf)
      have clen : ciphertext.size = bytes.size := cipher.1
      have tlen : (ByteArray.mk tag.toArray).size = 16 := tag.size_toArray
      have endAddr : BitVec.ofNat 64 ciphertext.size = fr.r9 := by
        rw [clen, ← lengthFits hf, BitVec.ofNat_toNat]; rfl
      have front : (span fr.r8 ciphertext.size).HasBytes out.store ciphertext := by
        simpa only [clen] using hc
      have suffix : (span (fr.r8 + BitVec.ofNat 64 ciphertext.size)
          (ByteArray.mk tag.toArray).size).HasBytes out.store ⟨tag.toArray⟩ := by
        rw [endAddr, outMem, tlen]
        simpa only [hbuf, hlen] using ht
      simpa only [clen, tlen] using
        hasBytes_append front suffix (by rw [clen]; omega)
    next => exact hc

end AesGcm.Proofs.Machine.Entry.InPlaceEncrypt
