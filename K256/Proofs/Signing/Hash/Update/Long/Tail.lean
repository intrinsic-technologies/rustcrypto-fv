import K256.Proofs.Signing.Hash.Update.Copy
import K256.Proofs.Verify.Hash.Update.Dispatch
import K256.Proofs.Verify.Hash.Update.Lengths
import K256.Proofs.Verify.LIR.Generated.Values
import K256.Proofs.Verify.Core.State
import K256.Proofs.Common.SignatureRun
import K256.Proofs.ParseSignature.Call

namespace K256.Proofs.Signing.Hash

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
open K256.Proofs.Verify.Hash

namespace Update

set_option maxRecDepth 4096 in
private theorem enterTail {c : Values Value Reg.count} {t : Ram} {sp src size : BitVec 64}
    (rsp : c[4] = ⟨64, sp⟩) (source : c[6] = ⟨64, src⟩)
    (length : c[13] = ⟨64, size⟩) (memcpy : c[15] = ⟨64, 0x12a820⟩)
    (small : size.toNat < 2^63)
    (store : StoreOk Extracted.programImage t (sp + 551) 1 0x10558c 8)
    (push : StoreOk Extracted.programImage
      (memStore t (sp + 551) (BitVec.ofNat 8 (size.toNat % 64))) (sp - 8) 8 0x10559f 3) :
    ∃ d : Values Value Reg.count,
      program.runBlock (dialect Extracted.programImage) ⟨.l105575, c, t⟩ =
        .call ⟨.l12a820, d, memStore
          (memStore t (sp + 551) (BitVec.ofNat 8 (size.toNat % 64))) (sp - 8)
          (0x1055a2 : BitVec 64)⟩ (Verify.Hash.Update.returnFrame .l1055a2 0x1055a2) ∧
      d[2].get 64 = BitVec.ofNat 64 (size.toNat % 64) ∧ d[4].get 64 = sp - 8 ∧
      d[6].get 64 = src + BitVec.ofNat 64 (64 * (size.toNat / 64)) ∧
      d[7].get 64 = sp + 488 ∧ d[13].width = 64 ∧
      (∀ i : Fin Reg.count, i.val ∈ [3,5,12,14,22,39,50,51] → d[i] = c[i]) := by
  have sp' : c[4].get 64 = sp := by rw [rsp]; rfl
  have src' : c[6].get 64 = src := by rw [source]; rfl
  have n' : c[13].get 64 = size := by rw [length]; rfl
  have lo' : c[13].get 32 = size.setWidth 32 := by rw [length]; rfl
  have fn' : c[15].get 64 = 0x12a820 := by rw [memcpy]; rfl
  have full : size &&& 0x7fffffffffffffc0 = BitVec.ofNat 64 (64 * (size.toNat / 64)) := by
    rw [BitVec.and_comm, Verify.Hash.Update.full_length _ small]
  have rem := Verify.Hash.Update.tail_length size
  have rem8 : (BitVec.ofNat 64 (size.toNat % 64)).setWidth 8 =
      BitVec.ofNat 8 (size.toNat % 64) :=
    BitVec.setWidth_ofNat_of_le (by decide : 8 ≤ 64) _
  refine ⟨?_, ?run, ?post⟩
  case run =>
    cfg_eval [sp', src', n', lo', fn', full, rem, store]
    rw [rem8, ite_eq_left push]
  case post =>
    refine ⟨rfl, rfl, rfl, rfl, rfl, ?_⟩
    intro ⟨i, _⟩ hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

set_option maxRecDepth 4096 in
private theorem leaveTail {c : Values Value Reg.count} {t : Ram} {sp : BitVec 64}
    (limit : c[3] = ⟨64, sp + 1152⟩) (slice : c[14] = ⟨64, sp + 1136⟩) :
    ∃ b, Verify.Core.Reaches .l1055a2 c t .l1055bf b t ∧
      (∀ i : Fin Reg.count, i.val ∈ [4,5,12,13,22,39,50,51] → b[i] = c[i]) := by
  have next : sp + 1136 + 16 = sp + 1152 := by rw [BitVec.add_assoc]; rfl
  have equal : (cmpSpec (sp + 1152) (sp + 1152)).ZF = true := by
    simp only [cmpSpec, subSpec, BitVec.sub_self]
    decide
  have sl' : c[14].get 64 = sp + 1136 := by rw [slice]; rfl
  have lim' : c[3].get 64 = sp + 1152 := by rw [limit]; rfl
  have step : ∃ d : Values Value Reg.count,
      program.runBlock (dialect Extracted.programImage) ⟨.l1055a2, c, t⟩ =
        .jump ⟨.l1055af, d, t⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [4,5,12,13,22,39,50,51] → d[i] = c[i]) := by
    refine ⟨?_, ?run, ?post⟩
    case run =>
      cfg_eval [sl', lim', next, equal]
      rfl
    case post =>
      intro ⟨i, _⟩ hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  obtain ⟨d, step, preserved⟩ := step
  have jump : ∃ b : Values Value Reg.count,
      program.runBlock (dialect Extracted.programImage) ⟨.l1055af, d, t⟩ =
        .jump ⟨.l1055bf, b, t⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [4,5,12,13,22,39,50,51] → b[i] = d[i]) := by
    refine ⟨?_, ?run, ?post⟩
    case run =>
      cfg_eval
      rfl
    case post =>
      intro ⟨i, _⟩ hi
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  obtain ⟨b, jump, kept⟩ := jump
  exact ⟨b, .step (congrArg (Transfer.next _ []) step)
    (.step (congrArg (Transfer.next _ []) jump) (.refl _)), fun i hi => (kept i hi).trans (preserved i hi)⟩

set_option maxRecDepth 4096 in
set_option maxHeartbeats 600000 in
theorem finishSlice {a : Values Value Reg.count} {m : Ram} {sp src : BitVec 64}
    {message : ByteArray}
    {c : Values Value Reg.count} {t : Ram}
    (frame : Frame sp a c m t) (limitReg : c[3] = ⟨64, sp+1152⟩) (rbp : c[5].width = 64)
    (source : c[6] = ⟨64,src⟩) (r12 : c[12].width = 64)
    (length : c[13] = ⟨64, BitVec.ofNat 64 message.size⟩)
    (slice : c[14] = ⟨64, sp+1136⟩) (memcpy : c[15] = ⟨64, 0x12a820⟩)
    (hash : Compression.StateAt t (sp + 552) (compressBlocks initialHash message))
    (blocks : memLoad t (sp + 584) 64 = BitVec.ofNat 64 (message.size/64))
    (_image : ∀ b ∈ Extracted.programImage, m[b.1]? = some b.2)
    (bytes : (⟨src.toNat, message.size⟩ : MemoryRegion).HasBytes m message)
    (input : Readable m src message.size)
    (stack : Writable Extracted.programImage m (sp - 512) 1672)
    (depth : 512 ≤ sp.toNat) (limit : sp.toNat + 1160 < 2^32)
    (inputLow : src.toNat + message.size < 2^32)
    (apart : src.toNat + message.size ≤ sp.toNat - 512 ∨ sp.toNat + 1160 ≤ src.toNat) :
    ∃ b u, (program.sem (dialect Extracted.programImage)).Reaches
      ⟨⟨.l105575, c, t⟩, []⟩ ⟨⟨.l1055bf, b, u⟩, []⟩ ∧
      Frame sp a b m u ∧ Buffer sp message b u := by
  let n := message.size % 64
  let count := BitVec.ofNat 64 n
  let tail := src + BitVec.ofNat 64 (64 * (message.size / 64))
  let marked := memStore t (sp + 551) (BitVec.ofNat 8 n)
  let pushed := memStore marked (sp - 8) (0x1055a2 : BitVec 64)
  let staging : List MemoryRegion := [⟨(sp - 8).toNat, 8⟩, ⟨sp.toNat + 488, 64⟩]
  have countNat : count.toNat = n := by
    exact Nat.mod_eq_of_lt (by dsimp only [n]; omega)
  have sizeNat : (BitVec.ofNat 64 message.size).toNat = message.size :=
    Nat.mod_eq_of_lt (by omega)
  have atNat (off : Nat) (bound : off ≤ 1160) :
      (sp + BitVec.ofNat 64 off).toNat = sp.toNat + off :=
    toNat_add_ofNat _ _ (by omega)
  have bottom : (sp - 512).toNat = sp.toNat - 512 :=
    BitVec.toNat_sub_of_le (show (512 : BitVec 64) ≤ sp from depth)
  have slotNat : (sp - 8).toNat = sp.toNat - 8 :=
    BitVec.toNat_sub_of_le (show (8 : BitVec 64) ≤ sp from (by change 8 ≤ sp.toNat; omega))
  have lengthNat : (sp + 551).toNat = sp.toNat + 551 := atNat 551 (by decide)
  have bufferNat : (sp + 488).toNat = sp.toNat + 488 := atNat 488 (by decide)
  have blocksNat : (sp + 584).toNat = sp.toNat + 584 := atNat 584 (by decide)
  have lengthWithin : InRegions staging (sp + 551) 1 :=
    ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by
      change sp.toNat + 488 ≤ _ ∧ _ ≤ sp.toNat + 488 + 64 ∧ _
      omega⟩
  have pushWithin : InRegion ⟨(sp - 8).toNat, 8⟩ (sp - 8) 8 :=
    ⟨Nat.le_refl _, Nat.le_refl _, by omega⟩
  have stagedWithin : RegionsWithin staging (regions sp) := by
    intro r hr
    simp only [staging, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, by change sp.toNat - 512 ≤ (sp - 8).toNat; omega,
        by change (sp - 8).toNat + 8 ≤ sp.toNat - 512 + 624; omega⟩
    · refine ⟨⟨sp.toNat + 488, 104⟩, ?_, Nat.le_refl _, ?_⟩
      · exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
      · change sp.toNat + 488 + 64 ≤ sp.toNat + 488 + 104
        omega
  have markedFrame : RamWriteFrame t marked staging :=
    (RamWriteFrame.refl _ _).memStore _ lengthWithin
  have pushedFrame : RamWriteFrame t pushed staging := markedFrame.memStore _ ⟨_, List.mem_cons_self, pushWithin⟩
  have window := stack.of_frame frame.writes
  have included x hx := Common.fnCode_subset_programImage x (code_l105575 x hx)
  have lengthStore : StoreOk Extracted.programImage t (sp + 551) 1 0x10558c 8 :=
    ParseSignature.storeOk_of_codeRange (off := 23) (window.sub (by omega) (by omega))
      included (by decide)
  have returnStore : StoreOk Extracted.programImage marked (sp - 8) 8 0x10559f 3 :=
    ParseSignature.storeOk_of_codeRange (off := 42)
      ((window.of_frame markedFrame).sub (by omega) (by omega)) included (by decide)
  obtain ⟨d, call, lenReg, spReg, srcReg, dstReg, remWidth, setupKept⟩ :=
    enterTail frame.rsp source length memcpy (by rw [sizeNat]; omega) lengthStore
      (by simpa only [sizeNat] using returnStore)
  rw [sizeNat] at call lenReg srcReg
  have ddf : d[22].get 1 = 0 :=
    congrArg (Value.get 1) ((setupKept 22 (by decide)).trans frame.df)
  have retWord : memLoad pushed (sp - 8) 64 = 0x1055a2 :=
    memLoad_memStore_same _ _ _ (by decide) (by decide)
  obtain ⟨out, run, copied, tag, outSp, copyKept, writes, remainder⟩ :=
    copyTail (n := count) (tail := tail) dstReg srcReg lenReg spReg ddf rfl countNat
      (frame.writes.trans pushedFrame stagedWithin) bytes input stack depth limit inputLow (fun _ => apart)
      (by rw [retWord]; decide)
  obtain ⟨b, finish, finishKept⟩ := leaveTail
    (((copyKept 3 (by decide)).trans (setupKept 3 (by decide))).trans limitReg)
    (((copyKept 14 (by decide)).trans (setupKept 14 (by decide))).trans slice)
  have resumed : Verify.Core.Reaches .l105575 c t .l1055a2 out.values out.store := by
    refine .step (congrArg (Transfer.next _ []) call) ?_
    have ret := ParseSignature.exec_reaches_resume run
      (Verify.Hash.Update.returnFrame .l1055a2 0x1055a2) [] (by rw [tag, retWord]; rfl)
    exact ret
  have keep (i : Fin Reg.count) (hi : i.val ∈ [5,12,22,39,50,51]) : b[i] = c[i] := by
    refine (finishKept i ?_).trans ((copyKept i ?_).trans (setupKept i ?_)) <;>
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢ <;> omega
  let copyRegions : List MemoryRegion := [⟨(sp - 8).toNat, 8⟩, ⟨sp.toNat + 488, n⟩]
  have afterMark : RamWriteFrame marked out.store copyRegions := by
    rw [copied]
    have pushFrame : RamWriteFrame marked pushed copyRegions :=
      (RamWriteFrame.refl _ _).memStore _
        ⟨_, List.mem_cons_self, pushWithin⟩
    exact Sec1.Wrapper.Copy.memCopy_frame pushFrame
      ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, by
        change sp.toNat + 488 ≤ _ ∧ _ ≤ sp.toNat + 488 + n ∧ _
        rw [countNat]
        dsimp only [n]
        omega⟩
  have copyRegionsWithin : RegionsWithin copyRegions staging := by
    intro r hr
    simp only [copyRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨_, List.mem_cons_of_mem _ List.mem_cons_self, Nat.le_refl _, by
        change sp.toNat + 488 + n ≤ sp.toNat + 488 + 64
        dsimp only [n]
        omega⟩
  have updated := markedFrame.trans afterMark copyRegionsWithin
  have afterBuffer (ptr : BitVec 64) (len : Nat)
      (start : sp.toNat + 552 ≤ ptr.toNat) (bound : ptr.toNat + len ≤ 2^64) :
      Outside staging ptr len := by
    refine ⟨bound, fun r hr => ?_⟩
    simp only [staging, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> right <;> dsimp only <;> omega
  have hash' : Compression.StateAt out.store (sp + 552) (compressBlocks initialHash message) := by
    refine ⟨hash.1, fun i hi => (updated.memLoad_eq ?_).trans (hash.2 i hi)⟩
    have addr : (wordAddr (sp + 552) 32 i).toNat = sp.toNat + (552 + 4*i) := by
      change (sp + BitVec.ofNat 64 552 + BitVec.ofNat 64 (4*i)).toNat = _
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, atNat _ (by omega)]
    exact afterBuffer _ _ (by rw [addr]; omega) (by rw [addr]; omega)
  have blocks' : memLoad out.store (sp + 584) 64 = BitVec.ofNat 64 (message.size / 64) :=
    (updated.memLoad_eq (afterBuffer _ _ (by omega) (by omega))).trans blocks
  have length' : memLoad out.store (sp + 551) 8 = BitVec.ofNat 8 n := by
    refine (afterMark.memLoad_eq ⟨by omega, fun r hr => ?_⟩).trans
      (memLoad_memStore_same _ _ _ (by decide) (by decide))
    simp only [copyRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> right <;> dsimp only [n] <;> omega
  refine ⟨b, out.store, resumed.trans finish,
    ⟨(finishKept 4 (by decide)).trans outSp, (keep 22 (by decide)).trans frame.df,
      fun i hi => (keep i (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
        omega)).trans (frame.kept i hi), writes⟩,
    ⟨?_, hash', remainder, length', blocks'⟩⟩
  intro ⟨i, hi⟩ h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl
  · exact (congrArg Value.width (keep 5 (by decide))).trans rbp
  · exact (congrArg Value.width (keep 12 (by decide))).trans r12
  · exact (congrArg Value.width ((finishKept 13 (by decide)).trans
      (copyKept 13 (by decide)))).trans remWidth

end Update
end K256.Proofs.Signing.Hash
