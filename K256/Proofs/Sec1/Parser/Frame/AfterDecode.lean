import K256.Proofs.Sec1.Parser.Result.AfterAffine
import K256.Proofs.Sec1.Parser.Result.Return
import K256.Proofs.Sec1.Decode

namespace K256.Proofs.Sec1.Parser.Frame

open K256.Spec K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Sec1.LIR
open K256.Proofs.Sec1.Parser.Result

private theorem sub_add_eq_sub (sp base delta : BitVec 64) :
    sp - base + delta = sp - (base - delta) := by bv_omega

private theorem savedSlots_afterResult {s : RamState} {bytes : ByteArray} {mem : Ram}
    (call : ValidCall publicKeyFromSec1Bytes s [bytes]) (slots : SavedSlots s mem) (flag : BitVec 8) :
    SavedSlots s (resultStore mem (s.regValue .rsp - 600) (s.regValue .rsp - 112) flag) := by
  let sp := s.regValue .rsp
  let stage : MemoryRegion := ⟨(sp - 528).toNat, 89⟩
  let output : MemoryRegion := ⟨(sp - 104).toNat, 88⟩
  have room : 1928 ≤ sp.toNat := call.stackAvailable.2.2.1
  have addr (off : Nat) (depth : off ≤ 1928) :
      (sp - BitVec.ofNat 64 off).toNat = sp.toNat - off := by
    have literal : (BitVec.ofNat 64 off).toNat = off := Nat.mod_eq_of_lt (by omega)
    rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def, literal]; omega), literal]
  have addrStage : (sp - 528).toNat = sp.toNat - 528 := addr 528 (by decide)
  have addrFlag : (sp - 440).toNat = sp.toNat - 440 := addr 440 (by decide)
  have addrOutput : (sp - 104).toNat = sp.toNat - 104 := addr 104 (by decide)
  have within (off n : Nat) (depth : off ≤ 1928) (fits : n ≤ off + 8) :
      InRegion (Wrapper.stack s) (sp - BitVec.ofNat 64 off) n := by
    obtain ⟨r, hr, inside⟩ := stackRange (off := off) (n := n) call depth fits
    rwa [List.mem_singleton.mp hr] at inside
  have staged : InRegion (Wrapper.stack s) (sp - 528) 89 := within 528 89 (by decide) (by decide)
  have copied : InRegion (Wrapper.stack s) (sp - 104) 88 := within 104 88 (by decide) (by decide)
  have changed : RamWriteFrame mem
      (resultStore mem (sp - 600) (sp - 112) flag) [stage, output] := by
    apply resultStore_frame
    · rw [sub_add_eq_sub]
      refine ⟨stage, List.mem_cons_self, Nat.le_refl _, ?_, ?_⟩
      · change (sp - 528).toNat + 88 ≤ (sp - 528).toNat + 89
        omega
      · change (sp - 528).toNat + 88 ≤ 2 ^ 64
        have := staged.2.2
        omega
    · rw [sub_add_eq_sub]
      refine ⟨stage, List.mem_cons_self, ?_⟩
      change (sp - 528).toNat ≤ (sp - 440).toNat ∧
        (sp - 440).toNat + 1 ≤ (sp - 528).toNat + 89 ∧ (sp - 440).toNat + 1 ≤ 2 ^ 64
      rw [addrStage, addrFlag]
      have h := staged.2.2
      change (sp - 528).toNat + 89 ≤ 2 ^ 64 at h
      rw [addrStage] at h
      omega
    · intro _
      rw [sub_add_eq_sub]
      exact ⟨output, List.mem_cons_of_mem _ List.mem_cons_self, Nat.le_refl _, Nat.le_refl _, copied.2.2⟩
  have allWithin : RegionsWithin [stage, output] [Wrapper.stack s] := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · exact ⟨_, List.mem_cons_self, staged.1, staged.2.1⟩
    · exact ⟨_, List.mem_cons_self, copied.1, copied.2.1⟩
  have keep (off : Nat) (aboveStage : off ≤ 280) (apartOutput : off ≤ 16 ∨ 112 ≤ off) :
      memLoad (resultStore mem (sp - 600) (sp - 112) flag) (sp - BitVec.ofNat 64 off) 64 =
        memLoad mem (sp - BitVec.ofNat 64 off) 64 := by
    apply changed.memLoad_eq
    refine ⟨(within off 8 (by omega) (by omega)).2.2, ?_⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · right
      change (sp - 528).toNat + 89 ≤ (sp - BitVec.ofNat 64 off).toNat
      rw [addrStage, addr off (by omega)]
      omega
    · change (sp - BitVec.ofNat 64 off).toNat + 8 ≤ (sp - 104).toNat ∨
        (sp - 104).toNat + 88 ≤ (sp - BitVec.ofNat 64 off).toNat
      rw [addrOutput, addr off (by omega)]
      omega
  have atReturn := keep 0 (by decide) (by decide)
  change memLoad _ (sp - 0#64) 64 = memLoad _ (sp - 0#64) 64 at atReturn
  rw [BitVec.sub_zero] at atReturn
  exact ⟨(keep 264 (by decide) (by decide)).trans slots.savedR15,
    (keep 272 (by decide) (by decide)).trans slots.savedR14,
    (keep 280 (by decide) (by decide)).trans slots.savedR12,
    (keep 256 (by decide) (by decide)).trans slots.parserRet,
    (keep 16 (by decide) (by decide)).trans slots.wrapperRbx,
    (keep 8 (by decide) (by decide)).trans slots.wrapperR14, atReturn.trans slots.wrapperRet,
    slots.writes.trans changed allWithin⟩

theorem parserCall_afterDecode {s : RamState} {bytes : ByteArray} {args : Values Value Reg.count} {mem : Ram}
    (call : ValidCall publicKeyFromSec1Bytes s [bytes]) (slots : SavedSlots s mem)
    (reached : Reaches Extracted.programImage .l106390 (Wrapper.parserArgs s) (Wrapper.parserMemory s)
      .l1064f4 args mem)
    (rsp : args[4].get 64 = s.regValue .rsp - 600)
    (rbx : args[3].get 64 = s.regValue .rsp - 600 + 160)
    (r12 : args[12].get 64 = 0)
    (r15 : args[15].get 64 = s.regValue .rsp - 112)
    (kept : ∀ i : Fin Reg.count, i.val ∈ [5, 13, 22] → args[i] = (Reg.ofIndex i).read s)
    {tag : UInt8} (tagByte : memLoad mem (s.regValue .rsp - 600 + 4) 8 = tag.toBitVec)
    (inputTag : bytes.data[0]? = some tag) (valid : validTag tag.toBitVec)
    (affine :
      if tag = 0 then memLoad mem (s.regValue .rsp - 600 + 248) 8 = 1
      else
        match Secp256k1.decodePublicKey bytes with
        | none => memLoad mem (s.regValue .rsp - 600 + 248) 8 = 0
        | some point => memLoad mem (s.regValue .rsp - 600 + 248) 8 = 1 ∧
          PublicKeyAt mem (s.regValue .rsp - 600 + 160) point) :
    Wrapper.ParserCall s bytes := by
  let sp := s.regValue .rsp
  let body := sp - 600
  let dst := sp - 112
  let byte := memLoad mem (body + 248) 8
  let flag := selectedByte tag.toBitVec byte 0
  let stored := resultStore mem body dst flag
  have df : args[22].get 1 = 0 :=
    congrArg (Value.get 1) ((kept 22 (by decide)).trans (Reg.read_df_iff.mpr call.directionFlagUnset))
  have stack : Writable Extracted.programImage mem body 249 :=
    (Wrapper.stackWritable (offset := 600) (len := 249) call (by decide) (by decide)
      (by decide)).of_frame slots.writes
  have output : Writable Extracted.programImage mem (dst + 8) 88 := by
    dsimp only [dst]
    rw [sub_add_eq_sub]
    exact (Wrapper.stackWritable (offset := 104) (len := 88) call (by decide) (by decide)
      (by decide)).of_frame slots.writes
  have separate : (body + 72).toNat + 88 ≤ (dst + 8).toNat := by
    have room : 1928 ≤ sp.toNat := call.stackAvailable.2.2.1
    have hs : (sp - 528).toNat = sp.toNat - 528 := by
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; change 528 ≤ sp.toNat; omega)]
      rfl
    have hd : (sp - 104).toNat = sp.toNat - 104 := by
      rw [BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; change 104 ≤ sp.toNat; omega)]
      rfl
    dsimp only [body, dst]
    rw [sub_add_eq_sub, sub_add_eq_sub]
    change (sp - 528).toNat + 88 ≤ (sp - 104).toNat
    rw [hs, hd]
    omega
  have identity : (args[12].get 64).setWidth 8 = 0 := by rw [r12]; rfl
  obtain ⟨next, step, outputReg, preserved, status⟩ :=
    afterAffine Common.fnCode_subset_programImage body dst tag.toBitVec byte 0 rsp rbx r15
      identity df valid tagByte rfl stack output (.inl separate)
  change Reaches _ .l1064f4 args mem (if flag = 0 then .l106560 else .l106565) next stored at step
  have resultSlots : SavedSlots s stored := savedSlots_afterResult call slots flag
  have resultFrame : ExitFrame s next stored :=
    { resultSlots with
      rsp := (congrArg (Value.get 64) (preserved.reg 4 (by decide))).trans rsp
      rdi := congrArg (Value.get 64) outputReg
      kept := fun i hi => (preserved.reg i (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
        omega)).trans (kept i hi) }
  have reject (decode : Secp256k1.decodePublicKey bytes = none) (zero : flag = 0) :
      Wrapper.ParserCall s bytes :=
    parserCall call resultFrame (.inl ⟨decode, reached.trans (by
      simpa only [ite_eq_left zero] using step)⟩)
  by_cases zero : tag = 0
  · subst tag
    exact reject (decodePublicKey_wrongTag inputTag (by decide) (by decide) (by decide) (by decide)) (by
      change selectedByte (0 : BitVec 8) byte 0 = 0
      simp only [selectedByte, ite_true])
  · have nonzero : tag.toBitVec ≠ 0 := by
      intro h
      apply zero
      exact UInt8.toBitVec_inj.mp h
    rw [ite_eq_right zero] at affine
    cases decode : Secp256k1.decodePublicKey bytes with
    | none =>
      have hbyte : byte = 0 := by simpa only [decode] using affine
      exact reject decode (by
        change selectedByte tag.toBitVec byte 0 = 0
        rw [hbyte, selectedByte, ite_eq_right nonzero]
        decide)
    | some point =>
      rw [decode] at affine
      obtain ⟨one, x, y, coords, key⟩ := affine
      have hbyte : byte = 1 := one
      have accepted : flag ≠ 0 := by
        change selectedByte tag.toBitVec byte 0 ≠ 0
        rw [hbyte, selectedByte, ite_eq_right nonzero]
        decide
      have copy : AffineAt stored (dst + 8) x y := resultStore_affine accepted key
      have dstKey : dst + 8 = sp - 104 := sub_add_eq_sub sp 112 8
      refine parserCall call resultFrame (.inr ⟨point, decode, reached.trans ?_,
        congrArg (Value.get 64) (status accepted), x, y, coords, ?_⟩)
      · simpa only [ite_eq_right accepted] using step
      · rwa [dstKey] at copy

end K256.Proofs.Sec1.Parser.Frame
