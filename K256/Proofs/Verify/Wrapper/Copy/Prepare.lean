import K256.Proofs.Verify.Wrapper.Copy.Blocks
import K256.Proofs.Verify.Wrapper.Frame
import K256.Proofs.Generate.Generator.Multiply.Prepare.Copy

namespace K256.Proofs.Verify.Wrapper

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine Verify.LIR Standards.SECG.ECC

theorem prepareSignature {s : RamState} {key msg sig : ByteArray} {args : Values Value Reg.count}
    {mem : Ram} {point : Curve.Point} (call : ValidCall verifyingKeyVerify s [key, msg, sig])
    (state : Memory s mem) (rsp : args[4].get 64 = localSp s) (df : args[22].get 1 = 0)
    (parsed : Ecdh.Decode.AffinePointAt mem (localSp s + 16) point) :
    let sp := localSp s
    let pushed := memStore (copiedKey mem sp) (sp - 8) (0x10302c : BitVec 64)
    program.runBlock (dialect Extracted.programImage) ⟨.l102ff4, args, mem⟩ =
      .call ⟨.l103ac0, signatureCallArgs args sp, pushed⟩
        ⟨.l10302c, #v[], rfl, some ⟨64, 0x10302c⟩⟩ ∧
      Memory s pushed ∧ Ecdh.Decode.AffinePointAt pushed (sp + 416) point ∧
      memLoad pushed (sp - 8) 64 = 0x10302c := by
  let sp := localSp s
  let slot := sp - 8
  have slotEq : slot = stackPtr s - 544 := by dsimp only [slot, sp, localSp]; bv_omega
  have top : (stackPtr s - 544).toNat = (stackPtr s).toNat - 544 := Common.stackOffset call.stackAvailable (off := 544) (by decide)
  have window : Writable Extracted.programImage mem slot 512 := by
    rw [slotEq]
    exact (Common.stackWritable call (by decide) (by decide) (by decide)).of_frame state.frame
  have bounds (off n : Nat) (h : off + n + 8 ≤ 512) :
      (sp + BitVec.ofNat 64 off).toNat = slot.toNat + (off + 8) := by
    have a : sp + BitVec.ofNat 64 off = slot + BitVec.ofNat 64 (off + 8) := by
      simp only [slot, BitVec.ofNat_add]
      bv_omega
    rw [a, BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := off+8) (by omega),
      Nat.mod_eq_of_lt (by have := window.readable.low; omega)]
  have b16 : (sp + 16).toNat = slot.toNat + 24 := bounds 16 88 (by decide)
  have b256 : (sp + 256).toNat = slot.toNat + 264 := bounds 256 88 (by decide)
  have b416 : (sp + 416).toNat = slot.toNat + 424 := bounds 416 88 (by decide)
  let regs : List MemoryRegion := [⟨slot.toNat, 512⟩]
  have low := window.readable.low
  have within (addr : BitVec 64) (n : Nat) (lo : slot.toNat ≤ addr.toNat)
      (hi : addr.toNat + n ≤ slot.toNat + 512) : InRegions regs addr n :=
    ⟨_, List.mem_singleton_self _, lo, hi, by omega⟩
  have writes := signatureCallFrame (RamWriteFrame.refl mem regs)
    (within (sp + 256) 88 (by omega) (by omega)) (within (sp + 416) 88 (by omega) (by omega))
    (within slot 8 (by omega) (by omega))
  refine ⟨?_, state.advance call writes ?_, signatureCallKey parsed,
    memLoad_memStore_same _ _ _ (by decide) (by decide)⟩
  · have code := fun x hx => Common.fnCode_subset_programImage x (code_l102ff4 x hx)
    have first : Writable Extracted.programImage (memCopy mem (sp + 256) (sp + 16) 88) slot 512 :=
      window.memStore _ _
    have read1 : Readable mem (sp + 16) 88 := window.readable.sub (by omega) (by omega)
    have write1 : Writable Extracted.programImage mem (sp + 256) 88 := window.sub (by omega) (by omega)
    have read2 : Readable (memCopy mem (sp + 256) (sp + 16) 88) (sp + 256) 88 :=
      first.readable.sub (by omega) (by omega)
    have write2 : Writable Extracted.programImage (memCopy mem (sp + 256) (sp + 16) 88) (sp + 416) 88 :=
      first.sub (by omega) (by omega)
    apply signatureCall (sp := sp) rsp
    · rw [df]
      exact Generate.Generator.Multiply.Prepare.copyGuard read1
        (ParseSignature.storeOk_of_codeRange (off := 21) write1 code (by decide))
        (Or.inl (by change (sp + 16).toNat + 88 ≤ (sp + 256).toNat; omega))
    · rw [df]
      exact Generate.Generator.Multiply.Prepare.copyGuard read2
        (ParseSignature.storeOk_of_codeRange (off := 40) write2 code (by decide))
        (Or.inl (by change (sp + 256).toNat + 88 ≤ (sp + 416).toNat; omega))
    · exact ParseSignature.storeOk_of_codeRange (off := 51)
        ((first.memStore _ _).sub (Nat.le_refl _) (by omega)) code (by decide)
  · intro r hr
    obtain rfl := List.mem_singleton.mp hr
    rw [← slotEq] at top
    change (stackPtr s).toNat - 13000 ≤ slot.toNat ∧ slot.toNat + 512 ≤ (stackPtr s).toNat - 32
    have room : 13000 ≤ (stackPtr s).toNat := call.stackAvailable.2.2.1
    omega

theorem prepareVerification {s : RamState} {key msg sig : ByteArray} {args : Values Value Reg.count}
    {mem : Ram} (call : ValidCall verifyingKeyVerify s [key, msg, sig])
    (state : Memory s mem) (rsp : args[4].get 64 = localSp s) :
    let sp := localSp s
    let pushed := memStore mem (sp - 8) (0x1033c7 : BitVec 64)
    program.runBlock (dialect Extracted.programImage) ⟨.l1033a2, args, mem⟩ =
      .call ⟨.l104f20, verificationCallArgs args sp, pushed⟩
        ⟨.l1033c7, #v[], rfl, some ⟨64, 0x1033c7⟩⟩ ∧
      Memory s pushed ∧ memLoad pushed (sp - 8) 64 = 0x1033c7 := by
  let slot := localSp s - 8
  have slotEq : slot = stackPtr s - 544 := by dsimp only [slot, localSp]; bv_omega
  have write : Writable Extracted.programImage mem slot 8 := by
    rw [slotEq]
    exact (Common.stackWritable call (by decide) (by decide) (by decide)).of_frame state.frame
  have pushed := (RamWriteFrame.refl mem [⟨slot.toNat,8⟩]).memStore (a := slot) (0x1033c7 : BitVec 64)
    (show InRegions _ slot 8 from ⟨_, List.mem_singleton_self _, Nat.le_refl _, Nat.le_refl _,
      by have := write.readable.low; omega⟩)
  refine ⟨verificationCall rsp (ParseSignature.storeOk_of_codeRange (off := 32) write
    (fun x hx => Common.fnCode_subset_programImage x (code_l1033a2 x hx)) (by decide)),
    state.advance call pushed ?_, memLoad_memStore_same _ _ _ (by decide) (by decide)⟩
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  have top : slot.toNat = (stackPtr s).toNat - 544 := by
    rw [slotEq]
    exact Common.stackOffset call.stackAvailable (by decide)
  have room : 13000 ≤ (stackPtr s).toNat := call.stackAvailable.2.2.1
  change (stackPtr s).toNat - 13000 ≤ slot.toNat ∧ slot.toNat + 8 ≤ (stackPtr s).toNat - 32
  omega

end K256.Proofs.Verify.Wrapper
