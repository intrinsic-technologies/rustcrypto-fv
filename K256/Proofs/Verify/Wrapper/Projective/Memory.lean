import K256.Proofs.Verify.Wrapper.OperandFrame
import K256.Proofs.Verify.Hash.Serialize
import K256.Proofs.Verify.Wrapper.Copy.Conversion

namespace K256.Proofs.Verify.Wrapper

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  CFG Lift Refine Verify.LIR Standards.SECG.ECC

theorem projectiveCallMemory {initial : RamState} {a : Core.Registers} {m : Ram}
    {key msg sig : ByteArray} {p : Curve.Point} {r s : Nat}
    (call : ValidCall verifyingKeyVerify initial [key,msg,sig])
    (hash : HashOutput initial a m p r s msg) :
    let sp := localSp initial
    let h := Hash.compressBlocks Hash.initialHash (Hash.bytePadding msg)
    let d := Hash.storeDigestWords m (sp + 128) h 8
    let pushed := Hash.coreMemory m sp h
    Memory initial pushed ∧ AffineInputs initial pushed p r s 352 ∧
      Ecdh.Decode.AffinePointAt pushed (sp + 160) p ∧
      Writable Extracted.programImage d (sp - 8) 512 := by
  let sp := localSp initial
  let h := Hash.compressBlocks Hash.initialHash (Hash.bytePadding msg)
  let d := Hash.storeDigestWords m (sp + 128) h 8
  let rs := Hash.Update.footprint initial
  have slot (off n : Nat) (hi : off ≤ 880) (fit : n + 184 ≤ off) :
      InRegions rs (stackPtr initial - BitVec.ofNat 64 off) n :=
    Hash.Update.frameSlot call rfl hi fit
  have fd : RamWriteFrame m d rs := by
    apply Hash.storeDigestWords_frame
    intro i hi
    apply Hash.Update.frameSlot call (off := 408 - 4*i) _ (by omega) (by omega)
    simp only [sp, localSp, wordAddr, Nat.reduceDiv,
      ← BitVec.ofNat_sub_ofNat_of_le 408 (4*i) (by omega : 4*i < 2^64) (by omega)]
    bv_omega
  have fc : RamWriteFrame m (Hash.coreMemory m sp h) rs := by
    apply conversionFrame fd
    · have addr : sp + 160 = stackPtr initial - 376 := by dsimp only [sp,localSp]; bv_omega
      rw [addr]
      exact slot 376 88 (by decide) (by decide)
    · have addr : sp - 8 = stackPtr initial - 544 := by dsimp only [sp,localSp]; bv_omega
      rw [addr]
      exact slot 544 8 (by decide) (by decide)
  obtain ⟨depth, _⟩ := Hash.Update.stackBounds call
  have base : sp.toNat = (stackPtr initial).toNat - 536 := Common.stackOffset call.stackAvailable (by decide)
  have below : ∀ reg ∈ rs, reg.start + reg.size ≤ sp.toNat + 352 := by
    intro reg hr
    obtain rfl := List.mem_singleton.mp hr
    change (stackPtr initial).toNat - 880 + 696 ≤ sp.toNat + 352
    omega
  exact ⟨Hash.Update.advance call hash.memory fc, hash.operands.afterHashWrites call fc below,
    conversionKey (hash.operands.afterHashWrites call fd below).point,
    Hash.Update.writable call (Hash.Update.advance call hash.memory fd) (off := 544)
      (by dsimp only [sp,localSp]; bv_omega) (by decide) (by decide) (by decide)⟩

end K256.Proofs.Verify.Wrapper
