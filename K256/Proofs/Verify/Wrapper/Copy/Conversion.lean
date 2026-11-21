import K256.Proofs.Ecdh.Decode.Repr
import K256.Proofs.Sec1.Parser.Result.Copy
import K256.Proofs.Common.SignatureRun
import K256.Proofs.Verify.LIR.Defs2
import K256.Proofs.Generate.Generator.Multiply.Prepare.Copy
import K256.Proofs.ParseSignature.Memory

namespace K256.Proofs.Verify.Wrapper

open K256.Spec.Program Verify.LIR Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.Lift K256.Proofs.Refine
  Standards.SECG.ECC

def conversionMemory (mem : Ram) (sp : BitVec 64) : Ram :=
  memStore (memCopy mem (sp + 160) (sp + 416) 88) (sp - 8) (0x1033a2 : BitVec 64)

theorem conversionKey {mem : Ram} {sp : BitVec 64} {point : Curve.Point}
    (key : Ecdh.Decode.AffinePointAt mem (sp + 416) point) :
    Ecdh.Decode.AffinePointAt (conversionMemory mem sp) (sp + 160) point := by
  apply key.of_copy
  intro off width within
  have apart : RangeApart (sp - 8) 8 (sp + 160) 88 :=
    RangeApart.of_offsets (addr_sub sp 8) rfl (by decide)
  rw [conversionMemory, memLoad_memStore_of_rangeApart _ _ _ _ _ (RangeApart.right_sub apart within)]
  exact Sec1.Parser.Result.memLoad_memCopy _ _ _ (by decide) within

theorem conversionFrame {initial mem : Ram} {sp : BitVec 64} {regions : List MemoryRegion}
    (frame : RamWriteFrame initial mem regions)
    (destination : InRegions regions (sp + 160) 88) (slot : InRegions regions (sp - 8) 8) :
    RamWriteFrame initial (conversionMemory mem sp) regions :=
  (frame.memStore _ destination).memStore _ slot

theorem conversionGuards {mem : Ram} {sp : BitVec 64}
    (win : Writable Extracted.programImage mem (sp - 8) 512) :
    RepMovsOk Extracted.programImage mem 0 (sp + 416) (sp + 160) 11 8 0x10338f 3 ∧
      StoreOk Extracted.programImage (memCopy mem (sp + 160) (sp + 416) 88)
        (sp - 8) 8 0x10339d 5 := by
  have included := fun x hx => Common.fnCode_subset_programImage x (code_l103306_1 x hx)
  have src : Readable mem (sp + 416) 88 :=
    win.readable.of_offsets rfl (addr_sub sp 8) (by decide)
  have dst : Writable Extracted.programImage mem (sp + 160) 88 := win.of_offsets rfl (addr_sub sp 8) (by decide)
  have left : (sp + 160).toNat = (sp - 8).toNat + 168 :=
    toNat_of_offsets (n := 88) rfl (addr_sub sp 8) win.readable.low (by decide)
  have right : (sp + 416).toNat = (sp - 8).toNat + 424 :=
    toNat_of_offsets (n := 88) rfl (addr_sub sp 8) win.readable.low (by decide)
  have slot : Writable Extracted.programImage (memCopy mem (sp + 160) (sp + 416) 88) (sp - 8) 8 :=
    (win.memStore _ _).sub (Nat.le_refl _) (by omega)
  refine ⟨Generate.Generator.Multiply.Prepare.copyGuard src ?_ (Or.inr (by
    change (sp + 160).toNat + 88 ≤ (sp + 416).toNat
    omega)), ?_⟩
  · exact ParseSignature.storeOk_of_codeRange (off := 55) dst included (by decide)
  · exact ParseSignature.storeOk_of_codeRange (off := 69) slot included (by decide)

end K256.Proofs.Verify.Wrapper
