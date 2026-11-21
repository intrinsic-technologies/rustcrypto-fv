import K256.Proofs.Generate.Generator.Multiply.Lookup.Execution
import K256.Proofs.Generate.Generator.Multiply.Constants

namespace K256.Proofs.Generate.Generator.Multiply

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Generate.LIR

theorem CoreEntry.generator_stored {fr : Activation} {a : Registers} {d : Nat}
    (h : CoreEntry fr a d) : Multiply.generator.Stored fr.original fr.rsi :=
  (Multiply.generator_stored h.loaded).of_word_copy h.generator

theorem TableAt.memCopy {m : Ram} {src dst : Word} {p : Standards.SECG.ECC.Curve.Point}
    (table : TableAt m src p) : TableAt (Lift.memCopy m dst src 960) dst p := by
  intro i
  obtain ⟨t, valid, stored, value⟩ := table i
  exact ⟨t, valid, stored.memCopy (by decide) (by have hi := i.isLt; omega), value⟩

theorem TableAt.of_frame {m n : Ram} {base : Word} {p : Standards.SECG.ECC.Curve.Point}
    {rs : List MemoryRegion} (table : TableAt m base p)
    (frame : RamWriteFrame m n rs) (out : Outside rs base 960) : TableAt n base p := by
  intro i
  obtain ⟨t, valid, stored, value⟩ := table i
  refine ⟨t, valid, stored.of_frame frame ?_, value⟩
  have hi := i.isLt
  have room := out.1
  have eq : (base + BitVec.ofNat 64 (120*i.val)).toNat = base.toNat + 120*i.val := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := 120*i.val) (by omega),
      Nat.mod_eq_of_lt (by omega)]
  exact Affine.outside_subregion out (by omega) (by omega)

end K256.Proofs.Generate.Generator.Multiply
