import K256.Proofs.Generate.Generator.Affine.Memory
import K256.Proofs.Generate.Generator.Affine.Invert.Core.Batch.Arithmetic
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Generate.Generator.Affine.Invert.Core.Batch

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Generate.LIR
open SafeGcd.Batch (Words)

def linearWrites (sp : Word) : List MemoryRegion :=
  [⟨(sp - 736).toNat, 440⟩, ⟨(base sp + 116).toNat, 4⟩, ⟨(base sp + 336).toNat, 24⟩]

def modularWrites (sp : Word) : List MemoryRegion :=
  [⟨(sp - 736).toNat, 488⟩, ⟨(base sp + 168).toNat, 40⟩, ⟨(base sp + 336).toNat, 24⟩]

structure LinearRows (b : Registers) (p : Ram) (sp : Word) (z : Fin modulus) (j : Nat)
    (s : Words) (c : Registers) (q : Ram) : Prop where
  rsp : c[4] = ⟨64, base sp⟩
  delta : c[5] = ⟨64, s.delta⟩
  second : c[12] = ⟨64, base sp + 56⟩
  shift : c[14] = ⟨64, BitVec.ofNat 64 (count j)⟩
  u : c[15] = ⟨64, s.u⟩
  v : c[3] = ⟨64, s.v⟩
  qWord : memLoad q (base sp + 8) 64 = s.q
  rWord : memLoad q (base sp + 104) 64 = s.r
  remaining : memLoad q (base sp + 352) 64 = BitVec.ofNat 64 (591 - roundsBefore j)
  firstResult : signedAt q (base sp + 16) (Core.model z (roundsBefore (j+1))).f
  secondResult : signedAt q (base sp + 56) (Core.model z (roundsBefore (j+1))).g
  controls : Controls b c
  frame : RamWriteFrame p q (linearWrites sp)

structure ModularRows (b : Registers) (p : Ram) (sp : Word) (z : Fin modulus) (j : Nat)
    (s : Words) (c : Registers) (q : Ram) (d' e' : Int) : Prop where
  rsp : c[4] = ⟨64, base sp - 16⟩
  delta : c[5] = ⟨64, s.delta⟩
  second : c[12] = ⟨64, base sp + 56⟩
  scratch : c[14] = ⟨64, base sp + 16⟩
  shift : c[15] = ⟨64, BitVec.ofNat 64 (count j)⟩
  remaining : memLoad q (base sp + 352) 64 = BitVec.ofNat 64 (591 - roundsBefore j)
  fValue : signedAt q (base sp + 120) (Core.model z (roundsBefore (j+1))).f
  gValue : signedAt q (base sp + 168) (Core.model z (roundsBefore (j+1))).g
  firstResult : signedAt q (base sp + 16) d'
  secondResult : signedAt q (base sp + 56) e'
  controls : Controls b c
  frame : RamWriteFrame p q (modularWrites sp)

theorem signedAt_of_frame {m q : Ram} {addr : Word} {x : Int} {rs : List MemoryRegion}
    (signed : signedAt m addr x) (fr : RamWriteFrame m q rs) (out : Outside rs addr 33) :
    signedAt q addr x := by
  obtain ⟨v, neg, words, sign, val⟩ := signed
  have low := out.1
  refine ⟨v, neg, words.of_frame fr (by decide) ?_, (fr.memLoad_eq ?_).trans sign, val⟩
  · exact outside_subregion out (Nat.le_refl _) (by omega)
  · apply outside_subregion out <;> bv_omega

theorem signedAt_of_copy {m q : Ram} {src dst : Word} {x : Int}
    (signed : signedAt m src x)
    (copy : ∀ i < 5, memLoad q (wordAddr dst 64 i) 64 = memLoad m (wordAddr src 64 i) 64) :
    signedAt q dst x := by
  obtain ⟨v, neg, words, sign, val⟩ := signed
  refine ⟨v, neg, fun i hi => (copy i (by omega)).trans (words i hi), ?_, val⟩
  have word := copy 4 (by decide)
  change memLoad q (dst + 32) 64 = memLoad m (src + 32) 64 at word
  have low (p : Ram) (a : Word) :
      (memLoad p a 64).extractLsb' 0 8 = memLoad p a 8 := by
    simpa only [Nat.zero_div, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      (extractLsb'_memLoad p a (n := 64) 0 8 (by decide) (by decide) (by decide))
  rw [← low, word, low, sign]

end K256.Proofs.Generate.Generator.Affine.Invert.Core.Batch
