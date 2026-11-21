import K256.Proofs.Generate.Generator.Multiply.Split.WideProduct
import K256.Proofs.Generate.Generator.Multiply.Prepare.Frame
import K256.Proofs.Generate.Generator.Multiply.Split.Caller.Arguments
import K256.Proofs.Generate.Generator.Multiply.Prepare.HighBit

namespace K256.Proofs.Generate.Generator.Multiply.Prepare.Bases

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR
  Standards.SECG.DomainParameters.Secp256k1

def localValues (fr : Activation) : List (BitVec 64 × BitVec 64) :=
  [(0x8,0),(0x38,fr.rsi),(0x60,66),(0x68,152),(0x88,152),(0xb0,fr.rsi),
   (0xc0,0),(0xd8,fr.rcx),(0xf0,fr.r9),(0x100,1),(0x1a0,1),(0x1c0,fr.rcx),
   (0x248,fr.rdi),(0xcc0,1)]

structure Context (fr : Activation) (a : Registers) (m : Ram) : Prop where
  atoms : Atom.All Extracted.programImage a m (Fn11c880.frameAt .l11c9e7 fr)
  widths : ParseSignature.ArgumentWidths a
  savedWidths : SavedWidths a
  frame : RamWriteFrame fr.original m [fr.region]
  locals : Locals fr m (localValues fr)

abbrev endoAt (fr : Activation) (m : Ram) :=
  ∃ p : Projective, p.valid ∧ p.Stored m (sp fr + 0x2b0) ∧ p.value = Curve.endomorphism domain.G

abbrev u (d : Nat) := scalarWords (Curve.splitFirst d)
abbrev v (d : Nat) := scalarWords (Curve.splitSecond d)
abbrev flag (r : Int) : BitVec 8 := if r < 0 then 1 else 0
abbrev negative (x : Nat) := scalarWords (if x = 0 then 0 else domain.n - x)

structure ComparedInput (fr : Activation) (a : Registers) (m : Ram) (d : Nat) : Prop extends Context fr a m where
  endo : endoAt fr m
  r5 : a[5] = ⟨64,(u d)[0]⟩
  r3 : a[3] = ⟨64,(u d)[1]⟩
  r13 : a[13] = ⟨64,(u d)[2]⟩
  r12 : a[12] = ⟨64,(u d)[3]⟩
  r14 : a[14] = ⟨64,(v d)[0]⟩
  r15 : a[15] = ⟨64,sp fr + 0x1d0⟩
  slots : Locals fr m [(0x40,(v d)[1]),(0x10,(v d)[2]),(0x28,(v d)[3])]

structure Compared (fr : Activation) (a : Registers) (m : Ram) (d : Nat) : Prop extends Context fr a m where
  endo : endoAt fr m
  firstSign : memLoad m (sp fr + 0x30) 8 = flag (firstComponent d)
  secondSign : a[0].get 8 = flag (secondComponent d)
  r5 : a[5] = ⟨64,(v d)[3]⟩
  r12 : a[12] = ⟨64,(u d)[3]⟩
  r15 : a[15] = ⟨64,sp fr + 0x1d0⟩
  slots : Locals fr m [(0x58,(u d)[0]),(0x70,(u d)[1]),(0x50,(u d)[2]),(0xa8,(v d)[0]),
    (0x40,(v d)[1]),(0x10,(v d)[2]),(0x28,(v d)[3])]

structure Negated (fr : Activation) (a : Registers) (m : Ram) (d : Nat) : Prop extends Context fr a m where
  endo : endoAt fr m
  firstSign : memLoad m (sp fr + 0x30) 8 = flag (firstComponent d)
  secondSign : memLoad m (sp fr + 0x48) 8 = flag (secondComponent d)
  firstMagnitude : WordsAt m (sp fr + 0x270) 64 (scalarWords (firstComponent d).natAbs)
  negSecond : WordsAt m (sp fr + 0x128) 64 (negative (Curve.splitSecond d))
  r12 : a[12] = ⟨64,(v d)[0]⟩
  r13 : a[13] = ⟨64,(v d)[1]⟩
  r14 : a[14] = ⟨64,(v d)[2]⟩
  r5 : a[5] = ⟨64,(v d)[3]⟩
  r3 : a[3] = ⟨64,0x3ffffffffffffc⟩
  r15 : a[15] = ⟨64,sp fr + 0x1d0⟩

theorem highBit_scalar {x : Nat} (hx : x < domain.n) :
    let w := scalarWords x
    highBit w[0] w[1] w[2] w[3] = (flag (Curve.centered x)).setWidth 64 := by
  dsimp only
  rw [highBit_correct]
  have hn : domain.n < 2^256 := by decide +kernel
  have h := Split.scalarWords_value x (Nat.lt_trans hx hn)
  change (if domain.n / 2 < Split.scalarValue (scalarWords x) then _ else _) = _
  rw [h]
  by_cases high : domain.n / 2 < x <;> simp only [Curve.centered, flag, high, ite_true, ite_false]
  · rw [ite_eq_left (by omega)]; rfl
  · rw [ite_eq_right (by omega)]; rfl

theorem selectMagnitude {x : Nat} (hx : x < domain.n) :
    (if flag (Curve.centered x) = 0 then scalarWords x else negative x) =
      scalarWords (Curve.centered x).natAbs := by
  by_cases high : domain.n / 2 < x
  · simp only [Curve.centered, high, ite_true, flag, ite_eq_left (show (x : Int) - domain.n < 0 by omega),
      negative, ite_eq_right (show x ≠ 0 by omega)]
    change scalarWords (domain.n - x) = scalarWords ((x : Int) - domain.n).natAbs
    congr 1; omega
  · simp only [Curve.centered, high, ite_false, flag, ite_eq_right (show ¬ (x : Int) < 0 by omega), ite_true,
      Int.natAbs_natCast]

end K256.Proofs.Generate.Generator.Multiply.Prepare.Bases
