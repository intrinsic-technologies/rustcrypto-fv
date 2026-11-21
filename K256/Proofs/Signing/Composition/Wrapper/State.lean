import K256.Proofs.Signing.Composition.Memory

namespace K256.Proofs.Signing.Composition.Wrapper

open K256.Spec K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  CFG Lift Refine Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Verify.Core (Registers)
open Generate.Generator.Multiply (scalarWords)

abbrev localSp (s : RamState) := sp s + 816
abbrev atBlock (l : LIR.Label) (a : Registers) (m : Ram) : LIR.lifted.State :=
  ⟨⟨l,a,m⟩,[]⟩

structure Saved (s : RamState) (a : Registers) : Prop where
  rsp : a[4] = ⟨64,localSp s⟩
  output : a[3] = ⟨64,s.regValue .rdi⟩
  rbp : a[5] = ⟨64,s.regValue .rbp⟩
  r13 : a[13] = ⟨64,s.regValue .r13⟩
  message : a[15] = ⟨64,s.regValue .rdx⟩
  length : a[14] = ⟨64,s.regValue .rcx⟩
  r12 : a[12].width = 64
  df : a[22] = ⟨1,0⟩
  fp : a[39].width = 32 ∧ a[50].width = 16 ∧ a[51].width = 16

structure Decoded (s : RamState) (d : Nat) (a : Registers) (m : Ram) : Prop
    extends Saved s a, Memory s m where
  key : WordsAt m (localSp s+40) 64 (scalarWords d)

structure DecodeResult (s : RamState) (d : Nat) (a : Registers) (m : Ram) : Prop
    extends Decoded s d a m where
  volatileWidths : ∀ i : Fin Reg.count, i.val ∈ [2,8,9] → a[i].width = 64

structure Multiplied (s : RamState) (d : Nat) (a : Registers) (m : Ram) : Prop
    extends Decoded s d a m where
  pointPtr : a[12] = ⟨64,localSp s+200⟩
  point : Generate.Generator.Affine.ProjectiveAt m (localSp s+200) (Generate.Curve.generatorWindow d)

end K256.Proofs.Signing.Composition.Wrapper
