import K256.Proofs.Ecdh.Scalar.Frame
import K256.Proofs.Ecdh.Multiply.State
import K256.Proofs.Ecdh.Decode.Repr
import K256.Proofs.Ecdh.LIR.Program
import K256.Proofs.Ecdh.Affine.State

namespace K256.Proofs.Ecdh.Wrapper

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine Ecdh.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1

abbrev Arguments := Values Value Reg.count

abbrev Reaches (l : Label) (a : Arguments) (m : Ram) (k : Label) (b : Arguments) (n : Ram) :=
  (program.sem (dialect Extracted.programImage)).Reaches ⟨⟨l, a, m⟩, []⟩ ⟨⟨k, b, n⟩, []⟩

structure Caller (s : RamState) (a : Arguments) (m : Ram) : Prop extends Scalar.Memory s m where
  rsp : a[4] = ⟨64, localSp s⟩
  output : a[3] = ⟨64, s.regValue .rdi⟩
  df : a[22] = ⟨1, 0⟩
  widths : ∀ i : Fin Reg.count, i.val ∈ [1,2,3,5,8,9,12,13,14,15] → a[i].width = 64
  mxcsr : a[39].width = 32
  ftw : a[50].width = 16
  fcw : a[51].width = 16

abbrev ScalarAt (s : RamState) (m : Ram) (off : Nat) (d : Nat) :=
  WordsAt m (localSp s + BitVec.ofNat 64 off) 64 (Generate.Generator.Multiply.scalarWords d)

end K256.Proofs.Ecdh.Wrapper
