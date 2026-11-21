import K256.Proofs.Verify.LIR.Fn104f20.Frame
import K256.Proofs.Verify.Model
import K256.Proofs.Generate.Generator.Multiply.State
import K256.Proofs.Generate.Generator.Multiply.Coordinates

namespace K256.Proofs.Verify.Core

open K256.Spec K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Multiply (scalarWords Projective)
open Generate.Generator.Affine (ProjectiveAt)

abbrev Registers := Values Value Reg.count
abbrev localSp (fr : Activation) := fr.rsp - 488

noncomputable abbrev Reaches (l : Label) (a : Registers) (m : Ram)
    (l' : Label) (a' : Registers) (m' : Ram) :=
  (program.sem (dialect Extracted.programImage)).Reaches ⟨⟨l, a, m⟩, []⟩ ⟨⟨l', a', m'⟩, []⟩

structure Entry (fr : Activation) (a : Registers) (p : Curve.Point) (digest : ByteArray)
    (r s : Nat) : Prop where
  atoms : Atom.All Extracted.programImage a fr.original (Fn104f20.frameAt .l104f20 fr)
  image : ∀ b ∈ Extracted.programImage, fr.original[b.1]? = some b.2
  dst : fr.rdi = fr.rsp + 168
  key : fr.rsi = fr.rsp + 16
  hash : fr.rdx = fr.rsp + 136
  size : fr.rcx = 32
  sig : fr.r8 = fr.rsp + 360
  stackRoom : 12456 ≤ fr.rsp.toNat
  stackBase : fr.low = fr.rsp - 12456
  stack : Writable Extracted.programImage fr.original fr.low 12456
  upper : Writable Extracted.programImage fr.original (fr.rsp + 8) 504
  low : fr.rsp.toNat + 512 ≤ 2^32
  peer : ∃ q : Projective, q.Stored fr.original fr.rsi ∧ q.valid ∧ q.value = p
  onCurve : Curve.onCurve domain p
  digestAt : (⟨fr.rdx.toNat, 32⟩ : MemoryRegion).HasBytes fr.original digest
  rAt : WordsAt fr.original fr.r8 64 (scalarWords r)
  sAt : WordsAt fr.original (fr.r8 + 32) 64 (scalarWords s)
  bounds : 0 < r ∧ r < domain.n ∧ 0 < s ∧ s < domain.n

structure Saved (fr : Activation) (a : Registers) (m : Ram) : Prop where
  sp : a[4] = ⟨64, localSp fr⟩
  dst : a[3] = ⟨64, fr.rdi⟩
  rbp : a[5] = ⟨64, fr.rbp⟩
  df : a[22] = ⟨1, 0⟩
  mxcsr : a[39] = ⟨32, fr.mxcsr⟩
  ftw : a[50] = ⟨16, fr.ftw⟩
  fcw : a[51] = ⟨16, fr.fcw⟩
  rbx : memLoad m (fr.rsp - 40) 64 = fr.rbx
  r12 : memLoad m (fr.rsp - 32) 64 = fr.r12
  r13 : memLoad m (fr.rsp - 24) 64 = fr.r13
  r14 : memLoad m (fr.rsp - 16) 64 = fr.r14
  r15 : memLoad m (fr.rsp - 8) 64 = fr.r15

structure Phase (fr : Activation) (a : Registers) (m : Ram) : Prop extends Saved fr a m where
  frame : RamWriteFrame fr.original m [fr.region]

structure Parsed (fr : Activation) (a : Registers) (m : Ram) (r s : Nat) : Prop
    extends Phase fr a m where
  r9Width : a[9].width = 64
  atoms : Atom.All Extracted.programImage a m (Fn104f20.frameAt .l1050c1 fr)
  rAt : WordsAt m (localSp fr + 256) 64 (scalarWords r)
  sAt : WordsAt m (localSp fr + 224) 64 (scalarWords s)

structure Products (fr : Activation) (a : Registers) (m : Ram) (u v r : Nat) : Prop
    extends Phase fr a m where
  key : a[14] = ⟨64, fr.rsi⟩
  uPtr : a[12] = ⟨64, localSp fr + 384⟩
  vPtr : a[15] = ⟨64, localSp fr + 416⟩
  uAt : WordsAt m (localSp fr + 384) 64 (scalarWords u)
  vAt : WordsAt m (localSp fr + 416) 64 (scalarWords v)
  rAt : WordsAt m (localSp fr + 256) 64 (scalarWords r)

structure PointResult (fr : Activation) (a : Registers) (m : Ram) (point : Curve.Point)
    (r : Nat) : Prop extends Phase fr a m where
  width12 : a[12].width = 64
  width15 : a[15].width = 64
  ptr : a[13] = ⟨64, localSp fr + 8⟩
  pointAt : ProjectiveAt m (localSp fr + 8) point
  rAt : WordsAt m (localSp fr + 256) 64 (scalarWords r)

def digestScalar (digest : ByteArray) (s : Nat) : Nat :=
  Nat.mod (Nat.mod (Encoding.octetsToNat digest) domain.n * Curve.inverse domain.n s) domain.n

def signatureScalar (r s : Nat) : Nat :=
  Nat.mod (r * Curve.inverse domain.n s) domain.n

end K256.Proofs.Verify.Core
