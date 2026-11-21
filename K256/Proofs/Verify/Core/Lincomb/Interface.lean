import K256.Proofs.Verify.Core.Lincomb.Call
import K256.Proofs.Verify.Combination
import K256.Proofs.Verify.Naf.Table

namespace K256.Proofs.Verify.Core.Lincomb

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Generate.Generator.Multiply (Projective)
open Generate.Curve

def scratch (sp : BitVec 64) (depth : Nat) : MemoryRegion := ⟨sp.toNat - depth, depth⟩

structure RoutineEntry (a : Registers) (m : Ram) (sp : BitVec 64) (depth : Nat) : Prop where
  rsp : a[4] = ⟨64, sp⟩
  saved : ∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15] → a[i].width = 64
  df : a[22] = ⟨1, 0⟩
  mxcsr : a[39].width = 32
  ftw : a[50].width = 16
  fcw : a[51].width = 16
  aligned : sp.toNat % 16 = 8
  room : depth ≤ sp.toNat
  stack : Writable Extracted.programImage m (sp - BitVec.ofNat 64 depth) depth
  returnSlot : Readable m sp 8
  returnLow : (memLoad m sp 64).toNat < 2^32
  image : ∀ v ∈ Extracted.programImage, m[v.1]? = some v.2

structure RoutineReturn (a : Registers) (m : Ram) (sp : BitVec 64) (depth : Nat)
    (buffers : List MemoryRegion) (out : Output Value Ram Reg.count) : Prop where
  tag : out.tag = some ⟨64, memLoad m sp 64⟩
  rsp : out.values[4] = ⟨64, sp + 8⟩
  saved : ∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15,22,39,50,51] → out.values[i] = a[i]
  frame : RamWriteFrame m out.store (scratch sp depth :: buffers)

def DigitBytes (m : Ram) (dst : BitVec 64) (digits : List Int) : Prop :=
  ∀ i : Fin 257, memLoad m (dst + BitVec.ofNat 64 i.val) 8 =
    BitVec.ofInt 8 (digits[i.val]?.getD 0)

def Prepared (m : Ram) (tables digits : BitVec 64) (p : Curve.Point) (scalar : Nat) : Prop :=
  ∀ j : Fin 2,
    let second := j.val = 1
    let component := centered (if second then splitSecond scalar else splitFirst scalar)
    let base := signedBase component (if second then endomorphism p else p)
    let ds := Naf.digits component.natAbs
    let header := digits + BitVec.ofNat 64 (0x110 * j.val)
    memLoad m header 64 = BitVec.ofNat 64 ds.length ∧ DigitBytes m (header + 8) ds ∧
      ∀ k : Fin 8, ∃ q : Projective, q.valid ∧ q.value = Naf.oddTableEntry base k.val ∧
        q.Stored m (tables + BitVec.ofNat 64 (120 * (8 * j.val + k.val)))

end K256.Proofs.Verify.Core.Lincomb
