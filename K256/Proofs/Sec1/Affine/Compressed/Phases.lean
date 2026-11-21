import K256.Proofs.Sec1.Affine.Compressed.Cube.Boundary
import K256.Proofs.Sec1.LIR.Fn1205b0.Frame
import K256.Proofs.Sec1.Parser.Affine

namespace K256.Proofs.Sec1.Affine.Compressed

open Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
open K256.Proofs.Refine K256.Proofs.Sec1.LIR K256.Proofs.Common.Field

def workSP (fr : Activation) : Word := fr.rsp - 488

def chosenY (root : Fin modulus) (want : BitVec 8) : Fin modulus :=
  if root.val % 2 = want.toNat then root else ⟨(modulus-root.val) % modulus, Nat.mod_lt _ (by decide)⟩

structure Environment (fr : Activation) : Prop where
  text : fr.rsp.toNat + 8 ≤ 0x100000 ∨ 0x12aa00 ≤ fr.low.toNat
  apart : fr.rdi.toNat + 89 ≤ fr.low.toNat ∨ fr.rsp.toNat + 8 ≤ fr.rdi.toNat

structure BodyAt (code : CodeMap) (fr : Activation) (args : Values Value Reg.count)
    (mem : Ram) (xs : Limbs) (ok : Bool) (want : BitVec 8) : Prop where
  atoms : Atom.All code args mem (Fn1205b0.frameAt .l120d03 fr)
  output : Writable code mem fr.rdi 89
  x : savedX mem (workSP fr) = xs
  valid : memLoad mem (workSP fr + 128) 64 = BitVec.ofNat 64 ok.toNat
  parity : memLoad mem (workSP fr + 108) 8 = want

structure RootAt (mem : Ram) (sp : Word) (root : Fin modulus) (ok : Bool) : Prop where
  flag : memLoad mem (sp+344) 8 = BitVec.ofNat 8 ok.toNat
  repr : ok = true → ∃ ys : Limbs, WordsAt mem (sp+304) 64 ys ∧ FieldRepr ys root 8

structure SelectedAt (mem : Ram) (sp : Word) (y : Fin modulus) (ok : Bool) : Prop where
  flag : memLoad mem (sp+32) 8 = BitVec.ofNat 8 ok.toNat
  repr : ok = true → ∃ ys : Limbs, WordsAt mem (sp+392) 64 ys ∧ FieldRepr ys y 8

def SelectCall (code : CodeMap) : Prop :=
  ∀ (fr : Activation) (args : Values Value Reg.count) (mem : Ram) (xs : Limbs)
    (xOK sqrtOK : Bool) (want : BitVec 8) (root : Fin modulus),
    Environment fr → BodyAt code fr args mem xs xOK want →
    (∀ i : Fin 53, i.val ∈ [3,5,12,13,14,15] → args[i] = ⟨64,args[i].get 64⟩) →
    RootAt mem (workSP fr) root sqrtOK →
    (want = 0 ∨ want = 1) → (sqrtOK = true → 0 < root.val) →
    ∃ (next : Values Value Reg.count) (m : Ram),
      (program.sem (dialect code)).Reaches ⟨⟨.l120d03,args,mem⟩,[]⟩ ⟨⟨.l120e9b,next,m⟩,[]⟩ ∧
      BodyAt code fr next m xs xOK want ∧ SelectedAt m (workSP fr) (chosenY root want) sqrtOK ∧
      RamWriteFrame mem m [fr.region]

def EmitCall (code : CodeMap) : Prop :=
  ∀ (fr : Activation) (args : Values Value Reg.count) (mem : Ram) (xs : Limbs)
    (xOK sqrtOK : Bool) (want : BitVec 8) (x y : Fin modulus),
    Environment fr → BodyAt code fr args mem xs xOK want → SelectedAt mem (workSP fr) y sqrtOK →
    (xOK = true → FieldRepr xs x 8) →
    ∃ out, program.Exec (dialect code) ⟨⟨.l120e9b,args,mem⟩,[]⟩ out ∧
      out.tag = some ⟨64,fr.ret⟩ ∧ Atom.All code out.values out.store (Fn1205b0.doneAt fr) ∧
      out.values[0] = ⟨64,fr.rdi⟩ ∧ RamWriteFrame mem out.store [fr.region, ⟨fr.rdi.toNat,89⟩] ∧
      memLoad out.store (fr.rdi + 88) 8 = BitVec.ofNat 8 (xOK && sqrtOK).toNat ∧
      ((xOK && sqrtOK) = true → Parser.AffineAt out.store fr.rdi x y)

end K256.Proofs.Sec1.Affine.Compressed
