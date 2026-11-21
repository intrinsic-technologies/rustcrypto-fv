import K256.Proofs.Generate.Generator.Affine.Invert.Core.Callee
import K256.Proofs.Verify.Core.Scalars.Inverse.Correction.Model
import K256.Proofs.Verify.Core.Scalars.Inverse.ModularShift.LinearCombination
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Verify.Core.Scalars.Inverse.ModularShift

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Verify.LIR
open Correction

structure TailFrame (entry : Registers) (original : Ram) (sp dst ret : Word) (a : Registers) (m : Ram) : Prop where
  rsp : a[4] = ⟨64, sp - 168⟩
  controls : ∀ i : Fin Reg.count, i.val ∈ [22, 39, 50, 51] → a[i] = entry[i]
  saved : Atom.All Extracted.programImage a m
    [.mem (sp - 8) 64 (entry[5].get 64), .mem (sp - 16) 64 (entry[15].get 64),
     .mem (sp - 24) 64 (entry[14].get 64), .mem (sp - 32) 64 (entry[13].get 64),
     .mem (sp - 40) 64 (entry[12].get 64), .mem (sp - 48) 64 (entry[3].get 64)]
  frame : RamWriteFrame original m [⟨(sp - 304).toNat, 304⟩]
  returned : memLoad m sp 64 = ret
  modPtr : memLoad m (sp + 8) 64 = 0x2021a0
  inverse : memLoad m (sp + 16) 64 = 0xb4f20099aa774ec1
  image : ∀ b ∈ Extracted.programImage, m[b.1]? = some b.2

def afterLinear (sp dst : Word) (p : Inputs) : List Atom :=
  [.gpr 5 (p.shift.setWidth 64),
       .gpr 3 (dst),
       .mem (sp - 0x98) 64 (p.magnitude[0]),
       .mem (sp - 0x90) 64 (p.magnitude[1]),
       .mem (sp - 0x88) 64 (p.magnitude[2]),
       .mem (sp - 0x80) 64 (p.magnitude[3]),
       .mem (sp - 0x78) 64 (p.magnitude[4]),
       .mem (sp - 0x70) 8 p.sign]

def beforeSelect (sp dst : Word) (p : Inputs) : List Atom :=
  [.gpr 5 ((v108b4c p).1),
       .gpr 3 (v108b3b p),
       .gpr 12 ((v108a7e p).1),
       .gpr 13 ((v108ade p).1),
       .gpr 14 ((((if !(decide ((v108b25 p : BitVec 64) = 0)) then 1 else 0 : BitVec 8)).setWidth 32 : BitVec 32).setWidth 64),
       .gpr 15 ((((if !(decide ((v108b25 p : BitVec 64) = 0)) then 1 else 0 : BitVec 8)).setWidth 32 : BitVec 32).setWidth 64),
       .gpr 1 ((v1089a7 p : BitVec 32).setWidth 64),
       .gpr 7 ((((if !(decide ((v108b25 p : BitVec 64) = 0)) then 1 else 0 : BitVec 8)).setWidth 32 : BitVec 32).setWidth 64),
       .gpr 6 ((((if !((v108b4f p).2.CF) then 1 else 0 : BitVec 8)).setWidth 32 : BitVec 32).setWidth 64),
       .low 9 8 ((mergeGPR 8 ((if !(decide ((v108b25 p : BitVec 64) = 0)) then 1 else 0 : BitVec 8)) ((0 : BitVec 64))).setWidth 8),
       .gpr 8 ((v108b44 p).1),
       .gpr 0 ((v108b1c p).1),
       .gpr 10 ((v108b4f p).1),
       .gpr 2 ((((if !(decide ((v108b25 p : BitVec 64) = 0)) then 1 else 0 : BitVec 8)).setWidth 32 : BitVec 32).setWidth 64),
       .gpr 11 ((v108aae p).1),
       .mem (sp - 0x90) 64 (p.magnitude[1]),
       .mem (sp - 0x88) 64 (p.magnitude[2]),
       .mem (sp - 0x80) 64 (p.magnitude[3]),
       .mem (sp - 0x78) 64 (p.magnitude[4]),
       .mem (sp - 0x70) 8 p.sign,
       .mem (sp - 0x64) 32 ((p.shift.setWidth 64).setWidth 32),
       .mem (sp - 0x38) 64 (dst),
       .mem (sp - 0x58) 64 (p.params.modulusWords[0]),
       .mem (sp - 0x50) 64 (p.params.modulusWords[1]),
       .mem (sp - 0x48) 64 (p.params.modulusWords[2]),
       .mem (sp - 0x40) 64 (p.params.modulusWords[3]),
       .mem (sp - 0x99) 8 (((p.sign.setWidth 32 : BitVec 32).setWidth 64).setWidth 8),
       .mem (sp - 0x60) 64 (v108a39 p),
       .mem (sp - 0x98) 8 ((if !(decide ((v108b25 p : BitVec 64) = 0)) then 1 else 0 : BitVec 8)),
       .mem (sp - 0x9a) 8 ((mergeGPR 8 ((if !(decide ((v108b25 p : BitVec 64) = 0)) then 1 else 0 : BitVec 8)) ((0 : BitVec 64))).setWidth 8)]

def Represents (p : Inputs) (x : Int) : Prop :=
  ∃ neg : Bool, p.sign = (if neg then 1 else 0) ∧
    x = (if neg then -(K256.Proofs.Common.Invert.LinearCombination.wideValue p.magnitude : Int) else (K256.Proofs.Common.Invert.LinearCombination.wideValue p.magnitude : Int))

end K256.Proofs.Verify.Core.Scalars.Inverse.ModularShift
