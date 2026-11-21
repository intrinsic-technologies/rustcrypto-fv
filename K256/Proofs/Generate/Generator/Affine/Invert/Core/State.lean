import K256.Proofs.Generate.Generator.Affine.Invert.Contract
import K256.Proofs.Generate.Generator.Affine.Invert.SafeGcd.Model

namespace K256.Proofs.Generate.Generator.Affine.Invert.Core

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Generate.LIR

structure Entry (a : Registers) (m : Ram) (sp : Word) (z : Fin modulus) (w : Vector Word 4) : Prop where
  rsp : a[4] = ⟨64, sp⟩
  rcx : a[1] = ⟨64, 0x27c7f6e22ddacacf⟩
  rdx : a[2] = ⟨64, 0x2021e0⟩
  rsi : a[6] = ⟨64, sp + 8⟩
  rdi : a[7] = ⟨64, sp + 96⟩
  r8 : a[8] = ⟨64, 0x202180⟩
  df : a[22] = ⟨1, 0⟩
  widths : ∀ i : Fin Reg.count, i.val ∈ [3, 5, 12, 13, 14, 15] → a[i].width = 64
  image : ∀ b ∈ Extracted.programImage, m[b.1]? = some b.2
  low : 736 ≤ sp.toNat
  high : sp.toNat + 129 ≤ 2^32
  aligned : sp.toNat % 16 = 8
  slot1Read : Readable m 0x203de0 8
  slot1 : memLoad m 0x203de0 64 = 0x129770
  slot2Read : Readable m 0x203e20 8
  slot2 : memLoad m 0x203e20 64 = 0x100a20
  apart : 0x204108 ≤ sp.toNat ∨ sp.toNat ≤ 0x203de0
  stack : Writable Extracted.programImage m (sp - 736) 736
  source : Readable m sp 40
  destination : Writable Extracted.programImage m (sp + 96) 33
  ret : memLoad m sp 64 = 0x10ed84
  words : WordsAt m (sp + 8) 64 w
  input : value w = z.val
  nonzero : z.val ≠ 0

def signedAt (m : Ram) (addr : Word) (x : Int) : Prop :=
  ∃ (v : Vector Word 4) (neg : Bool), WordsAt m addr 64 v ∧
    memLoad m (addr + 32) 8 = (if neg then 1 else 0) ∧
    x = (if neg then -(value v : Int) else (value v : Int))

def model (z : Fin modulus) (n : Nat) : SafeGcd.DivState :=
  SafeGcd.divsteps n ⟨1, modulus, z.val⟩

abbrev base (sp : Word) := sp - 408

structure LoopState (entry : Registers) (original : Ram) (sp : Word) (z : Fin modulus)
    (n : Nat) (a : Registers) (m : Ram) (d e : Int) : Prop where
  rsp : a[4] = ⟨64, base sp⟩
  delta : a[5] = ⟨64, BitVec.ofInt 64 (model z n).delta⟩
  remaining : a[2] = ⟨64, BitVec.ofNat 64 (591 - n)⟩
  scratch : a[14] = ⟨64, base sp + 16⟩
  kept : ∀ i : Fin Reg.count, i.val ∈ [22, 39, 50, 51] → a[i] = entry[i]
  saved : ∀ (i : Fin Reg.count) (off : Nat),
    (i.val, off) ∈ [(3,48),(5,8),(12,40),(13,32),(14,24),(15,16)] →
      memLoad m (sp - BitVec.ofNat 64 off) 64 = entry[i].get 64
  frame : RamWriteFrame original m [⟨(sp - 736).toNat, 736⟩]
  fValue : signedAt m (base sp + 120) (model z n).f
  gValue : signedAt m (base sp + 168) (model z n).g
  dValue : signedAt m (base sp + 208) d
  eValue : signedAt m (base sp + 248) e
  dBound : d.natAbs < modulus
  eBound : e.natAbs < modulus
  dInvariant : (d * z.val) % (modulus : Int) = (model z n).f % modulus
  eInvariant : (e * z.val) % (modulus : Int) = (model z n).g % modulus
  originalNonzero : (((memLoad m (base sp + 312) 64 ||| memLoad m (base sp + 296) 64) |||
    memLoad m (base sp + 288) 64) ||| memLoad m (base sp + 304) 64) ≠ 0
  outputPtr : memLoad m (base sp + 320) 64 = sp + 96
  modulusPtr : memLoad m (base sp + 160) 64 = 0x2021e0
  modulusInverse : memLoad m (base sp + 328) 64 = 0x27c7f6e22ddacacf

def roundsBefore (batch : Nat) := min (62 * batch) 591

def batchLabel (batch : Nat) : Label := if batch = 10 then .l1093fe else .l1091e4

def Result (entry : Registers) (m : Ram) (sp : Word) (z : Fin modulus)
    (out : Output Value Ram Reg.count) : Prop :=
  out.tag = some ⟨64, 0x10ed84⟩ ∧ out.values[4] = ⟨64, sp + 8⟩ ∧
  (∀ i : Fin Reg.count, i.val ∈ [3, 5, 12, 13, 14, 15, 22, 39, 50, 51] →
    out.values[i] = entry[i]) ∧
  RamWriteFrame m out.store [⟨(sp - 736).toNat, 736⟩, ⟨(sp + 96).toNat, 33⟩] ∧
  ∃ v : Vector Word 4, WordsAt out.store (sp + 96) 64 v ∧ value v = (inverse z).val ∧
    memLoad out.store (sp + 128) 8 = 1

end K256.Proofs.Generate.Generator.Affine.Invert.Core
