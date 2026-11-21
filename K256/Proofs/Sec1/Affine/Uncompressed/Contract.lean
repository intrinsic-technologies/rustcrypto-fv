import K256.Proofs.Sec1.Affine.Uncompressed.Arithmetic
import K256.Proofs.Common.CFG.Simulation

namespace K256.Proofs.Sec1.Affine.Uncompressed

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
open K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Sec1.LIR

structure EntryPre (code : CodeMap) (args : Values Value Reg.count) (mem : Ram)
    (sp dst x y ret : Word) : Prop where
  rsp : args[4].get 64 = sp
  rdi : args[7].get 64 = dst
  rsi : args[6].get 64 = x
  rdx : args[2].get 64 = y
  savedWidth : ∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15] → args[i] = ⟨64,args[i].get 64⟩
  stack : Writable code mem (sp - 273) 273
  room : 273 ≤ sp.toNat
  slot : Readable mem sp 8
  retWord : memLoad mem sp 64 = ret
  retLow : ret.toNat < 2^32
  output : Writable code mem dst 89
  inputX : Readable mem x 32
  inputY : Readable mem y 32
  apartX : x.toNat + 32 ≤ sp.toNat - 273 ∨ sp.toNat ≤ x.toNat
  apartY : y.toNat + 32 ≤ sp.toNat - 273 ∨ sp.toNat ≤ y.toNat
  apartDst : dst.toNat + 89 ≤ sp.toNat - 273 ∨ sp.toNat + 8 ≤ dst.toNat

def SavedWords (args : Values Value Reg.count) (m : Ram) (sp : Word) : Prop :=
  memLoad m (sp-48) 64 = args[3].get 64 ∧ memLoad m (sp-40) 64 = args[12].get 64 ∧
  memLoad m (sp-32) 64 = args[13].get 64 ∧ memLoad m (sp-24) 64 = args[14].get 64 ∧
  memLoad m (sp-16) 64 = args[15].get 64 ∧ memLoad m (sp-8) 64 = args[5].get 64

structure Prepared (args regs : Values Value Reg.count) (mem m : Ram) (sp dst : Word)
    (x y : CoordinateWords) : Prop where
  stack : regs[4].get 64 = sp - 264
  bit : (regs[0].get 64).setWidth 8 = BitVec.ofNat 8 y.valid.toNat
  r15 : regs[15].get 64 = y.d &&& 0xfffffffffffff
  r13 : regs[13].get 64 = shldResult 12 y.c y.d &&& 0xfffffffffffff
  r12 : regs[12].get 64 = shldResult 24 y.b y.c
  rbx : regs[3].get 64 = shldResult 36 y.a y.b
  r14 : regs[14].get 64 = y.a >>> 16
  rbp : regs[5].get 64 = 0xfffffffffffff
  xLimbs : localLimbs m (sp - 264) false = x.masked
  xFlag : memLoad m (sp - 264 + 200) 64 = BitVec.ofNat 64 x.valid.toNat
  output : memLoad m (sp - 264 + 208) 64 = dst
  saved : SavedWords args m sp
  kept : ∀ i : Fin Reg.count, i.val ∈ [22,39,50,51] → regs[i] = args[i]
  frame : RamWriteFrame mem m [⟨(sp - 273).toNat, 273⟩]

def StartCall (code : CodeMap) : Prop :=
  ∀ args mem sp dst x y ret, EntryPre code args mem sp dst x y ret →
    ∃ regs m, (program.sem (dialect code)).Reaches ⟨⟨.l11f780,args,mem⟩,[]⟩ ⟨⟨.l11f8f6,regs,m⟩,[]⟩ ∧
      Prepared args regs mem m sp dst (readCoordinate mem x) (readCoordinate mem y)

def DecoderCall (code : CodeMap) : Prop :=
  ∀ args mem sp dst x y ret, EntryPre code args mem sp dst x y ret →
    let point := Standards.SECG.ECC.Curve.Point.affine (readCoordinate mem x).nat (readCoordinate mem y).nat
    let ok := Standards.SECG.ECC.Curve.onCurve Standards.SECG.DomainParameters.Secp256k1.domain point
    ∃ out, program.Exec (dialect code) ⟨⟨.l11f780,args,mem⟩,[]⟩ out ∧
      out.tag = some ⟨64,ret⟩ ∧ out.values[4] = ⟨64,sp+8⟩ ∧ out.values[0] = ⟨64,dst⟩ ∧
      (∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15,22,39,50,51] → out.values[i] = args[i]) ∧
      RamWriteFrame mem out.store [⟨(sp-273).toNat,273⟩, ⟨dst.toNat,89⟩] ∧
      memLoad out.store (dst + 88) 8 = BitVec.ofNat 8 ok.toNat ∧
      (ok = true → K256.Proofs.Sec1.Parser.PublicKeyAt out.store dst point)

end K256.Proofs.Sec1.Affine.Uncompressed
