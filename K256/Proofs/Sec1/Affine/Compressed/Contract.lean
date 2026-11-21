import K256.Proofs.Sec1.Affine.Compressed.Phases
import K256.Proofs.Sec1.Affine.Routines
import K256.Proofs.Sec1.Affine.Uncompressed.Coordinate

namespace K256.Proofs.Sec1.Affine.Compressed

open Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
open K256.Proofs.Refine K256.Proofs.Sec1.LIR K256.Proofs.Common.Field

abbrev Inputs := Uncompressed.CoordinateWords
abbrev inputs (mem : Ram) (src : Word) : Inputs := Uncompressed.readCoordinate mem src
abbrev Inputs.x (v : Inputs) := Uncompressed.CoordinateWords.nat v
abbrev Inputs.valid (v : Inputs) := Uncompressed.CoordinateWords.valid v
abbrev Inputs.masked (v : Inputs) := Uncompressed.CoordinateWords.masked v

structure EntryPre (code : CodeMap) (fr : Activation) (args : Values Value Reg.count) (mem : Ram)
    (want : BitVec 8) : Prop where
  rsp : args[4].get 64 = fr.rsp
  src : args[6].get 64 = fr.rsi
  dst : args[7].get 64 = fr.rdi
  parity : (args[2].get 64).setWidth 8 = want
  rbp : args[5].get 64 = fr.rbp
  rbx : args[3].get 64 = fr.rbx
  r12 : args[12].get 64 = fr.r12
  r13 : args[13].get 64 = fr.r13
  r14 : args[14].get 64 = fr.r14
  r15 : args[15].get 64 = fr.r15
  df : args[22] = ⟨1,0⟩
  mx : args[39] = ⟨32,fr.mxcsr⟩
  ft : args[50] = ⟨16,fr.ftw⟩
  fc : args[51] = ⟨16,fr.fcw⟩
  ret : memLoad mem fr.rsp 64 = fr.ret
  retLow : fr.ret.toNat < 2^32
  slot : Readable mem fr.rsp 8
  stack : Writable code mem (fr.rsp - 0x418) 0x418
  room : fr.low.toNat + 0x418 ≤ fr.rsp.toNat
  align : fr.rsp.toNat % 16 = 8
  input : Readable mem fr.rsi 32
  output : Writable code mem fr.rdi 89
  srcApart : fr.rsi.toNat + 32 ≤ fr.low.toNat ∨ fr.rsp.toNat + 8 ≤ fr.rsi.toNat

structure CubeReady (code : CodeMap) (fr : Activation) (regs : Values Value Reg.count)
    (mem : Ram) (v : Inputs) (want : BitVec 8) : Prop where
  atoms : Atom.All code regs mem (Fn1205b0.frameAt .l12065f fr)
  output : Writable code mem fr.rdi 89
  parity : memLoad mem (workSP fr + 108) 8 = want
  canonical : (regs[0].get 64).setWidth 8 = BitVec.ofNat 8 v.valid.toNat
  r12 : regs[12].get 64 = v.d &&& 0xfffffffffffff
  r13 : regs[13].get 64 = shldResult 12 v.c v.d &&& 0xfffffffffffff
  r14 : regs[14].get 64 = shldResult 24 v.b v.c
  rbx : regs[3].get 64 = shldResult 36 v.a v.b
  r15 : regs[15].get 64 = v.a >>> 16
  rbp : regs[5].get 64 = 0xfffffffffffff

def StartCall (code : CodeMap) : Prop :=
  ∀ (fr : Activation) (args : Values Value Reg.count) (mem : Ram) (want : BitVec 8),
    EntryPre code fr args mem want →
    ∃ (regs : Values Value Reg.count) (m : Ram),
      (program.sem (dialect code)).Reaches ⟨⟨.l1205b0,args,mem⟩,[]⟩ ⟨⟨.l12065f,regs,m⟩,[]⟩ ∧
      CubeReady code fr regs m (inputs mem fr.rsi) want ∧ RamWriteFrame mem m [fr.region]

def DecoderCall (code : CodeMap) : Prop :=
  ∀ (fr : Activation) (args : Values Value Reg.count) (mem : Ram) (tag : UInt8) (want : BitVec 8),
    EntryPre code fr args mem want → Environment fr → want.toNat = tag.toNat % 2 →
    ∃ out, program.Exec (dialect code) ⟨⟨.l1205b0,args,mem⟩,[]⟩ out ∧
      out.tag = some ⟨64,fr.ret⟩ ∧ Atom.All code out.values out.store (Fn1205b0.doneAt fr) ∧
      out.values[0] = ⟨64,fr.rdi⟩ ∧ RamWriteFrame mem out.store [fr.region, ⟨fr.rdi.toNat,89⟩] ∧
      Affine.ResultAt out.store fr.rdi (Sec1.decompress tag (inputs mem fr.rsi).x)

end K256.Proofs.Sec1.Affine.Compressed
