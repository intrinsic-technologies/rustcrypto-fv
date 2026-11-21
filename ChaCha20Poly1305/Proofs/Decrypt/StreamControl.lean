import ChaCha20Poly1305.Proofs.Decrypt.Micro
import ChaCha20Poly1305.Proofs.Decrypt.FullKernel
import ChaCha20Poly1305.Proofs.Decrypt.TailKernel

namespace ChaCha20Poly1305.Proofs.Decrypt.Stream.Control
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program
open Micro

@[refine_layout] def qwords (a : BitVec 64) (v : Vector (BitVec 64) 8) : List Atom :=
  [.mem (a) 64 (v[0]),
   .mem (a+8) 64 (v[1]),
   .mem (a+16) 64 (v[2]),
   .mem (a+24) 64 (v[3]),
   .mem (a+32) 64 (v[4]),
   .mem (a+40) 64 (v[5]),
   .mem (a+48) 64 (v[6]),
   .mem (a+56) 64 (v[7])]

@[refine_layout] def fixedRegs (x : Input) (j : BitVec 64) (fr : Activation) : List Atom :=
  [.gpr 4 (fr.rsp),
   .reg 22 ⟨1,0⟩,
   .reg 39 ⟨32,fr.mxcsr⟩,
   .reg 50 ⟨16,fr.ftw⟩,
   .reg 51 ⟨16,fr.fcw⟩,
   .gpr 0 (j <<< 6),
   .gpr 7 (j),
   .low 10 32 (x.w[4].toBitVec),
   .low 11 32 (x.w[8].toBitVec),
   .low 12 32 (x.w[12].toBitVec),
   .low 8 32 (x.w[13].toBitVec)]

@[refine_layout] def fixedSlots (x : Input) (fr : Activation) : List Atom :=
  [.mem (fr.rsp + 88) 32 (x.w[0].toBitVec),
   .mem (fr.rsp + 16) 32 (x.w[1].toBitVec),
   .mem (fr.rsp + 12) 32 (x.w[2].toBitVec),
   .mem (fr.rsp + 64) 32 (x.w[3].toBitVec),
   .mem (fr.rsp + 56) 32 (x.w[4].toBitVec),
   .mem (fr.rsp + 52) 32 (x.w[5].toBitVec),
   .mem (fr.rsp + 48) 32 (x.w[6].toBitVec),
   .mem (fr.rsp + 44) 32 (x.w[7].toBitVec),
   .mem (fr.rsp + 132) 32 (x.w[8].toBitVec),
   .mem (fr.rsp + 40) 32 (x.w[9].toBitVec),
   .mem (fr.rsp + 36) 32 (x.w[10].toBitVec),
   .mem (fr.rsp + 32) 32 (x.w[11].toBitVec),
   .mem (fr.rsp + 128) 32 (x.w[13].toBitVec),
   .mem (fr.rsp + 28) 32 (x.w[14].toBitVec),
   .mem (fr.rsp + 24) 32 (x.w[15].toBitVec)]

@[refine_layout] def fullSaved (x : Input) (fr : Activation) : List Atom :=
  [.mem (fr.rsp+72) 64 (fr.rdi),
   .mem (fr.rsp+80) 64 (x.n >>> 6),
   .mem (fr.rsp+136) 64 (x.buf),
   .mem (fr.rsp+144) 64 (x.buf),
   .mem (fr.rsp+152) 64 (0),
   .mem (fr.rsp+160) 64 (Tail.rem64 x.n),
   .mem (fr.rsp+168) 64 (x.n)]


@[refine_layout] def blockPtr (x : Input) (j : BitVec 64) := x.buf+(j <<< 6)

@[refine_layout] def loadStep (x : Input) (j : BitVec 64) (fr : Activation) (v : Vector (BitVec 64) 8) : Step where
  entry := .l100efe
  exit := .l100fd0
  pre := fixedRegs x j fr ++ [.mem (fr.rsp+104) 64 x.buf,.writable fr.rsp 368,
    .readable (blockPtr x j) 64,
    .fact (fr.rsp.toNat + 368 ≤ (blockPtr x j).toNat ∨ (blockPtr x j).toNat+64 ≤ fr.rsp.toNat),
    .fact (fr.rsp.toNat+368 ≤ 0x100efe ∨ 0x100fd0 ≤ fr.rsp.toNat)] ++ qwords (blockPtr x j) v
  post := fixedRegs x j fr ++ [.gpr 1 3] ++ qwords (fr.rsp+304) v
  writes := [⟨fr.rsp.toNat+304,64⟩,⟨fr.rsp.toNat+176,64⟩]

@[refine_layout] def writeStep (x : Input) (j : BitVec 64) (fr : Activation) (v : Vector (BitVec 64) 8)
    (last : Bool) : Step where
  entry := .l101036
  exit := if last then .l1010b3 else .l100c70
  pre := fixedRegs x j fr ++ [.mem (fr.rsp+96) 64 x.buf,.mem (fr.rsp+80) 64 (x.n >>> 6),
    .readable fr.rsp 368,.writable (blockPtr x j) 64,
    .fact (fr.rsp.toNat + 368 ≤ (blockPtr x j).toNat ∨ (blockPtr x j).toNat+64 ≤ fr.rsp.toNat),
    .fact ((blockPtr x j).toNat+64 ≤ 0x101036 ∨ 0x1010b3 ≤ (blockPtr x j).toNat)] ++ qwords (fr.rsp+176) v
  post := Full.registers fr ++ [.gpr 7 (j+1),.low 12 32 (x.w[12].toBitVec+1),
    .low 10 32 x.w[4].toBitVec,.low 11 32 x.w[8].toBitVec,.low 8 32 x.w[13].toBitVec] ++ qwords (blockPtr x j) v
  writes := [⟨(blockPtr x j).toNat,64⟩]

@[refine_layout] def spillStep (x : Input) (fr : Activation) (blocks : Bool) : Step where
  entry := .l100ba5
  exit := if blocks then .l100bde else .l1010cc
  pre := Full.registers fr ++ [.writable fr.rsp 368,
    .fact (fr.rsp.toNat+368 ≤ 0x100ba5 ∨ 0x100bde ≤ fr.rsp.toNat),
    .gpr 7 fr.rdi,.gpr 3 x.buf,.gpr 14 x.buf,.gpr 10 0,.gpr 11 x.n,.gpr 15 (Tail.rem64 x.n),
    .low 12 32 x.w[12].toBitVec,.mem (fr.rsp+80) 64 (x.n >>> 6)]
  post := Full.registers fr ++ [.gpr 7 fr.rdi,.gpr 3 x.buf,.gpr 14 x.buf,.gpr 10 0,.gpr 11 x.n,
    .gpr 15 (Tail.rem64 x.n),.low 12 32 x.w[12].toBitVec] ++ fullSaved x fr
  writes := [⟨fr.rsp.toNat+72,8⟩,⟨fr.rsp.toNat+136,40⟩]

@[refine_layout] def prepareStep (x : Input) (fr : Activation) : Step where
  entry := .l100bde
  exit := .l100c70
  pre := Full.registers fr ++ [.writable fr.rsp 368,.readable fr.rdi 64,
    .fact (fr.rsp.toNat+368 ≤ fr.rdi.toNat ∨ fr.rdi.toNat+64 ≤ fr.rsp.toNat),
    .fact (fr.rsp.toNat+368 ≤ 0x100bde ∨ 0x100c70 ≤ fr.rsp.toNat),
    .gpr 7 fr.rdi,.gpr 3 x.buf,.gpr 14 x.buf,.gpr 10 0,.low 12 32 x.w[12].toBitVec] ++ state x fr.rdi
  post := Full.registers fr ++ [.gpr 7 0,.low 10 32 x.w[4].toBitVec,.low 11 32 x.w[8].toBitVec,
    .low 8 32 x.w[13].toBitVec,.low 12 32 x.w[12].toBitVec,.mem (fr.rsp+96) 64 x.buf,
    .mem (fr.rsp+104) 64 x.buf] ++ fixedSlots x fr
  writes := [⟨fr.rsp.toNat+12,8⟩,⟨fr.rsp.toNat+24,36⟩,⟨fr.rsp.toNat+64,4⟩,
     ⟨fr.rsp.toNat+88,24⟩,⟨fr.rsp.toNat+128,8⟩]

@[refine_layout] def updateStep (x : Input) (fr : Activation) : Step where
  entry := .l1010b3
  exit := .l1010cc
  pre := Full.registers fr ++ [.readable fr.rsp 176,.writable fr.rdi 64,
    .fact (fr.rsp.toNat+176 ≤ fr.rdi.toNat ∨ fr.rdi.toNat+64 ≤ fr.rsp.toNat),
    .fact (fr.rdi.toNat+64 ≤ 0x1010b3 ∨ 0x1010cc ≤ fr.rdi.toNat),
    .low 12 32 x.w[12].toBitVec,.mem (fr.rsp+72) 64 fr.rdi,.mem (fr.rsp+168) 64 x.n,
    .mem (fr.rsp+160) 64 (Tail.rem64 x.n)]
  post := Full.registers fr ++ [.gpr 7 fr.rdi,.gpr 11 x.n,.gpr 15 (Tail.rem64 x.n),
    .mem (fr.rdi+48) 32 x.w[12].toBitVec]
  writes := [⟨fr.rdi.toNat+48,4⟩]

end ChaCha20Poly1305.Proofs.Decrypt.Stream.Control
