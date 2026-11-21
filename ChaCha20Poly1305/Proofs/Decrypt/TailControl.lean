import ChaCha20Poly1305.Proofs.Decrypt.StreamControl

namespace ChaCha20Poly1305.Proofs.Decrypt.Stream.Control
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program
open Micro

def rem4 (x : Input) := (x.n.setWidth 32 &&& 3).setWidth 64
def groups (x : Input) := (x.n.setWidth 32 &&& 60).setWidth 64
def tailPtr (x : Input) := x.buf + Tail.base64 x.n

@[refine_layout] def testTail (x : Input) (fr : Activation) (r : Bool) : Step where
  entry := .l1010cc
  exit := if r then .l1010d5 else .l1014a8
  pre := Full.registers fr ++ [.gpr 7 fr.rdi,.gpr 11 x.n,.gpr 15 (Tail.rem64 x.n)]
  post := Full.registers fr ++ [.gpr 7 fr.rdi,.gpr 11 x.n]
  writes := []

@[refine_layout] def tailState (x : Input) (fr : Activation) : List Atom :=
  [.gpr 9 fr.rdi,.gpr 10 x.n,.gpr 14 (Tail.rem64 x.n),.gpr 0 (rem4 x),
   .readable fr.rsp 176,.mem (fr.rsp+152) 64 0,.mem (fr.rsp+144) 64 x.buf,
   .mem (fr.rsp+136) 64 x.buf,.mem (fr.rsp+64) 64 (Tail.base64 x.n)]

@[refine_layout] def tailRegs (x : Input) (fr : Activation) : List Atom :=
  Full.registers fr ++ [.gpr 3 x.buf,.gpr 11 x.buf,.gpr 14 (Tail.rem64 x.n),.gpr 15 (Tail.base64 x.n),
    .gpr 9 fr.rdi,.gpr 8 0,.gpr 0 (rem4 x)]

@[refine_layout] def smallStart (x : Input) (fr : Activation) : Step where
  entry := .l1013bf
  exit := .l10146c
  pre := Full.registers fr ++ tailState x fr
  post := tailRegs x fr ++ [.gpr 6 0]
  writes := []

@[refine_layout] def fourStart (x : Input) (fr : Activation) : Step where
  entry := .l1013e3
  exit := .l101420
  pre := Full.registers fr ++ tailState x fr
  post := tailRegs x fr ++ [.gpr 1 (tailPtr x+3),.gpr 2 (tailPtr x+3),.gpr 6 0,.gpr 10 (groups x)]
  writes := []

@[refine_layout] def fourEnd (x : Input) (fr : Activation) (r : Bool) : Step where
  entry := .l101467
  exit := if r then .l10146c else .l1014a4
  pre := tailRegs x fr ++ [.gpr 6 (groups x)]
  post := tailRegs x fr ++ [.gpr 6 (groups x)]
  writes := []

@[refine_layout] def oneStart (x : Input) (fr : Activation) : Step where
  entry := .l10146c
  exit := .l101490
  pre := tailRegs x fr ++ [.gpr 6 (groups x)]
  post := Full.registers fr ++ [.gpr 0 (rem4 x),.gpr 9 fr.rdi,.gpr 14 (Tail.rem64 x.n),
    .gpr 1 (fr.rdi+groups x+64),.gpr 2 0,.gpr 3 (tailPtr x+groups x),
    .gpr 11 (tailPtr x+groups x)]
  writes := []

@[refine_layout] def finishTail (x : Input) (fr : Activation) : Step where
  entry := .l1014a4
  exit := .l1014a8
  pre := Full.registers fr ++ [.gpr 9 fr.rdi,.gpr 14 (Tail.rem64 x.n),.writable fr.rdi 128,
    .fact (fr.rdi.toNat+128 ≤ 0x1014a4 ∨ 0x1014a8 ≤ fr.rdi.toNat)]
  post := Full.registers fr ++ [.mem (fr.rdi+64) 8 ((Tail.rem64 x.n).setWidth 8)]
  writes := [⟨fr.rdi.toNat+64,1⟩]

end ChaCha20Poly1305.Proofs.Decrypt.Stream.Control
