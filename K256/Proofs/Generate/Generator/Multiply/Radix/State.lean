import K256.Proofs.Common.Tactic
import K256.Proofs.Generate.LIR.Fn11aa40.Frame
import K256.Proofs.Generate.Curve.Window
import K256.Proofs.ParseSignature.Contract

namespace K256.Proofs.Generate.Generator.Multiply.Radix

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine
open K256.Proofs.Generate.LIR

def byte (x i : Nat) : BitVec 8 :=
  if i = 32 then BitVec.ofNat 8 (Generate.Curve.radixCarry x i)
  else BitVec.ofInt 8 (Generate.Curve.radixDigit (Generate.Curve.radixRemaining x i))


def nibble (x i : Nat) := Nat.mod (x / 16^i) 16

def pending (x i : Nat) : BitVec 8 :=
  BitVec.ofNat 8 (nibble x i + Generate.Curve.radixCarry x i)

def stackByte (x pos i : Nat) : BitVec 8 :=
  if i < pos then byte x i else if i = pos then pending x i else BitVec.ofNat 8 (nibble x i)

abbrev regs := Values Value Reg.count

def loopLabel (pos : Nat) : Label := if pos = 32 then .l11ac3d else .l11ac00

structure LoopState (code : CodeMap) (fr : Activation) (initial m : Ram)
    (a : regs) (x pos : Nat) : Prop where
  atoms : Atom.All code a m (Fn11aa40.frameAt .l11ac00 fr)
  widths : ParseSignature.ArgumentWidths a
  index : a[2].get 64 = BitVec.ofNat 64 (pos + 2)
  current : a[1].get 8 = pending x pos
  stack : WordsAt m (fr.rsp - 33) 8 (Vector.ofFn fun i : Fin 33 => stackByte x pos i.val)
  frame : RamWriteFrame initial m [⟨(fr.rsp - 33).toNat, 33⟩]

abbrev Path (code : CodeMap) (l : Label) (a : regs) (m : Ram) (l' : Label) (b : regs) (n : Ram) :=
  (program.sem (dialect code)).Reaches ⟨⟨l, a, m⟩, []⟩ ⟨⟨l', b, n⟩, []⟩

end K256.Proofs.Generate.Generator.Multiply.Radix
