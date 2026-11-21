import P256.Proofs.Field.Inverse.SafeGcd.Correction.Model
import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.Machine
import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.Machine.Correction.Frame
import P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.Support

namespace P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

inductive Label where
  | entry | stage0 | stage1 | stage2 | stage3 | stage4 | stage5 | stage6

@[refine_layout] def start : Label → Machine.Label
  | .entry => .l1181a0
  | .stage0 => .l1181ad
  | .stage1 => .l1181e3
  | .stage2 => .l11821e
  | .stage3 => .l118251
  | .stage4 => .l118288
  | .stage5 => .l1182a7
  | .stage6 => .l1182f8

inductive Op : Nat → Type

def program : Program Op Label (fun _ => 0) 0 where
  blocks
  | .entry => .terminate (.br ⟨.stage0, #v[]⟩)
  | .stage0 => .terminate (.br ⟨.stage1, #v[]⟩)
  | .stage1 => .terminate (.br ⟨.stage2, #v[]⟩)
  | .stage2 => .terminate (.br ⟨.stage3, #v[]⟩)
  | .stage3 => .terminate (.br ⟨.stage4, #v[]⟩)
  | .stage4 => .terminate (.br ⟨.stage5, #v[]⟩)
  | .stage5 => .terminate (.br ⟨.stage6, #v[]⟩)
  | .stage6 => .terminate (.ret #v[])

@[refine_layout] def commonAtoms (fr : Activation) (controls : RamState) (p : Inputs) : List Atom :=
  [.reg 39 ⟨32, controls.MXCSR⟩, .reg 51 ⟨16, controls.FP87_Control⟩,
   .writable fr.rdi 32,
   .fact (fr.rdi.toNat + 32 ≤ fr.low.toNat ∨ fr.rsp.toNat + 8 ≤ fr.rdi.toNat),
   .words fr.rsi 64 p.magnitude, .words fr.rcx 64 p.modulus,
   .mem (fr.rsi + 32) 8 p.sign, .readable fr.rsi 33, .readable fr.rcx 32,
   .fact (fr.rsi.toNat + 33 ≤ fr.low.toNat ∨ fr.rsp.toNat ≤ fr.rsi.toNat),
   .fact (fr.rcx.toNat + 32 ≤ fr.low.toNat ∨ fr.rsp.toNat ≤ fr.rcx.toNat),
   .fact (fr.rdx = p.negate)]

@[refine_layout] def coreAtoms (l : Label) (fr : Activation) (p : Inputs) : List Atom :=
  match l with
  | .entry | .stage0 => []
  | .stage1 =>
      [.gpr 2 (mergeGPR 8 (v1181db p) (p.negate)),
       .gpr 10 (p.magnitude[0]),
       .gpr 9 (p.magnitude[1]),
       .gpr 8 (p.magnitude[2]),
       .gpr 0 (p.magnitude[3]),
       .gpr 11 (v1181c2 p),
       .gpr 14 (v1181cb p),
       .mem (fr.rsp - 0x30) 64 (v1181d7 p)]
  | .stage2 =>
      [.gpr 6 ((v118200 p).1),
       .gpr 2 (mergeGPR 8 (v1181db p) (p.negate)),
       .gpr 10 (p.magnitude[0]),
       .gpr 9 (p.magnitude[1]),
       .gpr 8 (p.magnitude[2]),
       .gpr 0 (p.magnitude[3]),
       .gpr 3 (v118215 p),
       .gpr 11 (v1181c2 p),
       .gpr 14 (((0 : BitVec 32) : BitVec 32).setWidth 64),
       .mem (fr.rsp - 0x30) 64 (v118215 p)]
  | .stage3 =>
      [.gpr 6 ((v118200 p).1),
       .gpr 2 (mergeGPR 8 (v1181db p) (p.negate)),
       .gpr 10 (p.magnitude[0]),
       .gpr 9 (p.magnitude[1]),
       .gpr 8 (p.magnitude[2]),
       .gpr 0 (p.magnitude[3]),
       .gpr 3 ((v118233 p).1),
       .gpr 11 (v1181c2 p),
       .gpr 14 (((0 : BitVec 32) : BitVec 32).setWidth 64),
       .gpr 15 (v118248 p),
       .mem (fr.rsp - 0x30) 64 (v118248 p)]
  | .stage4 =>
      [.gpr 6 ((v118200 p).1),
       .gpr 2 (mergeGPR 8 (v1181db p) (p.negate)),
       .gpr 10 (p.magnitude[0]),
       .gpr 9 (p.magnitude[1]),
       .gpr 8 (p.magnitude[2]),
       .gpr 0 (p.magnitude[3]),
       .gpr 3 ((v118233 p).1),
       .gpr 11 (v1181c2 p),
       .gpr 14 (((0 : BitVec 32) : BitVec 32).setWidth 64),
       .gpr 15 ((v11826a p).1),
       .mem (fr.rsp - 0x30) 64 (v11827f p)]
  | .stage5 =>
      [.gpr 6 ((v118200 p).1),
       .gpr 2 (((if decide (v118294 p = 0) then ((((0 : BitVec 32) : BitVec 32).setWidth 64).setWidth 32) else (((((mergeGPR 8 (v118291 p) (mergeGPR 8 (v1181db p) (p.negate))).setWidth 8).setWidth 32 : BitVec 32).setWidth 64).setWidth 32)) : BitVec 32).setWidth 64),
       .gpr 10 (p.magnitude[0]),
       .gpr 9 (p.magnitude[1]),
       .gpr 8 (p.magnitude[2]),
       .gpr 0 (p.magnitude[3]),
       .gpr 3 ((v118233 p).1),
       .gpr 11 (v1181c2 p),
       .gpr 15 ((v11826a p).1),
       .mem (fr.rsp - 0x30) 64 (v11827f p),
       .mem (fr.rsp - 0x31) 8 ((((if decide (v118294 p = 0) then ((((0 : BitVec 32) : BitVec 32).setWidth 64).setWidth 32) else (((((mergeGPR 8 (v118291 p) (mergeGPR 8 (v1181db p) (p.negate))).setWidth 8).setWidth 32 : BitVec 32).setWidth 64).setWidth 32)) : BitVec 32).setWidth 64).setWidth 8)]
  | .stage6 =>
      [.gpr 6 (v1182e0 p),
       .gpr 2 (v1182f5 p),
       .gpr 1 (v1182b5 p),
       .gpr 10 (v1182cb p),
       .gpr 0 (p.magnitude[3]),
       .mem (fr.rsp - 0x30) 64 (v11827f p),
       .mem (fr.rsp - 0x31) 8 ((((if decide (v118294 p = 0) then ((((0 : BitVec 32) : BitVec 32).setWidth 64).setWidth 32) else (((((mergeGPR 8 (v118291 p) (mergeGPR 8 (v1181db p) (p.negate))).setWidth 8).setWidth 32 : BitVec 32).setWidth 64).setWidth 32)) : BitVec 32).setWidth 64).setWidth 8)]

def dialect : Dialect Op Unit Inputs where
  eval op := nomatch op
  truth _ := false

@[refine_layout] def outputRegion (fr : Activation) : MemoryRegion := ⟨fr.rdi.toNat, 32⟩

def layout (fr : Activation) (controls : RamState) : Layout program dialect Machine.lifted Unit where
  start := start
  Params _ := Inputs
  args _ _ := #v[]
  store _ p := p
  atoms l _ p := Machine.Correction.frameAt (start l) fr ++ commonAtoms fr controls p ++ coreAtoms l fr p
  Result := Inputs
  output p := ⟨#v[], none, p⟩
  done _ p := Machine.Correction.doneAt fr ++
    [.words fr.rdi 64 (correctedWords p), .readable fr.rdi 32,
     .reg 39 ⟨32, controls.MXCSR⟩, .reg 51 ⟨16, controls.FP87_Control⟩]
  retAddr _ := fr.ret
  original _ := fr.original
  regions _ := [fr.region, outputRegion fr]

end P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution
