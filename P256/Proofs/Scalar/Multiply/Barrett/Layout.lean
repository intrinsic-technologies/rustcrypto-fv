import P256.Proofs.Scalar.Multiply.Model
import P256.Proofs.Scalar.Multiply.Barrett.Machine.Eval
import P256.Proofs.Scalar.Multiply.Barrett.Machine.Reduce.Frame
import P256.Proofs.Scalar.Multiply.Barrett.Support

namespace P256.Proofs.Scalar.Multiply.Barrett

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

inductive Label where
  | entry | stage0 | stage1 | stage2 | stage3 | stage4 | stage5 | stage6 | stage7 | stage8 | stage9 | stage10 | stage11 | stage12 | stage13 | stage14 | stage15 | stage16 | stage17 | stage18 | stage19

@[refine_layout] def start : Label → Machine.Label
  | .entry => .l118320
  | .stage0 => .l11832e
  | .stage1 => .l11839b
  | .stage2 => .l118420
  | .stage3 => .l1184ac
  | .stage4 => .l118544
  | .stage5 => .l1185d2
  | .stage6 => .l118654
  | .stage7 => .l1186f3
  | .stage8 => .l118722
  | .stage9 => .l118752
  | .stage10 => .l118782
  | .stage11 => .l1187b8
  | .stage12 => .l1187ed
  | .stage13 => .l11880b
  | .stage14 => .l118837
  | .stage15 => .l118856
  | .stage16 => .l118882
  | .stage17 => .l1188a1
  | .stage18 => .l1188c5
  | .stage19 => .l1188e7

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
  | .stage6 => .terminate (.br ⟨.stage7, #v[]⟩)
  | .stage7 => .terminate (.br ⟨.stage8, #v[]⟩)
  | .stage8 => .terminate (.br ⟨.stage9, #v[]⟩)
  | .stage9 => .terminate (.br ⟨.stage10, #v[]⟩)
  | .stage10 => .terminate (.br ⟨.stage11, #v[]⟩)
  | .stage11 => .terminate (.br ⟨.stage12, #v[]⟩)
  | .stage12 => .terminate (.br ⟨.stage13, #v[]⟩)
  | .stage13 => .terminate (.br ⟨.stage14, #v[]⟩)
  | .stage14 => .terminate (.br ⟨.stage15, #v[]⟩)
  | .stage15 => .terminate (.br ⟨.stage16, #v[]⟩)
  | .stage16 => .terminate (.br ⟨.stage17, #v[]⟩)
  | .stage17 => .terminate (.br ⟨.stage18, #v[]⟩)
  | .stage18 => .terminate (.br ⟨.stage19, #v[]⟩)
  | .stage19 => .terminate (.ret #v[])

@[refine_layout] def commonAtoms (fr : Activation) (controls : RamState) (p : Inputs) : List Atom :=
  [.reg 39 ⟨32, controls.MXCSR⟩, .reg 51 ⟨16, controls.FP87_Control⟩,
   .writable fr.rdi 32,
   .fact (fr.rdi.toNat + 32 ≤ fr.low.toNat ∨ fr.rsp.toNat + 8 ≤ fr.rdi.toNat),
   .words fr.rsi 64 p.low, .words fr.rdx 64 p.high, .readable fr.rsi 32, .readable fr.rdx 32,
   .fact (fr.rsi.toNat + 32 ≤ fr.low.toNat ∨ fr.rsp.toNat ≤ fr.rsi.toNat),
   .fact (fr.rdx.toNat + 32 ≤ fr.low.toNat ∨ fr.rsp.toNat ≤ fr.rdx.toNat)]

@[refine_layout] def coreAtoms (l : Label) (fr : Activation) (p : Inputs) : List Atom :=
  match l with
  | .entry | .stage0 => []
  | .stage1 =>
      [.gpr 6 ((v118395 p).1),
       .gpr 12 (fr.rdx),
       .gpr 9 (85565669623438334),
       .gpr 13 (4834901528447446049),
       .gpr 10 ((v11838f p).1),
       .gpr 5 (18446744069414584319),
       .gpr 3 ((v118392 p).1),
       .gpr 11 ((v118398 p).1),
       .mem (fr.rsp - 0x48) 64 (fr.rsi),
       .mem (fr.rsp - 0x38) 64 (p.low[3]),
       .reg 16 (Value.ofBool ((v118398 p).2.CF))]
  | .stage2 =>
      [.gpr 12 ((v1183fb p).1),
       .gpr 9 (85565669623438334),
       .gpr 8 (fr.rdx),
       .gpr 13 (p.high[1]),
       .gpr 10 ((v118410 p).1),
       .gpr 14 ((v1183d9 p).1),
       .gpr 3 ((v118413 p).1),
       .gpr 15 ((v1183f8 p).1),
       .mem (fr.rsp - 0x48) 64 (fr.rsi),
       .mem (fr.rsp - 0x38) 64 (p.low[3]),
       .mem (fr.rsp - 0x58) 64 ((v1183a5 p).1),
       .mem (fr.rsp - 0x68) 8 ((if (v1183a5 p).2.CF then 1 else 0 : BitVec 8)),
       .mem (fr.rsp - 0x40) 64 (p.high[0]),
       .mem (fr.rsp - 0x60) 64 (fr.rdx)]
  | .stage3 =>
      [.gpr 12 (p.high[2]),
       .gpr 1 ((v118477 p).1),
       .gpr 0 (p.high[2]),
       .gpr 13 ((v11849e p).1),
       .gpr 10 ((v118486 p).1),
       .gpr 14 ((v1184a1 p).1),
       .gpr 15 ((v118489 p).1),
       .gpr 11 ((v118450 p).1),
       .mem (fr.rsp - 0x48) 64 (fr.rsi),
       .mem (fr.rsp - 0x38) 64 (p.low[3]),
       .mem (fr.rsp - 0x58) 64 ((v1183a5 p).1),
       .mem (fr.rsp - 0x68) 8 ((if (v118477 p).2.CF then 1 else 0 : BitVec 8)),
       .mem (fr.rsp - 0x40) 64 (p.high[0]),
       .mem (fr.rsp - 0x60) 64 (fr.rdx)]
  | .stage4 =>
      [.gpr 1 (mergeGPR 8 ((if (v11850c p).2.CF then 1 else 0 : BitVec 8)) ((v118477 p).1)),
       .gpr 9 (p.high[3]),
       .gpr 0 (p.high[3]),
       .gpr 8 ((v11850c p).1),
       .gpr 10 ((v11851c p).1),
       .gpr 5 ((v118519 p).1),
       .gpr 3 ((v1184e3 p).1),
       .gpr 15 ((v118531 p).1),
       .gpr 11 ((v118534 p).1),
       .mem (fr.rsp - 0x48) 64 (fr.rsi),
       .mem (fr.rsp - 0x38) 64 (p.low[3]),
       .mem (fr.rsp - 0x58) 64 ((v1183a5 p).1),
       .mem (fr.rsp - 0x68) 8 ((if (v118477 p).2.CF then 1 else 0 : BitVec 8)),
       .mem (fr.rsp - 0x40) 64 (p.high[0]),
       .mem (fr.rsp - 0x60) 64 (fr.rdx)]
  | .stage5 =>
      [.gpr 6 ((((mergeGPR 8 ((if (v1185a1 p).2.CF then 1 else 0 : BitVec 8)) ((v11850c p).1)).setWidth 8).setWidth 32 : BitVec 32).setWidth 64),
       .gpr 2 ((v1185c7 p).1),
       .gpr 1 ((v1185a1 p).1),
       .gpr 14 ((v11857b p).1),
       .gpr 3 ((v1185af p).1),
       .gpr 15 ((v1185cb p).1),
       .mem (fr.rsp - 0x48) 64 (fr.rsi),
       .mem (fr.rsp - 0x38) 64 (p.low[3]),
       .mem (fr.rsp - 0x58) 64 ((v1183a5 p).1),
       .mem (fr.rsp - 0x68) 8 ((if (v118477 p).2.CF then 1 else 0 : BitVec 8)),
       .mem (fr.rsp - 0x40) 64 (p.high[0]),
       .mem (fr.rsp - 0x60) 64 (fr.rdx),
       .reg 16 (Value.ofBool ((v1185cb p).2.CF))]
  | .stage6 =>
      [.gpr 12 ((v118615 p).1),
       .gpr 1 ((v1185d2 p).1),
       .gpr 9 ((v118600 p).1),
       .gpr 0 ((v1185af p).1),
       .gpr 8 (17562291160714782033),
       .gpr 10 ((v11864e p).1),
       .gpr 14 ((v118641 p).2),
       .gpr 3 ((v1185af p).1),
       .gpr 15 ((v1185cb p).1),
       .gpr 11 ((v118641 p).1),
       .mem (fr.rsp - 0x48) 64 (fr.rsi),
       .mem (fr.rsp - 0x38) 64 (p.low[3]),
       .mem (fr.rsp - 0x58) 64 ((v1185e6 p).2),
       .mem (fr.rsp - 0x40) 64 (p.high[0]),
       .mem (fr.rsp - 0x60) 64 ((v118600 p).2),
       .mem (fr.rsp - 0x68) 64 ((v1185e6 p).1),
       .mem (fr.rsp - 0x50) 64 ((v118615 p).2)]
  | .stage7 =>
      [.gpr 2 ((v1186dc p).2),
       .gpr 1 (fr.rsi),
       .gpr 9 ((v118689 p).1),
       .gpr 0 ((v1186dc p).1),
       .gpr 8 (p.low[0]),
       .gpr 13 ((v1186e2 p).1),
       .gpr 14 ((v1186e5 p).1),
       .gpr 3 ((v1186e8 p).1),
       .gpr 15 (17562291160714782033),
       .mem (fr.rsp - 0x48) 64 (fr.rsi),
       .mem (fr.rsp - 0x38) 64 (p.low[3]),
       .mem (fr.rsp - 0x58) 64 ((v1185e6 p).2),
       .mem (fr.rsp - 0x40) 64 (p.high[0]),
       .mem (fr.rsp - 0x60) 64 ((v118600 p).2),
       .mem (fr.rsp - 0x68) 64 ((v1185e6 p).1),
       .mem (fr.rsp - 0x50) 64 ((v118615 p).2)]
  | .stage8 =>
      [.gpr 6 (p.low[1]),
       .gpr 1 (p.low[2]),
       .gpr 9 ((v118689 p).1),
       .gpr 0 (v118701 p),
       .gpr 8 (v11871e p),
       .gpr 13 ((v1186e2 p).1),
       .gpr 14 ((v1186f3 p).1),
       .gpr 3 ((v1186f6 p).1),
       .gpr 15 (17562291160714782033),
       .mem (fr.rsp - 0x48) 64 (fr.rsi),
       .mem (fr.rsp - 0x38) 64 (p.low[3]),
       .mem (fr.rsp - 0x58) 64 ((v1185e6 p).2),
       .mem (fr.rsp - 0x40) 64 (p.high[0]),
       .mem (fr.rsp - 0x60) 64 ((v118600 p).2),
       .mem (fr.rsp - 0x68) 64 ((v1185e6 p).1),
       .mem (fr.rsp - 0x50) 64 ((v118615 p).2)]
  | .stage9 =>
      [.gpr 6 (v11874e p),
       .gpr 2 ((v118739 p).1),
       .gpr 1 (p.low[2]),
       .gpr 9 ((v118689 p).1),
       .gpr 0 (v118701 p),
       .gpr 13 ((v1186e2 p).1),
       .gpr 14 ((v1186f3 p).1),
       .gpr 3 ((v1186f6 p).1),
       .gpr 15 (17562291160714782033),
       .mem (fr.rsp - 0x48) 64 (fr.rsi),
       .mem (fr.rsp - 0x38) 64 (p.low[3]),
       .mem (fr.rsp - 0x58) 64 ((v1185e6 p).2),
       .mem (fr.rsp - 0x40) 64 (p.high[0]),
       .mem (fr.rsp - 0x60) 64 ((v118600 p).2),
       .mem (fr.rsp - 0x68) 64 ((v1185e6 p).1),
       .mem (fr.rsp - 0x50) 64 ((v118615 p).2),
       .mem (fr.rsp - 0x70) 64 (v11871e p)]
  | .stage10 =>
      [.gpr 6 ((v118769 p).1),
       .gpr 2 ((v118739 p).1),
       .gpr 1 (v11877e p),
       .gpr 9 ((v118689 p).1),
       .gpr 0 (v118701 p),
       .gpr 14 ((v1186f3 p).1),
       .gpr 3 ((v1186f6 p).1),
       .gpr 15 (17562291160714782033),
       .mem (fr.rsp - 0x48) 64 (fr.rsi),
       .mem (fr.rsp - 0x38) 64 (p.low[3]),
       .mem (fr.rsp - 0x58) 64 ((v1185e6 p).2),
       .mem (fr.rsp - 0x40) 64 (p.high[0]),
       .mem (fr.rsp - 0x60) 64 ((v118600 p).2),
       .mem (fr.rsp - 0x68) 64 ((v1185e6 p).1),
       .mem (fr.rsp - 0x50) 64 ((v118615 p).2),
       .mem (fr.rsp - 0x70) 64 (v11874e p)]
  | .stage11 =>
      [.gpr 6 ((v118769 p).1),
       .gpr 2 ((v118739 p).1),
       .gpr 9 ((v11879f p).1),
       .gpr 0 (v118701 p),
       .gpr 8 (v1187b4 p),
       .gpr 3 ((v1186f6 p).1),
       .gpr 15 (17562291160714782033),
       .mem (fr.rsp - 0x48) 64 (fr.rsi),
       .mem (fr.rsp - 0x38) 64 (p.low[3]),
       .mem (fr.rsp - 0x58) 64 ((v1185e6 p).2),
       .mem (fr.rsp - 0x40) 64 (p.high[0]),
       .mem (fr.rsp - 0x60) 64 ((v118600 p).2),
       .mem (fr.rsp - 0x68) 64 ((v1185e6 p).1),
       .mem (fr.rsp - 0x50) 64 ((v118615 p).2),
       .mem (fr.rsp - 0x70) 64 (v11877e p)]
  | .stage12 =>
      [.gpr 6 ((v118769 p).1),
       .gpr 2 ((v118739 p).1),
       .gpr 1 ((v1187d4 p).1),
       .gpr 9 ((v11879f p).1),
       .gpr 0 (v118701 p),
       .gpr 10 (v1187e9 p),
       .gpr 15 (17562291160714782033),
       .mem (fr.rsp - 0x48) 64 (fr.rsi),
       .mem (fr.rsp - 0x38) 64 (p.low[3]),
       .mem (fr.rsp - 0x58) 64 ((v1185e6 p).2),
       .mem (fr.rsp - 0x40) 64 (p.high[0]),
       .mem (fr.rsp - 0x60) 64 ((v118600 p).2),
       .mem (fr.rsp - 0x68) 64 ((v1185e6 p).1),
       .mem (fr.rsp - 0x50) 64 ((v118615 p).2),
       .mem (fr.rsp - 0x70) 64 (v1187b4 p)]
  | .stage13 =>
      [.gpr 6 ((v118769 p).1),
       .gpr 2 ((v118739 p).1),
       .gpr 1 ((v1187d4 p).1),
       .gpr 9 ((v11879f p).1),
       .gpr 0 (v118807 p),
       .gpr 8 ((v1187fe p).1),
       .gpr 10 (v1187e9 p),
       .gpr 15 (17562291160714782033),
       .mem (fr.rsp - 0x48) 64 (fr.rsi),
       .mem (fr.rsp - 0x38) 64 (p.low[3]),
       .mem (fr.rsp - 0x58) 64 ((v1185e6 p).2),
       .mem (fr.rsp - 0x40) 64 (p.high[0]),
       .mem (fr.rsp - 0x60) 64 ((v118600 p).2),
       .mem (fr.rsp - 0x68) 64 ((v1185e6 p).1),
       .mem (fr.rsp - 0x50) 64 ((v118615 p).2),
       .mem (fr.rsp - 0x70) 64 (v1187e9 p)]
  | .stage14 =>
      [.gpr 6 ((v118769 p).1),
       .gpr 2 (v118833 p),
       .gpr 1 ((v1187d4 p).1),
       .gpr 9 ((v11879f p).1),
       .gpr 0 ((v11882a p).1),
       .gpr 8 ((v1187fe p).1),
       .gpr 10 (v118819 p),
       .gpr 15 (17562291160714782033),
       .mem (fr.rsp - 0x48) 64 (fr.rsi),
       .mem (fr.rsp - 0x38) 64 (p.low[3]),
       .mem (fr.rsp - 0x58) 64 ((v1185e6 p).2),
       .mem (fr.rsp - 0x40) 64 (p.high[0]),
       .mem (fr.rsp - 0x60) 64 ((v118600 p).2),
       .mem (fr.rsp - 0x68) 64 ((v1185e6 p).1),
       .mem (fr.rsp - 0x50) 64 ((v118615 p).2),
       .mem (fr.rsp - 0x70) 64 (v118807 p)]
  | .stage15 =>
      [.gpr 6 (v118852 p),
       .gpr 2 ((v118849 p).1),
       .gpr 1 ((v1187d4 p).1),
       .gpr 9 ((v11879f p).1),
       .gpr 0 ((v11882a p).1),
       .gpr 8 ((v1187fe p).1),
       .gpr 10 (v118819 p),
       .gpr 15 (17562291160714782033),
       .mem (fr.rsp - 0x48) 64 (fr.rsi),
       .mem (fr.rsp - 0x38) 64 (p.low[3]),
       .mem (fr.rsp - 0x58) 64 ((v1185e6 p).2),
       .mem (fr.rsp - 0x40) 64 (p.high[0]),
       .mem (fr.rsp - 0x60) 64 ((v118600 p).2),
       .mem (fr.rsp - 0x68) 64 ((v1185e6 p).1),
       .mem (fr.rsp - 0x50) 64 ((v118615 p).2),
       .mem (fr.rsp - 0x70) 64 (v118833 p)]
  | .stage16 =>
      [.gpr 6 ((v118875 p).1),
       .gpr 2 ((v118849 p).1),
       .gpr 1 ((v1187d4 p).1),
       .gpr 9 (v11887e p),
       .gpr 0 ((v11882a p).1),
       .gpr 8 ((v1187fe p).1),
       .gpr 15 (17562291160714782033),
       .mem (fr.rsp - 0x48) 64 (fr.rsi),
       .mem (fr.rsp - 0x38) 64 (p.low[3]),
       .mem (fr.rsp - 0x58) 64 ((v1185e6 p).2),
       .mem (fr.rsp - 0x40) 64 (p.high[0]),
       .mem (fr.rsp - 0x60) 64 ((v118600 p).2),
       .mem (fr.rsp - 0x68) 64 ((v1185e6 p).1),
       .mem (fr.rsp - 0x50) 64 ((v118615 p).2),
       .mem (fr.rsp - 0x70) 64 (v118852 p)]
  | .stage17 =>
      [.gpr 6 ((v118875 p).1),
       .gpr 2 ((v118849 p).1),
       .gpr 1 (v11889d p),
       .gpr 0 ((v11882a p).1),
       .gpr 8 ((v1187fe p).1),
       .gpr 15 (17562291160714782033),
       .mem (fr.rsp - 0x48) 64 (fr.rsi),
       .mem (fr.rsp - 0x38) 64 (p.low[3]),
       .mem (fr.rsp - 0x58) 64 ((v1185e6 p).2),
       .mem (fr.rsp - 0x40) 64 (p.high[0]),
       .mem (fr.rsp - 0x60) 64 ((v118600 p).2),
       .mem (fr.rsp - 0x68) 64 ((v1185e6 p).1),
       .mem (fr.rsp - 0x50) 64 ((v118615 p).2),
       .mem (fr.rsp - 0x70) 64 (v11887e p)]
  | .stage18 =>
      [.gpr 6 ((v118875 p).1),
       .gpr 2 ((v118849 p).1),
       .gpr 1 (v1188b2 p),
       .gpr 9 (v1188af p),
       .gpr 0 ((v11882a p).1),
       .gpr 8 ((v1187fe p).1),
       .gpr 15 (v1188b5 p),
       .gpr 11 (v1188c2 p),
       .mem (fr.rsp - 0x48) 64 (fr.rsi),
       .mem (fr.rsp - 0x38) 64 (p.low[3]),
       .mem (fr.rsp - 0x58) 64 ((v1185e6 p).2),
       .mem (fr.rsp - 0x40) 64 (p.high[0]),
       .mem (fr.rsp - 0x60) 64 ((v118600 p).2),
       .mem (fr.rsp - 0x68) 64 ((v1185e6 p).1),
       .mem (fr.rsp - 0x50) 64 ((v118615 p).2),
       .mem (fr.rsp - 0x70) 64 (v11889d p)]
  | .stage19 =>
      [.gpr 2 ((v118849 p).1),
       .gpr 9 ((v1188ce p).1),
       .gpr 0 (mergeGPR 8 ((v1188df p).1) (mergeGPR 8 ((if (v1188c8 p).2.CF then 1 else 0 : BitVec 8)) ((v11882a p).1))),
       .gpr 8 ((v1188e4 p).1),
       .gpr 15 ((v1188c5 p).1),
       .gpr 11 ((v1188c8 p).1),
       .mem (fr.rsp - 0x48) 64 (fr.rsi),
       .mem (fr.rsp - 0x38) 64 (p.low[3]),
       .mem (fr.rsp - 0x58) 64 ((v1185e6 p).2),
       .mem (fr.rsp - 0x40) 64 (p.high[0]),
       .mem (fr.rsp - 0x60) 64 ((v118600 p).2),
       .mem (fr.rsp - 0x68) 64 ((v1185e6 p).1),
       .mem (fr.rsp - 0x50) 64 ((v118615 p).2),
       .mem (fr.rsp - 0x70) 64 (v11889d p)]

def dialect : Dialect Op Unit Inputs where
  eval op := nomatch op
  truth _ := false

@[refine_layout] def outputRegion (fr : Activation) : MemoryRegion := ⟨fr.rdi.toNat, 32⟩

def layout (fr : Activation) (controls : RamState) : Layout program dialect Machine.lifted Unit where
  start := start
  Params _ := Inputs
  args _ _ := #v[]
  store _ p := p
  atoms l _ p := Machine.Reduce.frameAt (start l) fr ++ commonAtoms fr controls p ++ coreAtoms l fr p
  Result := Inputs
  output p := ⟨#v[], none, p⟩
  done _ p := Machine.Reduce.doneAt fr ++
    [.words fr.rdi 64 (reducedWords p), .readable fr.rdi 32, .reg 39 ⟨32, controls.MXCSR⟩, .reg 51 ⟨16, controls.FP87_Control⟩]
  retAddr _ := fr.ret
  original _ := fr.original
  regions _ := [fr.region, outputRegion fr]

end P256.Proofs.Scalar.Multiply.Barrett
