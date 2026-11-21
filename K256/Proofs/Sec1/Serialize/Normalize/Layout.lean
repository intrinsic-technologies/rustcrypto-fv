import K256.Proofs.Sec1.Serialize.Normalize.Program
import K256.Proofs.Sec1.LIR.Fn114930.Frame
import K256.Proofs.Sec1.LIR.Fn127d50.Frame

namespace K256.Proofs.Sec1.Serialize.Normalize

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
open K256.Proofs.Refine K256.Proofs.Common.Field Prelude

structure Ctx where
  src : Word
  dst : Word
  mxcsr : Value
  ftw : Value
  fcw : Value

@[refine_layout] def floatingRegs (c : Ctx) : List Atom :=
  [.reg 39 c.mxcsr, .reg 50 c.ftw, .reg 51 c.fcw]

structure Entry where
  dst : Word
  store : Store

structure Resume where
  r : Word
  dst : Word
  t0 : Word
  t1 : Word
  t2 : Word
  t3 : Word
  t4 : Word
  store : Store

structure Choice where
  x : Word
  store : Store

def Params : Label → Type
  | .entry => Entry
  | .resume => Resume
  | .choice => Choice

@[refine_layout] def regions (c : Ctx) (fr : Activation) (s : Store) : List Atom :=
  floatingRegs c ++ [.words c.src 64 s.1, .readable c.src 40, .words c.dst 64 s.2, .writable c.dst 40,
    .fact (c.dst.toNat % 8 = 0),
    .fact (c.dst.toNat + 40 ≤ c.src.toNat ∨ c.src.toNat + 40 ≤ c.dst.toNat),
    .fact (c.src.toNat + 40 ≤ fr.low.toNat ∨ fr.rsp.toNat + 8 ≤ c.src.toNat),
    .fact (c.dst.toNat + 40 ≤ fr.low.toNat ∨ fr.rsp.toNat + 8 ≤ c.dst.toNat),
    .fact (c.dst.toNat + 40 ≤ 0x100000 ∨ 0x12a9bf ≤ c.dst.toNat),
    .fact (fr.rsp.toNat + 8 ≤ 0x100000 ∨ 0x12a9bf ≤ fr.low.toNat)]

open K256.Proofs.Sec1.LIR in
def core : LayoutCore program dialect lifted Ctx where
  start
    | .entry => .g0 .l114930
    | .resume => .g0 .l114a10
    | .choice => .g9 .l127d50
  Params := Params
  args
    | .entry => fun p => #v[p.dst]
    | .resume => fun p => #v[p.r, p.dst, p.t0, p.t1, p.t2, p.t3, p.t4]
    | .choice => fun p => #v[p.x]
  store
    | .entry => fun p => p.store
    | .resume => fun p => p.store
    | .choice => fun p => p.store
  atoms
    | .entry => fun c fr p => [.gpr 6 c.src, .gpr 7 c.dst, .fact (p.dst = c.dst)] ++
        regions c fr p.store
    | .resume => fun c fr p =>
        [.gpr 0 p.r, .fact (p.dst = c.dst), .fact (fr.rdi = c.dst), .gpr 3 p.t2, .gpr 5 p.t3,
          .gpr 12 p.t4, .gpr 13 p.t0, .gpr 14 0x1000003d1, .gpr 15 mask52,
          .mem (fr.rsp - 0x60) 64 (p.t3 &&& mask52), .mem (fr.rsp - 0x58) 64 (p.t0 &&& mask52),
          .mem (fr.rsp - 0x50) 64 (p.t1 &&& mask52), .mem (fr.rsp - 0x48) 64 (p.t2 &&& mask52),
          .mem (fr.rsp - 0x38) 64 p.t1] ++ regions c fr p.store
    | .choice => fun c fr p => floatingRegs c ++ [.gpr 7 p.x, .words c.src 64 p.store.1, .words c.dst 64 p.store.2,
        .fact (c.src.toNat + 40 ≤ fr.low.toNat ∨ fr.rsp.toNat + 8 ≤ c.src.toNat),
        .fact (c.dst.toNat + 40 ≤ fr.low.toNat ∨ fr.rsp.toNat + 8 ≤ c.dst.toNat),
        .fact (fr.rsp.toNat + 8 ≤ 0x100000 ∨ 0x12a9bf ≤ fr.low.toNat),
        .fact (c.src.toNat + 40 ≤ 2 ^ 32), .fact (c.dst.toNat + 40 ≤ 2 ^ 32)]
  Result := Word × Store
  output r := ⟨#v[r.1], none, r.2⟩
  done c _ r := floatingRegs c ++ [.gpr 0 r.1, .words c.src 64 r.2.1, .words c.dst 64 r.2.2]
  footprint c _ := [⟨c.dst.toNat, 40⟩]

private def frameRegister : Atom → Bool
  | .reg r _ => !(r.val ∈ [1, 2, 8, 9, 39, 50, 51])
  | _ => true

def frameAt (l : LIR.Label) (fr : Activation) : List Atom :=
  (LIR.Fn114930.frameAt l fr ++ LIR.Fn127d50.frameAt l fr).filter frameRegister

def doneAt (fr : Activation) : List Atom := (LIR.Fn114930.doneAt fr).filter frameRegister

@[refine_layout] theorem frameAt_114930 (fr : Activation) : frameAt .l114930 fr =
    [.gpr 4 fr.rsp, .reg 22 ⟨1, 0⟩, .gpr 3 fr.rbx, .gpr 5 fr.rbp, .gpr 6 fr.rsi,
     .gpr 7 fr.rdi, .gpr 12 fr.r12, .gpr 13 fr.r13, .gpr 14 fr.r14, .gpr 15 fr.r15,
     .readable fr.rsp 8, .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2^32),
     .writable (fr.rsp - 0x71) 0x71, .fact (fr.low.toNat + 0x71 ≤ fr.rsp.toNat),
     .fact (fr.rsp.toNat % 16 = 8)] := rfl

@[refine_layout] theorem frameAt_114a10 (fr : Activation) : frameAt .l114a10 fr =
    [.gpr 4 (fr.rsp - 0x68), .reg 22 ⟨1, 0⟩, .mem (fr.rsp - 0x40) 64 fr.rdi,
     .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
     .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp,
     .readable fr.rsp 8, .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2^32),
     .writable (fr.rsp - 0x71) 0x71, .fact (fr.low.toNat + 0x71 ≤ fr.rsp.toNat),
     .fact (fr.rsp.toNat % 16 = 8)] := rfl

@[refine_layout] theorem frameAt_127d50 (fr : Activation) : frameAt .l127d50 fr =
    [.gpr 4 fr.rsp, .reg 22 ⟨1, 0⟩, .gpr 3 fr.rbx, .gpr 5 fr.rbp, .gpr 6 fr.rsi,
     .gpr 7 fr.rdi, .gpr 12 fr.r12, .gpr 13 fr.r13, .gpr 14 fr.r14, .gpr 15 fr.r15,
     .readable fr.rsp 8, .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2^32),
     .writable (fr.rsp - 1) 1, .fact (fr.low.toNat + 1 ≤ fr.rsp.toNat),
     .fact (fr.rsp.toNat % 16 = 8)] := rfl

@[refine_layout] theorem doneAt_eq (fr : Activation) : doneAt fr =
    [.gpr 4 (fr.rsp + 8), .reg 22 ⟨1, 0⟩, .gpr 3 fr.rbx, .gpr 5 fr.rbp,
     .gpr 12 fr.r12, .gpr 13 fr.r13, .gpr 14 fr.r14, .gpr 15 fr.r15] := rfl

def layout := Layout.withFrame frameAt doneAt core

end K256.Proofs.Sec1.Serialize.Normalize
