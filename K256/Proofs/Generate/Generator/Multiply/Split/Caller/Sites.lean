import K256.Proofs.Generate.Generator.Multiply.Split.Contract
import K256.Proofs.Generate.Generator.Sample.Decide.Nonzero.Resume.Flag

namespace K256.Proofs.Generate.Generator.Multiply.Split.Caller

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR
  Standards.SECG.DomainParameters.Secp256k1

inductive Site where
  | roundFirst | mulFirst | roundSecond | mulSecond | addSecond | mulLambda | addFirst
  deriving DecidableEq

def Site.pc : Site → Label
  | .roundFirst => .l11c920
  | .mulFirst => .l11c95d
  | .roundSecond => .l11c977
  | .mulSecond => .l11c989
  | .addSecond => .l11c9a3
  | .mulLambda => .l11c9c0
  | .addFirst => .l11c9d2

def Site.callee : Site → Label
  | .roundFirst => .l11b8f0
  | .mulFirst => .l1099c0
  | .roundSecond => .l11b8f0
  | .mulSecond => .l1099c0
  | .addSecond => .l1109b0
  | .mulLambda => .l1099c0
  | .addFirst => .l1109b0

def Site.resume : Site → Label
  | .roundFirst => .l11c95d
  | .mulFirst => .l11c977
  | .roundSecond => .l11c989
  | .mulSecond => .l11c9a3
  | .addSecond => .l11c9c0
  | .mulLambda => .l11c9d2
  | .addFirst => .l11c9e7

def Site.ret : Site → BitVec 64
  | .roundFirst => 0x11c95d
  | .mulFirst => 0x11c977
  | .roundSecond => 0x11c989
  | .mulSecond => 0x11c9a3
  | .addSecond => 0x11c9c0
  | .mulLambda => 0x11c9d2
  | .addFirst => 0x11c9e7

def Site.window : Site → Nat
  | .roundFirst => 0xe0
  | .mulFirst => 0x141
  | .roundSecond => 0xe0
  | .mulSecond => 0x141
  | .addSecond => 0x40
  | .mulLambda => 0x141
  | .addFirst => 0x40


abbrev sp (fr : Activation) := fr.rsp - 0xcb8

def Site.child (k : Site) (fr : Activation) (a : Registers) : Activation :=
  let base := sp fr
  { fr with
    rsp := base - 8
    low := fr.low
    ret := k.ret
    rbx := if k = .roundFirst then fr.rbx else base + 0xc10
    rbp := fr.rsi + 120
    r12 := base + 0x128
    r13 := match k with
      | .roundFirst | .mulFirst | .roundSecond => fr.r13
      | _ => base + 0x328
    r14 := match k with
      | .addSecond | .mulLambda | .addFirst => base + 0x418
      | _ => 0
    r15 := base + 0x1d0
    rcx := match k with
      | .roundFirst => fr.rsi
      | .addSecond | .addFirst => 0x2021a0
      | _ => a[1].get 64
    r8 := a[8].get 64
    r9 := a[9].get 64
    rdi := match k with
      | .roundFirst | .roundSecond | .mulLambda => base + 0x128
      | .mulFirst => base + 0xc10
      | .mulSecond => base + 0x328
      | .addSecond => base + 0x418
      | .addFirst => base + 0x1d0
    rsi := match k with
      | .roundFirst | .roundSecond | .addFirst => fr.rsi + 120
      | .mulFirst | .mulSecond => base + 0x128
      | .addSecond => base + 0xc10
      | .mulLambda => base + 0x418
    rdx := match k with
      | .roundFirst => 0x202200
      | .mulFirst => 0x202220
      | .roundSecond => 0x202240
      | .mulSecond => 0x202260
      | .addSecond => base + 0x328
      | .mulLambda => 0x202280
      | .addFirst => base + 0x128 }

abbrev Site.returned (k : Site) (fr : Activation) (a : Registers) (b : Registers) (m : Ram) :=
  Atom.All Extracted.programImage b m (Fn1109b0.doneAt (k.child fr a))

def CallRegisters (fr : Activation) (a : Registers) : Prop :=
  a[4] = ⟨64, fr.rsp⟩ ∧ a[22] = ⟨1, 0⟩ ∧ a[1] = ⟨64, fr.rcx⟩ ∧
  a[2] = ⟨64, fr.rdx⟩ ∧ a[3] = ⟨64, fr.rbx⟩ ∧ a[5] = ⟨64, fr.rbp⟩ ∧
  a[6] = ⟨64, fr.rsi⟩ ∧ a[7] = ⟨64, fr.rdi⟩ ∧ a[8] = ⟨64, fr.r8⟩ ∧
  a[9] = ⟨64, fr.r9⟩ ∧ a[12] = ⟨64, fr.r12⟩ ∧ a[13] = ⟨64, fr.r13⟩ ∧
  a[14] = ⟨64, fr.r14⟩ ∧ a[15] = ⟨64, fr.r15⟩ ∧ a[39] = ⟨32, fr.mxcsr⟩ ∧
  a[50] = ⟨16, fr.ftw⟩ ∧ a[51] = ⟨16, fr.fcw⟩

def locals (fr : Activation) : List (BitVec 64 × BitVec 64) :=
  [(0x8,0),(0x38,fr.rsi),(0x60,66),(0x68,152),(0x88,152),(0xb0,fr.rsi),
   (0xc0,0),(0xd8,fr.rcx),(0xf0,fr.r9),(0x100,1),(0x1a0,1),(0x1c0,fr.rcx),(0x248,fr.rdi)]

def savedSlots (fr : Activation) : List (BitVec 64 × BitVec 64) :=
  [(0xc88,fr.rbx),(0xc90,fr.r12),(0xc98,fr.r13),(0xca0,fr.r14),(0xca8,fr.r15),(0xcb0,fr.rbp)]

def LocalsAt (fr : Activation) (m : Ram) :=
  ∀ kv ∈ locals fr ++ savedSlots fr, memLoad m (sp fr + kv.1) 64 = kv.2

end K256.Proofs.Generate.Generator.Multiply.Split.Caller
