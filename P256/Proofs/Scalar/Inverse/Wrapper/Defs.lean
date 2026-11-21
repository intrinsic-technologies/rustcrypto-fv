import P256.Proofs.Scalar.Inverse.Wrapper.Machine
import P256.Proofs.Scalar.Inverse.Wrapper.Machine.Inverse.Frame
import P256.Proofs.Scalar.Inverse.SafeGcd
import P256.Proofs.Field.Inverse.SafeGcd.Core.Support

namespace P256.Proofs.Scalar.Inverse.Wrapper

open P256.Proofs.Field.Inverse.SafeGcd
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

structure Inputs where
  a : Vector (BitVec 64) 4
  mxcsr : BitVec 32
  fcw : BitVec 16

def scalarInput (p : Inputs) : Core.Inputs :=
  ⟨p.a, #v[0xf3b9cac2fc632551, 0xbce6faada7179e84, 0xffffffffffffffff, 0xffffffff00000000],
    #v[1, 0, 0, 0], 0x332e375511ff43b1⟩

def resultWords (a : Inputs) := Core.resultWords (scalarInput a)

def resultChoice (a : Inputs) := Core.resultChoice (scalarInput a)

def outputRegion (fr : Activation) : MemoryRegion := ⟨fr.rdi.toNat, 33⟩

@[refine_layout] def frameAtoms (fr : Activation) (p : Inputs) (sp : BitVec 64) : List Atom :=
  [.gpr 4 sp, .reg 22 ⟨1, 0⟩, .gpr 3 fr.rdi, .gpr 5 fr.rbp,
   .gpr 12 fr.r12, .gpr 13 fr.r13, .gpr 14 fr.r14, .gpr 15 fr.r15,
   .mem (fr.rsp - 8) 64 fr.rbx, .mem fr.rsp 64 fr.ret,
   .readable fr.rsp 8, .fact (fr.ret.toNat < 2^32),
   .writable (fr.rsp - 0x300) 0x300, .fact (fr.low.toNat + 0x300 ≤ fr.rsp.toNat),
   .fact (fr.rsp.toNat % 16 = 8),
   .reg 39 ⟨32, p.mxcsr⟩, .reg 51 ⟨16, p.fcw⟩]

@[refine_layout] def outputAtoms (fr : Activation) : List Atom :=
  [.writable fr.rdi 33,
   .fact (fr.rdi.toNat + 33 ≤ fr.low.toNat ∨ fr.rsp.toNat + 8 ≤ fr.rdi.toNat)]

@[refine_layout] def inputAtoms (fr : Activation) (p : Inputs) : List Atom :=
  [.words fr.rsi 64 p.a, .readable fr.rsi 32,
   .fact (fr.rsi.toNat + 32 ≤ fr.low.toNat ∨ fr.rsp.toNat ≤ fr.rsi.toNat),
   .words 0x2025e0 64 (scalarInput p).modulus,
   .words 0x2025c0 64 (scalarInput p).scale,
   .readable 0x2025e0 32, .readable 0x2025c0 32,
   .fact (0x202600 ≤ fr.low.toNat ∨ fr.rsp.toNat ≤ 0x2025e0),
   .fact (0x2025e0 ≤ fr.low.toNat ∨ fr.rsp.toNat ≤ 0x2025c0)]

@[refine_layout] def entryAtoms (fr : Activation) (p : Inputs) : List Atom :=
  Machine.Inverse.frameAt .l118910 fr ++ outputAtoms fr ++ inputAtoms fr p ++
  [.reg 39 ⟨32, p.mxcsr⟩, .reg 51 ⟨16, p.fcw⟩]

@[refine_layout] def coreCall (fr : Activation) (p : Inputs) : List Atom :=
  frameAtoms fr p (fr.rsp - 0x40) ++ outputAtoms fr ++ inputAtoms fr p ++
  [.gpr 7 (fr.rsp - 0x30), .gpr 6 fr.rsi, .gpr 2 0x2025e0,
   .gpr 1 0x332e375511ff43b1, .gpr 8 0x2025c0,
   .mem (fr.rsp - 0x40) 64 0x112e5a, .readable (fr.rsp - 0x40) 8]

@[refine_layout] def coreReturned (fr : Activation) (p : Inputs) : List Atom :=
  frameAtoms fr p (fr.rsp - 0x38) ++ outputAtoms fr ++
  [.words (fr.rsp - 0x30) 64 (resultWords p),
   .mem (fr.rsp - 0x10) 8 (resultChoice p), .readable (fr.rsp - 0x30) 33]

@[refine_layout] def choiceCall (fr : Activation) (p : Inputs) : List Atom :=
  frameAtoms fr p (fr.rsp - 0x40) ++ outputAtoms fr ++
  [.words fr.rdi 64 (resultWords p), .readable fr.rdi 32, .low 7 8 (resultChoice p),
   .mem (fr.rsp - 0x40) 64 0x112e86, .readable (fr.rsp - 0x40) 8]

@[refine_layout] def choiceReturned (fr : Activation) (p : Inputs) : List Atom :=
  frameAtoms fr p (fr.rsp - 0x38) ++ outputAtoms fr ++
  [.words fr.rdi 64 (resultWords p), .readable fr.rdi 32, .gpr 0 ((resultChoice p).setWidth 64)]

inductive Label where | entry | core | middle | choice | finish

def program : Program Core.Support.Op Label (fun _ => 0) 0 where
  blocks
  | .entry => .terminate (.call ⟨.core, #v[]⟩ {target := .middle, kept := #v[], arity := rfl})
  | .middle => .terminate (.call ⟨.choice, #v[]⟩ {target := .finish, kept := #v[], arity := rfl})
  | _ => .terminate (.ret #v[])

def dialect : Dialect Core.Support.Op Unit Inputs where
  eval op := nomatch op
  truth _ := false

@[refine_layout] def start : Label → Machine.Label
  | .entry => .l118910 | .core => .l117650 | .middle => .l11893a
  | .choice => .l126f60 | .finish => .l118966

def layout (fr : Activation) : Layout program dialect Machine.lifted Unit where
  start := start
  Params _ := Inputs
  args _ _ := #v[]
  store _ p := p
  atoms l _ p := match l with
    | .entry => entryAtoms fr p | .core => coreCall fr p
    | .middle => coreReturned fr p | .choice => choiceCall fr p | .finish => []
  Result := Empty
  output r := nomatch r
  done _ r := nomatch r
  retAddr _ := fr.ret
  original _ := fr.original
  regions _ := [fr.region, outputRegion fr]

macro "wrapper_store" fr:ident mem:ident hc:ident : tactic =>
  `(tactic| first
    | (apply Correction.Execution.CrossPage.StoreOk.of_region (b := ($fr).rsp - 0x300) (len := 0x300)
       · repeat' first | assumption | apply Writable.memStore
       · refine_arith
       · refine_arith
       · apply Correction.Execution.writable_codeApart (mem := $mem) _ $hc (by decide) (by decide)
         apply Writable.sub (b := ($fr).rsp - 0x300) (len := 0x300)
         · repeat' first | assumption | apply Writable.memStore
         · refine_arith
         · refine_arith)
    | (apply StoreOk.of_region (b := ($fr).rsp - 0x300) (len := 0x300)
       · repeat' first | assumption | apply Writable.memStore
       · refine_arith
       · refine_arith
       · apply Correction.Execution.writable_codeApart (mem := $mem) _ $hc (by decide) (by decide)
         apply Writable.sub (b := ($fr).rsp - 0x300) (len := 0x300)
         · repeat' first | assumption | apply Writable.memStore
         · refine_arith
         · refine_arith))

end P256.Proofs.Scalar.Inverse.Wrapper
