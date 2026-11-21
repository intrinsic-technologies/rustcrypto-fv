import P256.Proofs.Field.Inverse.SafeGcd.Core.Arithmetic.LinearShift.Model
import P256.Proofs.Field.Inverse.SafeGcd.Core.LinearShift.Machine
import P256.Proofs.Field.Inverse.SafeGcd.Core.LinearShift.Machine.Shift.Frame
import P256.Proofs.Field.Inverse.SafeGcd.Core.Support

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.LinearShift

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

def outputRegion (fr : Activation) : MemoryRegion := ⟨fr.rdi.toNat, 33⟩

@[refine_layout] def bounds (p : Inputs) : List Atom :=
  [.fact (1 ≤ p.shift.toNat), .fact (p.shift.toNat < 64)]

@[refine_layout] def frameAtoms (fr : Activation) (sp : BitVec 64) (p : Inputs) : List Atom :=
  [.gpr 4 sp, .reg 22 ⟨1, 0⟩, .gpr 3 fr.rdi, .gpr 5 (p.shift.setWidth 64),
   .gpr 12 fr.r12, .gpr 13 fr.r13, .gpr 14 fr.r14, .gpr 15 fr.r15,
   .mem (fr.rsp - 8) 64 fr.rbp, .mem (fr.rsp - 16) 64 fr.r14,
   .mem (fr.rsp - 24) 64 fr.rbx, .mem fr.rsp 64 fr.ret,
   .readable fr.rsp 8, .fact (fr.ret.toNat < 2^32),
   .writable (fr.rsp - 0xc0) 0xc0, .fact (fr.low.toNat + 0xc0 ≤ fr.rsp.toNat),
   .fact (fr.rsp.toNat % 16 = 8)] ++ bounds p

@[refine_layout] def outputAtoms (fr : Activation) (controls : RamState) : List Atom :=
  [.reg 39 ⟨32, controls.MXCSR⟩, .reg 51 ⟨16, controls.FP87_Control⟩,
   .writable fr.rdi 33,
   .fact (fr.rdi.toNat + 33 ≤ fr.low.toNat ∨ fr.rsp.toNat + 8 ≤ fr.rdi.toNat)]

@[refine_layout] def inputAtoms (fr : Activation) (p : Inputs) : List Atom :=
  [.words fr.rsi 64 p.linear.a, .words fr.rdx 64 p.linear.b,
   .mem (fr.rsi + 32) 8 p.linear.aSign, .mem (fr.rdx + 32) 8 p.linear.bSign,
   .readable fr.rsi 33, .readable fr.rdx 33,
   .fact (fr.rsi.toNat + 33 ≤ fr.low.toNat ∨ fr.rsp.toNat ≤ fr.rsi.toNat),
   .fact (fr.rdx.toNat + 33 ≤ fr.low.toNat ∨ fr.rsp.toNat ≤ fr.rdx.toNat),
   .fact (fr.rcx = p.linear.u), .fact (fr.r8 = p.linear.v)]

@[refine_layout] def entryAtoms (fr : Activation) (controls : RamState) (p : Inputs) : List Atom :=
  Machine.Shift.frameAt .l1170b0 fr ++ outputAtoms fr controls ++ inputAtoms fr p ++
    bounds p ++ [.fact (fr.r9.setWidth 32 = p.shift)]

@[refine_layout] def linearCall (fr : Activation) (controls : RamState) (p : Inputs) : List Atom :=
  frameAtoms fr (fr.rsp - 0x50) p ++ outputAtoms fr controls ++ inputAtoms fr p ++
  [.gpr 7 (fr.rsp - 0x48), .gpr 6 fr.rsi, .gpr 2 fr.rdx, .gpr 1 fr.rcx, .gpr 8 fr.r8,
   .mem (fr.rsp - 0x50) 64 0x1115e6, .readable (fr.rsp - 0x50) 8]

@[refine_layout] def linearReturned (fr : Activation) (controls : RamState) (p : Inputs) : List Atom :=
  frameAtoms fr (fr.rsp - 0x48) p ++ outputAtoms fr controls ++
  [.words (fr.rsp - 0x48) 64 (LinearCombination.resultWords p.linear),
   .mem (fr.rsp - 0x20) 8 (resultSign p), .readable (fr.rsp - 0x48) 41]

inductive Label where | entry | linear | finish

def program : Program Support.Op Label (fun _ => 0) 0 where
  blocks
  | .entry => .terminate (.call ⟨.linear, #v[]⟩ {target := .finish, kept := #v[], arity := rfl})
  | _ => .terminate (.ret #v[])

def dialect : Dialect Support.Op Unit Inputs where
  eval op := nomatch op
  truth _ := false

@[refine_layout] def start : Label → Machine.Label
  | .entry => .l1170b0 | .linear => .l116d00 | .finish => .l1170c6

def layout (fr : Activation) (controls : RamState) : Layout program dialect Machine.lifted Unit where
  start := start
  Params _ := Inputs
  args _ _ := #v[]
  store _ p := p
  atoms l _ p := match l with
    | .entry => entryAtoms fr controls p | .linear => linearCall fr controls p | .finish => []
  Result := Empty
  output r := nomatch r
  done _ r := nomatch r
  retAddr _ := fr.ret
  original _ := fr.original
  regions _ := [fr.region, outputRegion fr]

macro "shift_stack_store" fr:ident mem:ident hc:ident : tactic =>
  `(tactic| first
    | (apply P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StoreOk.of_region (b := ($fr).rsp - 0xc0) (len := 0xc0)
       · repeat' first | assumption | apply Writable.memStore
       · refine_arith
       · refine_arith
       · apply P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.writable_codeApart (mem := $mem) _ $hc (by decide) (by decide)
         apply Writable.sub (b := ($fr).rsp - 0xc0) (len := 0xc0)
         · repeat' first | assumption | apply Writable.memStore
         · refine_arith
         · refine_arith)
    | (apply StoreOk.of_region (b := ($fr).rsp - 0xc0) (len := 0xc0)
       · repeat' first | assumption | apply Writable.memStore
       · refine_arith
       · refine_arith
       · apply P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.writable_codeApart (mem := $mem) _ $hc (by decide) (by decide)
         apply Writable.sub (b := ($fr).rsp - 0xc0) (len := 0xc0)
         · repeat' first | assumption | apply Writable.memStore
         · refine_arith
         · refine_arith))

end P256.Proofs.Field.Inverse.SafeGcd.Core.LinearShift
