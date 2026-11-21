import P256.Proofs.Verifying.Core.Inverse.Model
import P256.Proofs.Verifying.Core.Inverse.SafeGcd.Machine
import P256.Proofs.Verifying.Core.Inverse.SafeGcd.Machine.Core.Frame
import P256.Proofs.Field.Inverse.SafeGcd.Core.Support

namespace P256.Proofs.Verifying.Core.Inverse.SafeGcd

open P256.Proofs.Field.Inverse.SafeGcd
open P256.Proofs.Field.Inverse.SafeGcd.Core.Shared

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

def outputRegion (fr : Activation) : MemoryRegion := ⟨fr.rdi.toNat, 33⟩

@[refine_layout] def outputAtoms (fr : Activation) : List Atom :=
  [.writable fr.rdi 33,
   .fact (fr.rdi.toNat + 33 ≤ fr.low.toNat ∨ fr.rsp.toNat + 8 ≤ fr.rdi.toNat)]

@[refine_layout] def inputAtoms (fr : Activation) (p : Inputs) : List Atom :=
  [.words fr.rsi 64 p.a, .words fr.rdx 64 p.modulus, .words fr.r8 64 p.scale,
   .readable fr.rsi 32, .readable fr.rdx 32, .readable fr.r8 32,
   .fact (fr.rsi.toNat + 32 ≤ fr.low.toNat ∨ fr.rsp.toNat ≤ fr.rsi.toNat),
   .fact (fr.rdx.toNat + 32 ≤ fr.low.toNat ∨ fr.rsp.toNat ≤ fr.rdx.toNat),
   .fact (fr.r8.toNat + 32 ≤ fr.low.toNat ∨ fr.rsp.toNat ≤ fr.r8.toNat),
   .fact (fr.rcx = p.inverse)]

@[refine_layout] def commonAtoms (fr : Activation) (p : Inputs) : List Atom :=
  outputAtoms fr ++ inputAtoms fr p

@[refine_layout] def frameAtoms (fr : Activation) (controls : RamState) : List Atom :=
  [.gpr 4 (fr.rsp - 0x188), .reg 22 ⟨1, 0⟩,
   .mem (fr.rsp - 8) 64 fr.rbp, .mem (fr.rsp - 16) 64 fr.r15,
   .mem (fr.rsp - 24) 64 fr.r14, .mem (fr.rsp - 32) 64 fr.r13,
   .mem (fr.rsp - 40) 64 fr.r12, .mem (fr.rsp - 48) 64 fr.rbx,
   .mem fr.rsp 64 fr.ret, .readable fr.rsp 8, .fact (fr.ret.toNat < 2^32),
   .writable (fr.rsp - 0x2c0) 0x2c0, .fact (fr.low.toNat + 0x2c0 ≤ fr.rsp.toNat),
   .fact (fr.rsp.toNat % 16 = 8),
   .mem (fr.rsp - 0x130) 64 fr.rdx, .mem (fr.rsp - 0x68) 64 fr.rdi,
   .mem (fr.rsp - 0x60) 64 fr.rcx,
   .reg 39 ⟨32, controls.MXCSR⟩, .reg 51 ⟨16, controls.FP87_Control⟩]

@[refine_layout] def savedInputAtoms (fr : Activation) (p : Inputs) : List Atom :=
  [.mem (fr.rsp - 0x80) 64 p.a[0], .mem (fr.rsp - 0x70) 64 p.a[1],
   .mem (fr.rsp - 0x88) 64 p.a[2], .mem (fr.rsp - 0x78) 64 p.a[3]]

@[refine_layout] def signedAtoms (address : BitVec 64) (s : SignedWords) : List Atom :=
  [.words address 64 s.words, .mem (address + 32) 8 s.sign]

@[refine_layout] def stateAtoms (fr : Activation) (s : LoopState) : List Atom :=
  signedAtoms (fr.rsp - 0x180) s.f ++ signedAtoms (fr.rsp - 0x158) s.g ++
  signedAtoms (fr.rsp - 0x128) s.d ++ signedAtoms (fr.rsp - 0x100) s.e

@[refine_layout] def loopAtoms (fr : Activation) (controls : RamState) (p : Inputs) (s : LoopState) : List Atom :=
  frameAtoms fr controls ++ commonAtoms fr p ++ savedInputAtoms fr p ++ stateAtoms fr s ++
  [.gpr 12 s.delta, .gpr 6 (BitVec.ofNat 64 s.remaining)]

macro "core_stack_store" fr:ident mem:ident hc:ident : tactic =>
  `(tactic| first
    | (apply Correction.Execution.CrossPage.StoreOk.of_region (b := ($fr).rsp - 0x2c0) (len := 0x2c0)
       · repeat' first | assumption | apply Writable.memStore
       · refine_arith
       · refine_arith
       · apply Correction.Execution.writable_codeApart (mem := $mem) _ $hc (by decide) (by decide)
         apply Writable.sub (b := ($fr).rsp - 0x2c0) (len := 0x2c0)
         · repeat' first | assumption | apply Writable.memStore
         · refine_arith
         · refine_arith)
    | (apply StoreOk.of_region (b := ($fr).rsp - 0x2c0) (len := 0x2c0)
       · repeat' first | assumption | apply Writable.memStore
       · refine_arith
       · refine_arith
       · apply Correction.Execution.writable_codeApart (mem := $mem) _ $hc (by decide) (by decide)
         apply Writable.sub (b := ($fr).rsp - 0x2c0) (len := 0x2c0)
         · repeat' first | assumption | apply Writable.memStore
         · refine_arith
         · refine_arith))

end P256.Proofs.Verifying.Core.Inverse.SafeGcd
