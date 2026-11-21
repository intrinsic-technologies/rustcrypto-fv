import ChaCha20Poly1305.Proofs.Decrypt.LeafContracts
import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Fn1001f0.Part1
import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Fn1001f0.Part2

namespace ChaCha20Poly1305.Proofs.Decrypt.Hash
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program
open Poly1305

@[refine_layout] def regs (fr : Activation) : List Atom :=
  [.gpr 4 fr.rsp,.reg 22 ⟨1,0⟩,.reg 39 ⟨32,fr.mxcsr⟩,.reg 50 ⟨16,fr.ftw⟩,.reg 51 ⟨16,fr.fcw⟩,
   .gpr 3 fr.rbx,.gpr 12 fr.rdi,.gpr 13 fr.r13,.gpr 14 fr.r14,.gpr 15 fr.r15]

@[refine_layout] def space (fr : Activation) (n : Nat) : List Atom :=
  [.writable (fr.rsp-BitVec.ofNat 64 n) n,.fact (fr.low.toNat+n ≤ fr.rsp.toNat),
   .fact (fr.rsp.toNat%16=0),.fact (fr.rsp.toNat ≤ 0x1001f0 ∨ 0x102e00+n ≤ fr.rsp.toNat)]

@[refine_layout] def push (fr : Activation) := {fr with rsp := fr.rsp-8}

@[refine_layout] def rData (p : BitVec 64) (r : Vector (BitVec 32) 5) : List Atom :=
  [.mem (p+16) 32 r[0],.mem (p+20) 32 r[1],.mem (p+24) 32 r[2],.mem (p+28) 32 r[3],.mem (p+32) 32 r[4]]
@[refine_layout] def accData (p : BitVec 64) (r : Vector (BitVec 32) 5) : List Atom :=
  [.mem (p+36) 32 r[0],.mem (p+40) 32 r[1],.mem (p+44) 32 r[2],.mem (p+48) 32 r[3],.mem (p+52) 32 r[4]]
@[refine_layout] def data128 (p : BitVec 64) (b : BitVec 128) : List Atom :=
  [.mem p 32 (b.extractLsb' 0 32),.mem (p+3) 32 (b.extractLsb' 24 32),
   .mem (p+6) 32 (b.extractLsb' 48 32),.mem (p+9) 32 (b.extractLsb' 72 32),.mem (p+12) 32 (b.extractLsb' 96 32)]

@[refine_layout] def multiply (x : Mul.Input) (out : Vector (BitVec 32) 5) : Callee where
  entry := .l101e30
  abi := Fn101e30.active .l101e30
  pre fr := Mul.shared fr ++ (rData fr.rdi x.r ++ accData fr.rdi x.acc ++ data128 fr.rsi x.block)
  post fr := accData fr.rdi out
  writes fr := [⟨fr.rdi.toNat+36,20⟩]

theorem multiplyCorrect (x : Mul.Input) : (multiply x (Mul.output x)).Correct := mulFnCorrect x

@[refine_layout] def call (ct : Bool) (x : Mul.Input) (out : Vector (BitVec 32) 5) (ctx : BitVec 64) : Invoke.Edge where
  site := match ct with | true => .l1004a0 | false => .l100420
  resume := match ct with | true => .l1004ac | false => .l10042c
  callee := multiply x out
  before fr := regs fr ++ space fr 96 ++ [.gpr 6 fr.rsi,.fact (fr.rdi=ctx)] ++ (multiply x out).pre (push fr)
  after fr := regs fr ++ [.gpr 5 (fr.rsi+16)] ++ (multiply x out).post fr
  footprint := [⟨ctx.toNat+36,20⟩]

set_option maxRecDepth 9000
set_option maxHeartbeats 900000
set_option pp.maxSteps 140

theorem callValid (ct : Bool) (x : Mul.Input) (out : Vector (BitVec 32) 5) (ctx : BitVec 64) :
    (Invoke.layout (call ct x out ctx)).BlockSimulation fnCode .site := by
  cases ct
  all_goals
    refine_intro
    subst ctx
    refine_uir [Invoke.program]
    refine_lifted []
    refine_close []
  all_goals assumption

end ChaCha20Poly1305.Proofs.Decrypt.Hash
