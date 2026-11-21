import P256.Proofs.Signing.Core.Iteration.Components.BinaryCall
import P256.Proofs.Signing.Core.Iteration.Components.Callees
import P256.Proofs.Verifying.Core.Products.Correct

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Components

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open SecretKeyFromBytes.Scalar (Nat256At)

def add_callSite : FieldCall.BinaryCallSite 4584 2280 0x113310 64 :=
  ⟨0xd2d0,0x603b,by decide,by decide +kernel,by decide +kernel,by decide,
    inProgram_of_textOffset 0x13310 (by decide),
    ⟨2288,984,1752,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩,
    rfl,by decide,952,by decide,by decide,by decide⟩

theorem add_call [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x y : Nat}
    (add : AddContract) (hx : x < Operations.domain.n) (hy : y < Operations.domain.n)
    (hp : SignPre s boundary) (frame : Frame s t) (rip : t.RIP = 0x10d2d0)
    (source : t.regValue .rsi = frameBase s+1296)
    (right : t.regValue .rdx = frameBase s+1328)
    (destination : t.regValue .rdi = frameBase s+528)
    (first : Nat256At t (frameBase s+1296) x) (second : Nat256At t (frameBase s+1328) y) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x10d2d5 ∧
      Nat256At u (frameBase s+528) ((x+y) % Operations.domain.n) ∧
      (∀ offset < 2280, offset < 528 ∨ 560 ≤ offset →
        u.external[frameBase s+BitVec.ofNat 64 offset]? =
          t.external[frameBase s+BitVec.ofNat 64 offset]?) ∧
      (∀ reg ∈ [Syntax.Reg.rbx,.rbp,.r12,.r13,.r14,.r15],
        u.regValue reg = t.regValue reg) := by
  have leftAddress : frameBase s+1296 = stackPtr s-984 := NextNonce.base_add s (by decide)
  have rightAddress : frameBase s+1328 = stackPtr s-952 := NextNonce.base_add s (by decide)
  have outputAddress : frameBase s+528 = stackPtr s-1752 := NextNonce.base_add s (by decide)
  obtain ⟨n,u,run,frameU,ripU,value,regs,memory,_⟩ := binary_nat_call (x := x) (y := y) (op := fun a b => (a+b)%Operations.domain.n) hp frame add_callSite
    (fun _ cp a b => add cp a b hx hy) rip
    (source.trans leftAddress) (right.trans rightAddress) (destination.trans outputAddress)
    (leftAddress ▸ first) (rightAddress ▸ second)
  refine ⟨n,u,run,frameU,ripU,outputAddress ▸ value,?_,regs⟩
  intro offset bound apart
  have h := memory (2280-offset) 1 (by omega) (by omega) (by
    change (2280-offset)+32 ≤ 1752 ∨ 1752+1 ≤ 2280-offset
    omega) 0 (by decide)
  have address := NextNonce.base_add s (offset := offset) (by omega)
  simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_zero,← address] using h

def inverse_productSite : FieldCall.BinaryCallSite 4584 2280 0x113320 280 :=
  ⟨0xd2eb,0x6030,by decide,by decide +kernel,by decide +kernel,by decide,
    inProgram_of_textOffset 0x13320 (by decide),
    ⟨2288,1944,184,by decide,by decide,by decide,by decide,by decide,by decide,by decide⟩,
    rfl,by decide,1752,by decide,by decide,by decide⟩

theorem inverse_product [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x y : Nat}
    (hp : SignPre s boundary) (frame : Frame s t) (rip : t.RIP = 0x10d2eb)
    (source : t.regValue .rsi = frameBase s+336)
    (right : t.regValue .rdx = frameBase s+528)
    (destination : t.regValue .rdi = frameBase s+2096)
    (first : Nat256At t (frameBase s+336) x) (second : Nat256At t (frameBase s+528) y) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x10d2f0 ∧
      Nat256At u (frameBase s+2096) ((x*y) % Operations.domain.n) ∧
      (∀ offset < 2280, offset < 2096 ∨ 2128 ≤ offset →
        u.external[frameBase s+BitVec.ofNat 64 offset]? =
          t.external[frameBase s+BitVec.ofNat 64 offset]?) ∧
      (∀ reg ∈ [Syntax.Reg.rbx,.rbp,.r12,.r13,.r14,.r15],
        u.regValue reg = t.regValue reg) := by
  have leftAddress : frameBase s+336 = stackPtr s-1944 := NextNonce.base_add s (by decide)
  have rightAddress : frameBase s+528 = stackPtr s-1752 := NextNonce.base_add s (by decide)
  have outputAddress : frameBase s+2096 = stackPtr s-184 := NextNonce.base_add s (by decide)
  obtain ⟨n,u,run,frameU,ripU,value,regs,memory,_⟩ := binary_nat_call (x := x) (y := y) (op := fun a b => (a*b)%Operations.domain.n) hp frame inverse_productSite
    (fun _ cp a b => Verifying.Core.Products.multiply_correct cp a b) rip
    (source.trans leftAddress) (right.trans rightAddress) (destination.trans outputAddress)
    (leftAddress ▸ first) (rightAddress ▸ second)
  refine ⟨n,u,run,frameU,ripU,outputAddress ▸ value,?_,regs⟩
  intro offset bound apart
  have h := memory (2280-offset) 1 (by omega) (by omega) (by
    change (2280-offset)+32 ≤ 184 ∨ 184+1 ≤ 2280-offset
    omega) 0 (by decide)
  have address := NextNonce.base_add s (offset := offset) (by omega)
  simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_zero,← address] using h

end P256.Proofs.Signing.Core.Iteration.Components
