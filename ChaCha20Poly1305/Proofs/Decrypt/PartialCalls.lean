import ChaCha20Poly1305.Proofs.Decrypt.HashCall
import ChaCha20Poly1305.Proofs.Decrypt.CallRun

namespace ChaCha20Poly1305.Proofs.Decrypt.Hash
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program
open Poly1305

@[refine_layout] def fillFrame (fr : Activation) := {push fr with
  rdi := fr.rsp + fr.r14 + 32,rsi := 0,rdx := 16-fr.r14}
@[refine_layout] def afterFill (ct : Bool) (fr : Activation) := match ct with
  | true => {fr with r13 := fr.r13+fr.r15}
  | false => {fr with rbp := fr.rsi+fr.r13}

@[refine_layout] def fill (ct : Bool) (dest num : BitVec 64) : Invoke.Edge where
  site := match ct with | true => .l1004c2 | false => .l10043a
  resume := match ct with | true => .l1004dd | false => .l10045a
  callee := fillFn
  before fr := regs fr ++ space fr 8 ++
    (match ct with | true => [.gpr 5 fr.rbp] | false => [.readable (fr.rsp+8) 8,.mem (fr.rsp+8) 64 fr.rsi]) ++
    [.readable 0x2013e0 8,.mem 0x2013e0 64 0x102d70,.fact (fr.rsp+fr.r14+32=dest),
     .fact (16-fr.r14=num)] ++ fillFn.pre (fillFrame fr)
  after fr := regs (afterFill ct fr) ++ [.gpr 5 (afterFill ct fr).rbp,.mem dest (8*num.toNat) 0]
  footprint := [⟨dest.toNat,num.toNat⟩]

set_option maxRecDepth 8000
set_option maxHeartbeats 1000000
set_option pp.maxSteps 160
theorem fillValid (ct : Bool) (dest num : BitVec 64) : (Invoke.layout (fill ct dest num)).BlockSimulation fnCode .site := by
  cases ct
  all_goals
    refine_intro
    subst dest; subst num
    refine_uir [Invoke.program]
    refine_lifted []
    refine_close []
  all_goals try assumption

@[refine_layout] def copySource (ct : Bool) (fr : Activation) := match ct with | true => fr.r13 | false => fr.rbp
@[refine_layout] def copyFrame (ct : Bool) (fr : Activation) := {push fr with
  rdi := fr.rsp+32,rsi := copySource ct fr,rdx := fr.r14}

@[refine_layout] def copy (ct : Bool) (dest num : BitVec 64) (v : BitVec (8*num.toNat)) : Invoke.Edge where
  site := match ct with | true => .l1004dd | false => .l10045a
  resume := match ct with | true => .l1004f1 | false => .l10046e
  callee := copyFn
  before fr := regs fr ++ space fr 8 ++ [.gpr 5 fr.rbp,.readable 0x2013a8 8,.mem 0x2013a8 64 0x102dc0,
    .fact (fr.rsp+32=dest),.fact (fr.r14=num),
    .fact ((copySource ct fr).toNat+num.toNat ≤ fr.rsp.toNat-8 ∨ fr.rsp.toNat ≤ (copySource ct fr).toNat),
    .mem (copySource ct fr) (8*num.toNat) v] ++ copyFn.pre (copyFrame ct fr)
  after fr := regs {fr with rbx := dest} ++ [.gpr 5 fr.rbp,.mem dest (8*num.toNat) v]
  footprint := [⟨dest.toNat,num.toNat⟩]

theorem copyValid (ct : Bool) (dest num : BitVec 64) (v : BitVec (8*num.toNat)) :
    (Invoke.layout (copy ct dest num v)).BlockSimulation fnCode .site := by
  cases ct
  all_goals
    refine_intro
    subst dest; subst num
    refine_uir [Invoke.program]
    refine_lifted []
    refine_close []
  all_goals try assumption
  all_goals rw [memLoad_memStore_of_rangeApart _ _ _ _ _ (RangeApart.of_toNat (by bv_omega) (by bv_omega) (by bv_omega))]
  all_goals assumption

@[refine_layout] def padMul (ct : Bool) (x : Mul.Input) (out : Vector (BitVec 32) 5) (ctx : BitVec 64) : Invoke.Edge where
  site := match ct with | true => .l1004f1 | false => .l10046e
  resume := match ct with | true => .l1004fc | false => .l100479
  callee := multiply x out
  before fr := regs fr ++ space fr 96 ++ [.gpr 5 fr.rbp,.fact (fr.rdi=ctx)] ++ (multiply x out).pre {push fr with rsi := fr.rbx}
  after fr := regs fr ++ [.gpr 5 fr.rbp] ++ accData fr.rdi out
  footprint := [⟨ctx.toNat+36,20⟩]

theorem padMulValid (ct : Bool) (x : Mul.Input) (out : Vector (BitVec 32) 5) (ctx : BitVec 64) :
    (Invoke.layout (padMul ct x out ctx)).BlockSimulation fnCode .site := by
  cases ct
  all_goals
    refine_intro
    subst ctx
    refine_uir [Invoke.program]
    refine_lifted []
    refine_close []
  all_goals assumption

end ChaCha20Poly1305.Proofs.Decrypt.Hash
