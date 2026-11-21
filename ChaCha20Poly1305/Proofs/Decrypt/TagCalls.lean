import ChaCha20Poly1305.Proofs.Decrypt.TagContracts
import ChaCha20Poly1305.Proofs.Decrypt.PadRun

namespace ChaCha20Poly1305.Proofs.Decrypt.Hash
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program
open Poly1305

@[refine_layout] def slot (s : BitVec 64) (i n : Nat) : MemoryRegion := ⟨(s+BitVec.ofNat 64 i).toNat,n⟩

@[refine_layout] def localArea (fr : Activation) : List Atom :=
  [.writable fr.rsp 392,.fact (fr.rsp.toNat+392 ≤ 0x1001f0 ∨ 0x102def ≤ fr.rsp.toNat)]

@[refine_layout] def lengthsCall (r w out : Vector (BitVec 32) 5) (a c sp ctx : BitVec 64) : Invoke.Edge where
  site := .l1004fc
  resume := .l100520
  callee := (lastMul r w out a c).reserve [slot sp 32 16]
  before fr := regs fr ++ [.gpr 5 fr.rbp] ++ space fr 96 ++ localArea fr ++
    [.fact (fr.rsp=sp),.fact (fr.rdi=ctx),.fact (fr.rsp.toNat+208 ≤ fr.rdi.toNat ∨ fr.rdi.toNat+56 ≤ fr.rsp.toNat),
     .mem (fr.rsp+192) 64 a,.mem (fr.rsp+24) 64 c] ++
    Mul.shared {push fr with rsi:=fr.rsp+32} ++ rData fr.rdi r ++ accData fr.rdi w
  after fr := regs fr ++ [.gpr 5 fr.rbp] ++ accData fr.rdi out
  footprint := [⟨ctx.toNat+36,20⟩,slot sp 32 16]

@[refine_layout] def finishCall (q : Vector (BitVec 64) 7) (lo hi sp : BitVec 64) : Invoke.Edge where
  site := .l100520
  resume := .l100577
  callee := (endFn q lo hi).reserve [slot sp 32 56]
  before fr := regs fr ++ [.gpr 5 fr.rbp] ++ space fr 56 ++ localArea fr ++
    [.fact (fr.rsp=sp),.readable fr.rdi 56,
     .fact (fr.rsp.toNat+176 ≤ fr.rdi.toNat ∨ fr.rdi.toNat+56 ≤ fr.rsp.toNat)] ++
    Finish.shared {push fr with rdi:=fr.rsp+160,rsi:=fr.rsp+32} ++ quad7 fr.rdi q
  after fr := regs fr ++ [.gpr 5 fr.rbp,.mem (fr.rsp+160) 64 lo,.mem (fr.rsp+168) 64 hi]
  footprint := [slot sp 160 16,slot sp 32 56]

set_option maxHeartbeats 1400000
set_option maxRecDepth 8000
set_option pp.maxSteps 140

theorem lengthsValid (r w out : Vector (BitVec 32) 5) (a c sp ctx : BitVec 64) :
    (Invoke.layout (lengthsCall r w out a c sp ctx)).BlockSimulation fnCode .site := by
  refine_intro
  subst sp; subst ctx
  refine_uir [Invoke.program]
  refine_lifted []
  refine_close []
  all_goals try first | assumption | rfl

theorem finishValid (q : Vector (BitVec 64) 7) (lo hi sp : BitVec 64) :
    (Invoke.layout (finishCall q lo hi sp)).BlockSimulation fnCode .site := by
  refine_intro
  subst sp
  refine_uir [Invoke.program]
  refine_lifted []
  refine_close []
  all_goals try first | assumption | rfl
  rw [BitVec.add_assoc] at done12
  exact done12

end ChaCha20Poly1305.Proofs.Decrypt.Hash
