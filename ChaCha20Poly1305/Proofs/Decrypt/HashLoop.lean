import ChaCha20Poly1305.Proofs.Decrypt.HashCall
import ChaCha20Poly1305.Proofs.Decrypt.CallRun
import ChaCha20Poly1305.Proofs.Decrypt.JoinTactic

namespace ChaCha20Poly1305.Proofs.Decrypt.Hash
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program
open Poly1305

@[refine_layout] def site : Bool → Lifted.Label | false => .l100420 | true => .l1004a0
@[refine_layout] def resume : Bool → Lifted.Label | false => .l10042c | true => .l1004ac
@[refine_layout] def finish : Bool → Lifted.Label | false => .l100435 | true => .l1004b5

@[refine_layout] def next (fr : Activation) := {fr with rbx := fr.rbx-16,rsi := fr.rsi+16}

@[refine_layout] def again (ct more : Bool) (fr : Activation) : Micro.Step where
  entry := resume ct
  exit := match more with | true => site ct | false => finish ct
  pre := regs fr ++ [.gpr 5 (fr.rsi+16)]
  post := regs (next fr) ++ [.gpr 6 (fr.rsi+16)]
  writes := []

set_option maxHeartbeats 600000
set_option maxRecDepth 6000
set_option pp.maxSteps 140

theorem againValid (ct more : Bool) (fr : Activation) (h : (fr.rbx≠16) ↔ more=true) :
    Micro.Valid (again ct more fr) := by
  cases ct <;> cases more <;> simp at h
  all_goals unfold Micro.Valid
  all_goals refine_one [Micro.program,again]
  all_goals try rfl
  all_goals try assumption
  all_goals exfalso
  all_goals first
    | (rw [h] at hc; exact Bool.noConfusion hc)
    | (have nz : fr.rbx + (18446744073709551600#64) ≠ 0 := by
         intro eq; apply h; bv_omega
       exact hc (beq_eq_false_iff_ne.mpr nz))

theorem split128 {m : Ram} {p : BitVec 64} {b : BitVec 128} {rs} (h : memLoad m p 128=b) :
    Atom.All fnCode rs m (data128 p b) := by
  subst b
  simp only [data128,Atom.All,Atom.Holds]
  simp [extractLsb'_memLoad]

structure Scope (fr : Activation) (src : BitVec 64) (n : Nat) (m : Ram) : Prop where
  below : Writable fnCode m (fr.rsp-96) 96
  ctx : Writable fnCode m fr.rdi 56
  buf : Readable m src n
  floor : 96 ≤ fr.rsp.toNat
  align : fr.rsp.toNat%16=0
  stackCode : fr.rsp.toNat ≤ 0x1001f0 ∨ 0x102e00+96 ≤ fr.rsp.toNat
  ctxCode : fr.rdi.toNat+56 ≤ 0x1001f0 ∨ 0x102e00 ≤ fr.rdi.toNat
  stackCtx : fr.rdi.toNat+56 ≤ fr.rsp.toNat-96 ∨ fr.rsp.toNat ≤ fr.rdi.toNat
  stackBuf : src.toNat+n ≤ fr.rsp.toNat-96 ∨ fr.rsp.toNat ≤ src.toNat
  ctxBuf : src.toNat+n ≤ fr.rdi.toNat ∨ fr.rdi.toNat+56 ≤ src.toNat

theorem Scope.after {fr src n m m' rs} (s : Scope fr src n m) (f : RamWriteFrame m m' rs) :
    Scope fr src n m' := {s with below := s.below.of_frame f,ctx := s.ctx.of_frame f,buf := s.buf.of_frame f}

def addr (src : BitVec 64) (i : Nat) := src+BitVec.ofNat 64 (16*i)
def remain (s : ByteArray) (i : Nat) := BitVec.ofNat 64 (16*(s.size/16-i))

def iter (fr : Activation) (src : BitVec 64) (s : ByteArray) (i : Nat) (m : Ram) :=
  {fr with low := fr.rsp-96,rsi := addr src i,rbx := remain s i,original := m}

def regions (fr : Activation) : List MemoryRegion :=
  [⟨fr.rsp.toNat-96,96⟩,⟨fr.rdi.toNat+36,20⟩]

def word (s : ByteArray) (i : Nat) := (Bytes.packed s).extractLsb' (8*(16*i)) 128

theorem wordNat (s : ByteArray) (i : Nat) (hi : i<s.size/16) : (word s i).toNat=blockNumber s i := by
  rw [blockNumber,show 16*(i+1)=16*i+16 by omega]
  exact Bytes.slice s (16*i) 16 (by omega)

theorem iterRegion {fr src s i m} (h : 96≤fr.rsp.toNat) :
    (iter fr src s i m).region :: [⟨fr.rdi.toNat+36,20⟩] = regions fr := by
  simp [iter,Activation.region,regions]; bv_omega

end ChaCha20Poly1305.Proofs.Decrypt.Hash
