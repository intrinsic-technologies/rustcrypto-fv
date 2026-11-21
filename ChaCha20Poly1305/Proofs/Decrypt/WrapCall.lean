import ChaCha20Poly1305.Proofs.Decrypt.WrapStore
import ChaCha20Poly1305.Proofs.Decrypt.Lifted.Decrypt

namespace ChaCha20Poly1305.Proofs.Decrypt.Wrapper
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program
open Hash Detached

@[refine_layout] def afterD (f : Activation) (n : BitVec 64) := {f with r13:=n}

@[refine_layout] def enterD (p : Packet) (la : BitVec 64) (fr : Activation) :=
  {push (afterD fr p.n) with rdi:=fr.rsp+56,rsi:=fr.r12,rdx:=fr.r15,rcx:=la,r8:=fr.rsp+32,r9:=p.tag.extractLsb' 0 64}

@[refine_layout] def oldData (p : Packet) (la : BitVec 64) (f : Activation) : List Atom :=
  [.readable f.r12 12,.readable (f.rsp+144) 8,.mem (f.rsp+144) 64 la,.readable p.pa p.aad.size,.writable p.buf p.n.toNat,
   .fact (f.rsp.toNat+88≤0x1001f0 ∨ 0x102e00+872≤f.rsp.toNat),
   .fact (f.r12.toNat+12≤f.rsp.toNat-872 ∨ f.rsp.toNat+88≤f.r12.toNat),
   .fact (p.pa.toNat+p.aad.size≤f.rsp.toNat-872 ∨ f.rsp.toNat+88≤p.pa.toNat),
   .fact (p.buf.toNat+p.n.toNat+16≤f.rsp.toNat-872 ∨ f.rsp.toNat+88≤p.buf.toNat),
   .fact (p.buf.toNat+p.n.toNat≤0x100a80 ∨ 0x1014bc≤p.buf.toNat),
   .fact (la.toNat=p.aad.size),.fact (la.toNat<2^32),.fact (0<p.aad.size → f.r15=p.pa),
   .mem p.pa (8*p.aad.size) (Bytes.packed p.aad),.mem p.buf (8*p.n.toNat) p.src,
   .readable p.buf (p.n.toNat+16),.mem (p.buf+p.n) 64 (p.tag.extractLsb' 0 64),
   .mem (p.buf+p.n+8) 64 (p.tag.extractLsb' 64 64),
   .readable 0x2013a8 8,.mem 0x2013a8 64 0x102dc0,.readable 0x2013e0 8,.mem 0x2013e0 64 0x102d70,
   .fact (f.rsp.toNat+88≤0x2013a8 ∨ 0x2013e8+872≤f.rsp.toNat),
   .writable f.rsp 88,.fact (f.rsp.toNat+88≤0x101596 ∨ 0x1015d4≤f.rsp.toNat)] ++
   inputs p.x (enterD p la f)

@[refine_layout] def extraD (sp : BitVec 64) := [slot sp 0 8,slot sp 32 24]
@[refine_layout] def detachedCall (p : Packet) (la sp : BitVec 64) : Invoke.Edge where
  site := .l101596
  resume := .l1015d4
  callee := (detachedFn p).reserve (extraD sp)
  before f := live f ++ space f 872 ++ [.fact (f.rsp=sp),.fact (f.rbp=p.buf),.fact (f.r14-16=p.n)] ++ oldData p la f
  after f := live (afterD f p.n) ++ (detachedFn p).post f
  footprint := (if p.good then [⟨p.buf.toNat,p.n.toNat⟩] else []) ++ extraD sp

attribute [local irreducible] memLoad memStore Packet.good Packet.src Packet.dst Packet.x
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000
set_option pp.maxSteps 120
set_option linter.constructorNameAsVariable false

theorem detachedValid (x : Packet) (la sp : BitVec 64) :
    (Invoke.layout (detachedCall x la sp)).BlockSimulation fnCode .site := by
  refine_intro
  subst sp
  have ad : fr.rbp+fr.r14+18446744073709551600=x.buf+x.n := by bv_omega
  have hi : fr.rbp+fr.r14+18446744073709551608=x.buf+x.n+8 := by bv_omega
  have ln : fr.r14+18446744073709551600=x.n := by bv_omega
  refine_uir [Invoke.program]
  refine_lifted [ad,hi,ln]
  prepare_call (fun m => ({enterD x la fr with original:=m,ret:=0x1015d4},()))
  · cases hg : x.good <;> refine_close [enterD,ad,hi,ln,hg]
    all_goals simp only [BitVec.add_assoc] at atom53 atom54 atom55
    all_goals try first | exact atom53 | exact atom54 | exact atom55
    all_goals try (rw [show x.buf+fr.r14-16=x.buf+x.n by bv_omega]; exact atom40)
    all_goals try (rw [show x.buf+fr.r14-8=x.buf+x.n+8 by bv_omega]; exact atom41)
    all_goals apply (storesRead (by omega) atom50 _ _).trans
    all_goals first | exact atom36 | exact atom37 | omega
  · cases hg : x.good <;> close_resume [enterD,hg]
    all_goals try exact done12.1
    all_goals try assumption
    all_goals try trivial
    all_goals try (simp only [ite_true,ite_false,Bool.false_eq_true,List.nil_append,Atom.All,Atom.Holds] at done12 ⊢; first | exact done12.1 | trivial)
    all_goals simp only [hg,Bool.false_eq_true,ite_false,ite_true,BitVec.add_zero] at hframe hframe0 ⊢
    all_goals apply finishFrame atom13 atom50 hframe hframe0

end ChaCha20Poly1305.Proofs.Decrypt.Wrapper
