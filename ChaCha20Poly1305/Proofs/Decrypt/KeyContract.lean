import ChaCha20Poly1305.Proofs.Decrypt.StreamView
import ChaCha20Poly1305.Proofs.Decrypt.Reserve

namespace ChaCha20Poly1305.Proofs.Decrypt.Detached
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program
open Standards.RFC.ChaCha20Poly1305

@[refine_layout] def short (w : Vector UInt32 16) (buf : BitVec 64) : Stream.Input := ⟨w,buf,32,by decide⟩
@[refine_layout] def keyView (w : Vector UInt32 16) (x : Raw) (b : BitVec 64) (dst : BitVec 256) :=
  view (short w b) x 0 (zero32 b) dst

@[refine_layout] def fixed (x : Raw) (p : BitVec 64) : List Atom :=
  [.mem p 64 3684054920433006693,.mem (p+8) 64 7719281312240119090,
   .mem (p+16) 64 x.k[0],.mem (p+24) 64 x.k[1],.mem (p+32) 64 x.k[2],.mem (p+40) 64 x.k[3],
   .mem (p+52) 64 x.nl,.mem (p+60) 32 x.nh]

@[refine_layout] def keyFn (w : Vector UInt32 16) (x : Raw) (b : BitVec 64) (dst : BitVec 256) : Callee :=
  let k := keyView w x b dst
  {k with pre := fun fr => k.pre fr ++ [.fact (fr.rsp.toNat+8 ≤ fr.rdi.toNat)],
          post := fun fr => k.post fr ++ fixed x fr.rdi}

set_option maxHeartbeats 700000
set_option maxRecDepth 8000
set_option pp.maxSteps 140

private theorem kept {x : Raw} {w b dst fr} {m m' rs rs'} (g : Atom.All fnCode rs m ((keyFn w x b dst).pre fr))
    (f : RamWriteFrame m m' (fr.region :: Stream.extra (short w b) fr)) (low : fr.low.toNat≤fr.rsp.toNat) :
    Atom.All fnCode rs' m' (fixed x fr.rdi) := by
  have init : Atom.All fnCode rs m (fixed x fr.rdi) := by unpack_atoms g []; join_atoms [] <;> assumption
  have geo := g
  unpack_atoms geo []
  apply ChaChaRound.keepFrame _ f init
  intro t ht
  simp only [fixed,List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals simp [ChaChaRound.pass,Outside,Activation.region,Stream.extra,short] <;> bv_omega

theorem keyFnCorrect (key : Vector UInt8 32) (nonce : Vector UInt8 12) (b : BitVec 64) :
    (keyFn (Stream.words key nonce 0) (raw key nonce) b (Poly1305.keyBits (poly1305KeyGen key nonce))).Correct := by
  let x := Stream.keyInput key nonce b
  let dst := Poly1305.keyBits (poly1305KeyGen key nonce)
  have ok : (keyView x.w (raw key nonce) b dst).Correct :=
    viewCorrect (x := x) (key:=key) (nonce:=nonce) (ctr:=0) rfl (zero32 b) (fun _ _ h => zeroInput h)
      (Stream.keyCorrect key nonce b)
  intro fr a hl hat hf
  change Atom.All _ _ _ ((Fn100a80.active .l100a80 fr) ++ ((keyView x.w (raw key nonce) b dst).pre fr ++ _)) at hat
  rw [Atom.all_append] at hat
  obtain ⟨abi,g⟩ := hat
  have low : fr.low.toNat≤fr.rsp.toNat := by unpack_atoms abi []; omega
  let sf := {fr with original := a.store}
  obtain ⟨o,e,tag,out,f⟩ := ok sf a hl ((Atom.all_append _ _).2 ⟨abi,((Atom.all_append _ _).1 g).1⟩) (.refl _ _)
  refine ⟨o,e,tag,?_,hf.trans f (fun z hz => ⟨z,hz,Nat.le_refl _,Nat.le_refl _⟩)⟩
  change Atom.All _ _ _ (abiOut fr ++ ((keyView x.w (raw key nonce) b dst).post fr ++ fixed (raw key nonce) fr.rdi))
  rw [Atom.all_append,Atom.all_append]
  obtain ⟨ao,pr⟩ := (Atom.all_append _ _).1 out
  refine ⟨ao,pr,?_⟩
  exact kept (w:=x.w) (dst:=dst) (b:=b) (fr:=fr) g (by exact f) low

end ChaCha20Poly1305.Proofs.Decrypt.Detached
