import ChaCha20Poly1305.Proofs.Decrypt.HashBytes
import ChaCha20Poly1305.Proofs.Decrypt.Reserve
import ChaCha20Poly1305.Proofs.Decrypt.TagBytes

namespace ChaCha20Poly1305.Proofs.Decrypt.Hash
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program
open Poly1305

@[refine_layout] def lastMul (r w out : Vector (BitVec 32) 5) (a c : BitVec 64) : Callee where
  entry := .l101e30
  abi := Fn101e30.active .l101e30
  pre fr := Mul.shared fr ++ (rData fr.rdi r ++ accData fr.rdi w ++ [.mem fr.rsi 64 a,.mem (fr.rsi+8) 64 c])
  post fr := accData fr.rdi out
  writes fr := [⟨fr.rdi.toNat+36,20⟩]

theorem lastMulCorrect (r w : Vector (BitVec 32) 5) (a c : BitVec 64) :
    (lastMul r w (Mul.output ⟨r,w,c++a⟩) a c).Correct := by
  intro fr b hl hat hf
  change Atom.All _ _ _ (_ ++ (Mul.shared fr ++ ((rData _ _ ++ accData _ _) ++ _))) at hat
  rw [Atom.all_append,Atom.all_append,Atom.all_append] at hat
  obtain ⟨abi,geo,limbs,lo,hi,_⟩ := hat
  have all : memLoad b.store fr.rsi 128 = c++a := by
    apply (loadJoin 8 8).trans
    congr 1 <;> assumption
  apply multiplyCorrect ⟨r,w,c++a⟩ fr b hl _ hf
  exact (Atom.all_append _ _).2 ⟨abi,(Atom.all_append _ _).2 ⟨geo,(Atom.all_append _ _).2 ⟨limbs,split128 all⟩⟩⟩

@[refine_layout] def quad7 (p : BitVec 64) (q : Vector (BitVec 64) 7) : List Atom :=
  [.mem p 64 q[0],.mem (p+8) 64 q[1],.mem (p+16) 64 q[2],.mem (p+24) 64 q[3],
   .mem (p+32) 64 q[4],.mem (p+40) 64 q[5],.mem (p+48) 64 q[6]]

def quads (r : Vector (BitVec 32) 5) (x : Finish.Input) : Vector (BitVec 64) 7 :=
  #v[x.s[1] ++ x.s[0],x.s[3] ++ x.s[2],r[1] ++ r[0],r[3] ++ r[2],x.acc[0] ++ r[4],x.acc[2] ++ x.acc[1],x.acc[4] ++ x.acc[3]]

@[refine_layout] def endFn (q : Vector (BitVec 64) 7) (lo hi : BitVec 64) : Callee where
  entry := .l101ce0
  abi := Fn101ce0.active .l101ce0
  pre fr := Finish.shared fr ++ quad7 fr.rsi q
  post fr := [.mem fr.rdi 64 lo,.mem (fr.rdi+8) 64 hi]
  writes fr := [⟨fr.rdi.toNat,16⟩]

theorem pair32 {m : Ram} {p : BitVec 64} {u v : BitVec 32} :
    memLoad m p 64 = u++v ↔ (memLoad m (p+4) 32=u ∧ memLoad m p 32=v) := by
  rw [loadJoin 4 4]
  change (memLoad m (p+4) 32 ++ memLoad m p 32 = u++v) ↔ _
  constructor
  · intro e; exact ⟨by simpa only [BitVec.extractLsb'_append_eq_left] using congrArg (fun x : BitVec 64 => x.extractLsb' 32 32) e,
        by simpa only [BitVec.extractLsb'_append_eq_right] using congrArg (fun x : BitVec 64 => x.extractLsb' 0 32) e⟩
  · rintro ⟨l,r⟩; rw [l,r]

def tagLo (x : Finish.Input) := (Finish.v101df5 x).setWidth 32 ++ Finish.v101dec x
def tagHi (x : Finish.Input) := Finish.v101e0e x ++ (Finish.v101e02 x).setWidth 32

private theorem p32 {m : Ram} {p : BitVec 64} {i j : BitVec 64} {lo hi : BitVec 32}
    (h : memLoad m (p+i) 64 = hi++lo) (eq : i+4=j) :
    memLoad m (p+j) 32=hi ∧ memLoad m (p+i) 32=lo := by
  rw [←eq,←BitVec.add_assoc]; exact pair32.mp h

theorem endCorrect (r : Vector (BitVec 32) 5) (x : Finish.Input) : (endFn (quads r x) (tagLo x) (tagHi x)).Correct := by
  intro fr a hl hat hf
  change Atom.All _ _ _ (_ ++ (Finish.shared fr ++ quad7 fr.rsi (quads r x))) at hat
  rw [Atom.all_append,Atom.all_append] at hat
  obtain ⟨abi,geo,q0,q1,_,_,q4,q5,q6,_⟩ := hat
  have a0 := pair32.mp q0
  have a1 := p32 (j := 12) q1 rfl
  have a4 := p32 (j := 36) q4 rfl
  have a5 := p32 (j := 44) q5 rfl
  have a6 := p32 (j := 52) q6 rfl
  have start : Atom.All fnCode a.arguments a.store ((finishFn x).abi fr ++ (finishFn x).pre fr) :=
    (Atom.all_append _ _).2 ⟨abi,(Atom.all_append _ _).2
      ⟨geo,a0.2,a0.1,a1.2,a1.1,a4.1,a5.2,a5.1,a6.2,a6.1,trivial⟩⟩
  obtain ⟨o,e,t,h,f⟩ := finishFnCorrect x fr a hl start hf
  rw [Atom.all_append] at h
  obtain ⟨done,lo,q1,q2,hi,_⟩ := h
  refine ⟨o,e,t,(Atom.all_append _ _).2 ⟨done,?_,?_,trivial⟩,f⟩
  · exact pair32.mpr ⟨q1,lo⟩
  · apply pair32.mpr
    exact ⟨by rw [BitVec.add_assoc]; exact hi,q2⟩

end ChaCha20Poly1305.Proofs.Decrypt.Hash
