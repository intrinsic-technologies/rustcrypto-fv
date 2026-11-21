import ChaCha20Poly1305.Proofs.Decrypt.CallTactic
import ChaCha20Poly1305.Proofs.Decrypt.KeyContract
import ChaCha20Poly1305.Proofs.Decrypt.TagCalls

namespace ChaCha20Poly1305.Proofs.Decrypt.Detached
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program
open Hash Poly1305

@[refine_layout] def initGeo (fr : Activation) : List Atom :=
  [.readable fr.rsi 32,.writable fr.rdi 56,
   .fact (fr.rdi.toNat+56≤fr.rsi.toNat ∨ fr.rsi.toNat+32≤fr.rdi.toNat),
   .fact (fr.rdi.toNat+56≤0x101e40 ∨ 0x101eb8≤fr.rdi.toNat),
   .fact (fr.rdi.toNat+56≤fr.rsp.toNat ∨ fr.rsp.toNat+8≤fr.rdi.toNat)]
@[refine_layout] def pads (p lo hi : BitVec 64) : List Atom := [.mem p 64 lo,.mem (p+8) 64 hi]
@[refine_layout] def initWide (k : BitVec 256) (r zero : Vector (BitVec 32) 5) (lo hi : BitVec 64) : Callee where
  entry := .l101e40
  abi := Fn101e40.active .l101e40
  pre fr := initGeo fr ++ [.mem fr.rsi 256 k]
  post fr := pads fr.rdi lo hi ++ rData fr.rdi r ++ accData fr.rdi zero
  writes fr := [⟨fr.rdi.toNat,56⟩]

theorem initWideCorrect (k : Vector UInt8 32) :
    (initWide (keyBits k) (rWords k) zeroAcc ((keyBits k).extractLsb' 128 64) ((keyBits k).extractLsb' 192 64)).Correct := by
  intro fr a lbl hat hf
  change Atom.All _ _ _ (_ ++ (initGeo fr ++ [.mem fr.rsi 256 (keyBits k)])) at hat
  rw [Atom.all_append,Atom.all_append] at hat
  obtain ⟨abi,geo,key,_⟩ := hat
  have part (i j : Nat) (h : 8*(i+j)≤256) := (Hash.loadPart (m:=a.store) (p:=fr.rsi) i j h).symm
  change memLoad a.store fr.rsi 256=keyBits k at key
  simp only [key] at part
  obtain ⟨rd,wr,ap,cd,st,_⟩ := geo
  have e0 := part 0 4 (by decide)
  rw [BitVec.add_zero] at e0
  have pre : Atom.All _ _ _ ((initFn (keyBits k)).abi fr ++ (initFn (keyBits k)).pre fr) :=
    (Atom.all_append _ _).2 ⟨abi,rd,wr,ap,cd,st,e0,part 3 4 (by decide),part 6 4 (by decide),
      part 9 4 (by decide),part 12 4 (by decide),part 16 8 (by decide),part 24 8 (by decide),trivial⟩
  obtain ⟨o,run,tag,post,f⟩ := initFnCorrect (keyBits k) fr a lbl pre hf
  obtain ⟨done,_,ds⟩ := (Atom.all_append _ _).1 post
  exact ⟨o,run,tag,(Atom.all_append _ _).2 ⟨done,ds⟩,f⟩

@[refine_layout] def newCtx (fr : Activation) := {fr with rdi := fr.rsp+336,r12 := fr.rsp+336,r15 := 274877906879}
@[refine_layout] def initCall (k : BitVec 256) (r zero : Vector (BitVec 32) 5) (lo hi sp : BitVec 64) : Invoke.Edge where
  site := .l10038c
  resume := .l1003ae
  callee := initWide k r zero lo hi
  before fr := regs {fr with rdi := fr.r12} ++ [.gpr 5 fr.rbp] ++ space fr 8 ++
    [.fact (fr.rsp=sp),.mem (fr.rsp+160) 256 k] ++ initGeo {push fr with rdi:=fr.rsp+336,rsi:=fr.rsp+160}
  after fr := regs (newCtx fr) ++ [.gpr 5 fr.rbp] ++ (initWide k r zero lo hi).post (newCtx fr)
  footprint := [slot sp 336 56]

attribute [local irreducible] memLoad memStore

set_option maxHeartbeats 1600000
set_option maxRecDepth 7500
set_option pp.maxSteps 130
theorem initValid (k : BitVec 256) (r zero : Vector (BitVec 32) 5) (lo hi sp : BitVec 64) :
    (Invoke.layout (initCall k r zero lo hi sp)).BlockSimulation fnCode .site := by
  refine_intro
  subst sp
  refine_uir [Invoke.program]
  refine_lifted []
  prepare_call (fun m => ({fr with original:=m,rsp:=fr.rsp-8,ret:=0x1003ae,rdi:=fr.rsp+336,rsi:=fr.rsp+160,r12:=fr.rsp+336,r15:=274877906879},()))
  · refine_close [BitVec.add_assoc]
    all_goals try assumption
  · close_resume [BitVec.add_assoc]
    all_goals simp only [BitVec.add_assoc] at done12 done13 done14 done15 done16 done17 done18 done19 done20 done21 done22 
    all_goals assumption

end ChaCha20Poly1305.Proofs.Decrypt.Detached
