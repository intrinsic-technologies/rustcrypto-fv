import ChaCha20Poly1305.Proofs.Decrypt.KeyMaterial
import ChaCha20Poly1305.Proofs.Decrypt.DetachedEntry
import ChaCha20Poly1305.Proofs.Decrypt.TagContracts

namespace ChaCha20Poly1305.Proofs.Decrypt.Detached
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program
open Standards.RFC.ChaCha20Poly1305

def raw (key : Vector UInt8 32) (nonce : Vector UInt8 12) : Raw :=
  ⟨keyQuads key,pair nonce 0,(word nonce 2).toBitVec⟩

@[refine_layout] def header (x : Raw) (ctr : BitVec 32) (p : BitVec 64) : List Atom :=
  [.mem p 64 3684054920433006693,.mem (p+8) 64 7719281312240119090,
   .mem (p+16) 64 x.k[0],.mem (p+24) 64 x.k[1],.mem (p+32) 64 x.k[2],.mem (p+40) 64 x.k[3],
   .mem (p+48) 32 ctr,.mem (p+52) 64 x.nl,.mem (p+60) 32 x.nh]

@[refine_layout] def vec (p b n : BitVec 64) : List Atom :=
  [.mem p 64 b,.mem (p+8) 64 b,.mem (p+16) 64 n]

@[refine_layout] def zero32 (b : BitVec 64) : List Atom :=
  [.mem b 64 0,.mem (b+8) 64 0,.mem (b+16) 64 0,.mem (b+24) 64 0]

@[refine_layout] def view (x : Stream.Input) (raw : Raw) (ctr : BitVec 32) (src : List Atom)
    (dst : BitVec (8*x.n.toNat)) : Callee where
  entry := .l100a80
  abi := Fn100a80.active .l100a80
  pre fr := Stream.geometry x fr ++ (header raw ctr fr.rdi ++ ([.mem (fr.rdi+64) 8 64] ++ vec fr.rsi x.buf x.n) ++ src)
  post _ := [.gpr 0 0,.mem x.buf (8*x.n.toNat) dst]
  writes := Stream.extra x

private theorem splitQ {m : Ram} {p : BitVec 64} {i j : BitVec 64} {a b : BitVec 32}
    (h : memLoad m (p+i) 64=b++a) (eq : i+4=j) : memLoad m (p+i) 32=a ∧ memLoad m (p+j) 32=b := by
  rw [←eq,←BitVec.add_assoc]; exact (Hash.pair32.mp h).symm

set_option maxHeartbeats 500000
set_option maxRecDepth 8000

theorem headerState {key : Vector UInt8 32} {nonce : Vector UInt8 12} {ctr : Nat} {x : Stream.Input}
    (hw : x.w=Stream.words key nonce ctr) {m rs p}
    (h : Atom.All fnCode rs m (header (raw key nonce) (BitVec.ofNat 32 ctr) p)) :
    Atom.All fnCode rs m (Stream.state x p) := by
  obtain ⟨a,b,c,d,e,f,g,n,last,_⟩ := h
  have a := Hash.pair32.mp (show memLoad m p 64 = (0x3320646e#32) ++ (0x61707865#32) from a)
  have b := splitQ (j:=12) (show memLoad m (p+8) 64 = (0x6b206574#32) ++ (0x79622d32#32) from b) rfl
  have c := splitQ (j:=20) (show memLoad m (p+16) 64 = (word key 1).toBitVec ++ (word key 0).toBitVec from c) rfl
  have d := splitQ (j:=28) (show memLoad m (p+24) 64 = (word key 3).toBitVec ++ (word key 2).toBitVec from d) rfl
  have e := splitQ (j:=36) (show memLoad m (p+32) 64 = (word key 5).toBitVec ++ (word key 4).toBitVec from e) rfl
  have f := splitQ (j:=44) (show memLoad m (p+40) 64 = (word key 7).toBitVec ++ (word key 6).toBitVec from f) rfl
  have n := splitQ (j:=56) (show memLoad m (p+52) 64 = (word nonce 1).toBitVec ++ (word nonce 0).toBitVec from n) rfl
  simp only [Stream.state,hw]
  exact ⟨a.2,a.1,b.1,b.2,c.1,c.2,d.1,d.2,e.1,e.2,f.1,f.2,g,n.1,n.2,last,trivial⟩

theorem viewCorrect {key : Vector UInt8 32} {nonce : Vector UInt8 12} {ctr : Nat} {x : Stream.Input}
    (hw : x.w=Stream.words key nonce ctr) (input : List Atom) {src dst : BitVec (8*x.n.toNat)}
    (inp : ∀ m rs, Atom.All fnCode rs m input → memLoad m x.buf (8*x.n.toNat)=src)
    (ok : (Stream.fn x src dst).Correct) : (view x (raw key nonce) (BitVec.ofNat 32 ctr) input dst).Correct := by
  intro fr a hl hat hf
  change Atom.All _ _ _ (_ ++ (Stream.geometry x fr ++ ((header _ _ _ ++ _) ++ input))) at hat
  rw [Atom.all_append,Atom.all_append,Atom.all_append,Atom.all_append] at hat
  obtain ⟨abi,geo,⟨hdr,more⟩,data⟩ := hat
  apply ok fr a hl _ hf
  change Atom.All _ _ _ (_ ++ (((Stream.geometry x fr ++ Stream.state x fr.rdi) ++ _ ++ []) ++ _))
  rw [List.append_nil,Atom.all_append,Atom.all_append,Atom.all_append,Atom.all_append]
  exact ⟨abi,⟨⟨geo,headerState hw hdr⟩,more⟩,inp _ _ data,trivial⟩

theorem zeroInput {m rs p} (h : Atom.All fnCode rs m (zero32 p)) : memLoad m p 256=0 := by
  obtain ⟨e0,e1,e2,e3,_⟩ := h
  have z0 : memLoad m p 128 = 0 := by
    rw [Hash.loadJoin 8 8]; change memLoad m (p+8) 64 ++ memLoad m p 64=0#128
    rw [e1,e0]; rfl
  have z1 : memLoad m (p+16) 128=0 := by
    rw [Hash.loadJoin 8 8,BitVec.add_assoc]
    change memLoad m (p+24) 64 ++ memLoad m (p+16) 64=0#128; rw [e3,e2]; rfl
  rw [Hash.loadJoin 16 16]; change memLoad m (p+16) 128 ++ memLoad m p 128=0#256
  rw [z0,z1]; rfl

end ChaCha20Poly1305.Proofs.Decrypt.Detached
