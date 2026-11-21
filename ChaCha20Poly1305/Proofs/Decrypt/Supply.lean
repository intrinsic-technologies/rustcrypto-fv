import ChaCha20Poly1305.Proofs.Decrypt.Suffix
import ChaCha20Poly1305.Proofs.Decrypt.ReadSupply
import ChaCha20Poly1305.Proofs.Decrypt.OutputSupply

namespace ChaCha20Poly1305.Proofs.Decrypt.Wrapper
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program
open ChaCha20Poly1305.Spec.Program
open Hash Detached

set_option allowUnsafeReducibility true in
attribute [local reducible] ChaCha20Poly1305.Proofs.Decrypt.Lifted.lifted
set_option maxHeartbeats 2300000
set_option maxRecDepth 8000
set_option pp.maxSteps 160
set_option linter.constructorNameAsVariable false
attribute [local irreducible] memLoad memStore Standards.RFC.ChaCha20Poly1305.poly1305Mac
  Standards.RFC.ChaCha20Poly1305.chacha20Encrypt Standards.RFC.ChaCha20Poly1305.poly1305KeyGen

theorem supply {s : RamState} {key : Vector UInt8 32} {nonce : Vector UInt8 12} {aad msg : ByteArray}
    (hc : ValidCall decrypt s [key,nonce,aad,msg]) (long : 16≤msg.size) (small : msg.size<2^32)
    (ret cap : BitVec 64)
    (geo : Short.Geometry (Short.envOf s msg cap) (2^32)) (x : Prefix.Inputs (Short.envOf s msg cap))
    (keyEq : x.key=Prefix.initialKey s) (cipherEq : x.ciphertext=(Bytes.packed msg).setWidth (8*(Short.envOf s msg cap).n.toNat))
    (a : lifted.Location) :
    let e := Short.envOf s msg cap
    let root := Activation.ofEntry s decrypt.minStackBytes ret
    let c := {root with rbp:=1,r12:=root.r8+e.n,r13:=Short.limit e,rdx:=0}
    let p := packet key nonce aad msg (s.regValue .rdx) (s.regValue .r8) long small
    (Prefix.layout e x).Rel fnCode (root,c) (unitLoc .finish) a →
      Supplied root p e.n (BitVec.ofNat 64 aad.size) a := by
  let e := Short.envOf s msg cap
  let root := Activation.ofEntry s decrypt.minStackBytes ret
  let c := {root with rbp:=1,r12:=root.r8+e.n,r13:=Short.limit e,rdx:=0}
  let p := packet key nonce aad msg (s.regValue .rdx) (s.regValue .r8) long small
  let f := wframe root p e.n
  let sp := s.regValue .rsp
  let la := BitVec.ofNat 64 aad.size
  change (Prefix.layout e x).Rel fnCode (root,c) (unitLoc .finish) a → Supplied root p e.n la a
  intro rel
  obtain ⟨lbl,⟨_,_,_,hat⟩,wf⟩ := rel
  change Atom.All fnCode a.arguments a.store (Decrypt.frameAt .l10158b root ++
    (((Short.shared e c root ++ _) ++ (Prefix.keyAtoms (root.rsp-80) x.key ++ _)))) at hat
  obtain ⟨abi,other⟩ := (Atom.all_append _ _).1 hat
  obtain ⟨sa,extras⟩ := (Atom.all_append _ _).1 other
  obtain ⟨shared,regs⟩ := (Atom.all_append _ _).1 sa
  obtain ⟨keys,bp,v0,v1,heap,_⟩ := (Atom.all_append _ _).1 extras
  have size : e.n.toNat=msg.size := Nat.mod_eq_of_lt (by omega)
  have plen : p.n.toNat=msg.size-16 := by change (BitVec.ofNat 64 (msg.size-16)).toNat=_; rw [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have floor : 1136≤sp.toNat := hc.stackAvailable.2.2.1
  have memFrame : RamWriteFrame s.external a.store (prefixWrites s msg.size) := by
    change RamWriteFrame s.external a.store ([root.region,⟨e.heap.toNat,e.n.toNat⟩,allocatorStateRegion]) at wf
    rw [show root.region=⟨sp.toNat-1136,1136⟩ from relFrame floor,size] at wf
    exact wf
  have rootFrame : RamWriteFrame root.original a.store (root.region :: commonFoot p e.n) := wf
  obtain ⟨nr,n0,n1,ns⟩ := nonceSupply hc (by omega) memFrame
  obtain ⟨ar,av,as_,aLow⟩ := aadSupply hc (by omega) memFrame
  obtain ⟨lr,lv⟩ := aadLength hc (by omega) memFrame
  have an : la.toNat=aad.size := Nat.mod_eq_of_lt (by omega)
  have cl : memLoad a.store p.buf (8*msg.size)=Bytes.packed msg := by
    change memLoad a.store p.buf (8*e.n.toNat)=x.ciphertext at heap
    rw [cipherEq] at heap
    rw [show (Short.envOf s msg cap).n.toNat=msg.size from size,BitVec.setWidth_eq] at heap
    exact heap
  obtain ⟨ct,tagL,tagH⟩ := splitData msg long a.store p.buf p.n plen cl
  have k := keyEq.trans (keyMatch hc.inputsInMemory.1)
  have ka : Atom.All fnCode a.arguments a.store (Prefix.keyAtoms (root.rsp-80) (keyQuads key)) := k ▸ keys
  have hin : Atom.All fnCode a.arguments a.store (inputs p.x (enterD p la f)) := by
    obtain ⟨k0,k1,k2,k3,_⟩ := ka
    have eq : (enterD p la f).rdi=root.rsp-80 := by change root.rsp-136+56=root.rsp-80; bv_omega
    simp only [inputs,eq,Atom.All,Atom.Holds]
    exact ⟨k0,k1,k2,k3,n0,n1,trivial⟩
  have rootLow := (show Readable a.store root.rsp 8 by unpack_atoms abi []; assumption).low
  have sq : f.rsp=sp-136 := rfl
  have sa : sp.toNat+8≤0x100000 ∨ 0x102def≤sp.toNat-1136 := geo.stackCode
  have ro : sp.toNat+8≤0x2013a8 ∨ 0x2013e8≤sp.toNat-1136 := geo.stackRO
  have hs : p.buf.toNat+msg.size≤sp.toNat-1136 ∨ sp.toNat+8≤p.buf.toNat := size ▸ geo.stackHeap
  have ht : p.buf.toNat+msg.size≤0x100000 ∨ 0x102def≤p.buf.toNat := size ▸ geo.code
  have hro : p.buf.toNat+msg.size≤0x2013a8 ∨ 0x2013e8≤p.buf.toNat := size ▸ geo.rodata
  have dry : Writable fnCode a.store p.buf e.n.toNat := by unpack_atoms shared []; assumption
  have whole : Readable a.store p.buf (p.n.toNat+16) := by rw [show p.n.toNat+16=e.n.toNat by omega]; exact dry.readable
  have short : Writable fnCode a.store p.buf p.n.toNat := dry.sub (Nat.le_refl _) (by omega)
  have st : Writable fnCode a.store (root.rsp-1008) 1008 := by unpack_atoms abi []; assumption
  have wr : Writable fnCode a.store f.rsp 88 := st.sub (by change (sp-1008).toNat≤(sp-136).toNat; bv_omega)
    (by change (sp-136).toNat+88≤(sp-1008).toNat+1008; bv_omega)
  have spN : f.rsp.toNat=sp.toNat-136 := by rw [sq]; bv_omega
  have slot : f.rsp+144=s.regValue .rsp+8 := by change sp-136+144=sp+8; bv_omega
  have ptrA (pos : 0<aad.size) : f.r15=p.pa := by simp [f,wframe,p,packet,Nat.ne_of_gt pos,root,Activation.ofEntry]
  have gd : Atom.All fnCode a.arguments a.store (oldData p la f) := by
    apply (Atom.all_append _ _).2
    refine ⟨?_,hin⟩
    have cd : f.rsp.toNat+88≤0x1001f0 ∨ 0x102e00+872≤f.rsp.toNat := by rw [spN]; omega
    have no : f.r12.toNat+12≤f.rsp.toNat-872 ∨ f.rsp.toNat+88≤f.r12.toNat := by
      change (s.regValue .rsi).toNat+12≤(sp-136).toNat-872 ∨ (sp-136).toNat+88≤(s.regValue .rsi).toNat
      change _≤sp.toNat-1136 ∨ sp.toNat+8≤_ at ns; bv_omega
    have ad : p.pa.toNat+aad.size≤f.rsp.toNat-872 ∨ f.rsp.toNat+88≤p.pa.toNat := by
      change p.pa.toNat+aad.size≤sp.toNat-1136 ∨ sp.toNat+8≤p.pa.toNat at as_
      rw [spN]; omega
    have bh : p.buf.toNat+p.n.toNat+16≤f.rsp.toNat-872 ∨ f.rsp.toNat+88≤p.buf.toNat := by rw [spN]; omega
    have bc : p.buf.toNat+p.n.toNat≤0x100a80 ∨ 0x1014bc≤p.buf.toNat := by omega
    have gs : f.rsp.toNat+88≤0x2013a8 ∨ 0x2013e8+872≤f.rsp.toNat := by rw [spN]; omega
    have sc : f.rsp.toNat+88≤0x101596 ∨ 0x1015d4≤f.rsp.toNat := by omega
    have abi' := abi; unpack_atoms abi' []
    exact ⟨nr,slot ▸ lr,slot ▸ lv,ar,short,cd,no,ad,bh,bc,an,an ▸ aLow,ptrA,av,ct,whole,tagL,tagH,
      by assumption,by assumption,by assumption,by assumption,gs,wr,sc,trivial⟩
  refine ⟨lbl,rootFrame,?_,?_,gd,by omega,size ▸ small,?_,size ▸ hro,?_,?_,?_⟩
  · unpack_atoms abi []; join_atoms [] <;> assumption
  · unpack_atoms abi []; unpack_atoms regs []; join_atoms [f] <;> assumption
  · change p.buf.toNat+e.n.toNat≤sp.toNat-1008 ∨ sp.toNat+8≤p.buf.toNat; omega
  · rw [show (wframe root p e.n).rsp+8=root.rsp-128 by dsimp [wframe]; bv_omega]; exact v0
  · rw [show (wframe root p e.n).rsp+16=root.rsp-120 by dsimp [wframe]; bv_omega]; exact v1
  · intro good
    exact outputSupply hc (by omega) ((needsPacket (pa:=s.regValue .rdx) (heap:=s.regValue .r8) (h:=long) (small:=small)).trans good) memFrame p.n plen

end ChaCha20Poly1305.Proofs.Decrypt.Wrapper
