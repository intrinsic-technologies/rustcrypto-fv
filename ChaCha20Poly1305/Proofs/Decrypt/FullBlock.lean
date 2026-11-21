import ChaCha20Poly1305.Proofs.Decrypt.FullKernelAll
import ChaCha20Poly1305.Proofs.Decrypt.FullXorRun
import ChaCha20Poly1305.Proofs.Decrypt.ControlLoad
import ChaCha20Poly1305.Proofs.Decrypt.StreamWords

namespace ChaCha20Poly1305.Proofs.Decrypt.Stream.Control
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program
set_option maxHeartbeats 800000
set_option maxRecDepth 6000
set_option pp.maxSteps 150

structure BlockGeo (sp d : BitVec 64) (m : Ram) : Prop where
  stack : Writable fnCode m sp 368
  buf : Writable fnCode m d 64
  apart : sp.toNat+368 ≤ d.toNat ∨ d.toNat+64 ≤ sp.toNat
  stackCode : sp.toNat+368 ≤ 0x100a80 ∨ 0x1014bc ≤ sp.toNat
  bufCode : d.toNat+64 ≤ 0x100a80 ∨ 0x1014bc ≤ d.toNat

def blockScratch (fr : Activation) : List MemoryRegion :=
  [⟨fr.rsp.toNat+4,8⟩,⟨fr.rsp.toNat+20,4⟩,⟨fr.rsp.toNat+60,4⟩,⟨fr.rsp.toNat+112,16⟩,⟨fr.rsp.toNat+176,192⟩]

@[refine_layout] def pointers (x : Input) (fr : Activation) : List Atom :=
  [.mem (fr.rsp+80) 64 (x.n >>> 6),.mem (fr.rsp+96) 64 x.buf,.mem (fr.rsp+104) 64 x.buf]

theorem sumAtFull {x : Input} {j : BitVec 64} {fr : Activation} {b : lifted.Location}
    (h : Atom.All fnCode b.arguments b.store ((Full.layout x j).atoms .finished fr ())) :
    WordsAt b.store (fr.rsp+240) 32 (sums x.w) := by
  let hh := ((Atom.all_append _ _).mp (show Atom.All _ _ _ ((Full.registers fr ++ Full.keep x j fr) ++ _) from h)).2
  intro i hi
  simp only [sums,Vector.getElem_ofFn,Fin.getElem_fin]
  rcases (show i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4 ∨ i=5 ∨ i=6 ∨ i=7 ∨ i=8 ∨ i=9 ∨ i=10 ∨ i=11 ∨ i=12 ∨ i=13 ∨ i=14 ∨ i=15 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [show wordAddr (fr.rsp+240) 32 0 = fr.rsp+240 by simp [wordAddr]]
    exact hh.1
  · rw [show wordAddr (fr.rsp+240) 32 1 = fr.rsp+244 by simp [wordAddr,BitVec.add_assoc]]
    exact hh.2.1
  · rw [show wordAddr (fr.rsp+240) 32 2 = fr.rsp+248 by simp [wordAddr,BitVec.add_assoc]]
    exact hh.2.2.1
  · rw [show wordAddr (fr.rsp+240) 32 3 = fr.rsp+252 by simp [wordAddr,BitVec.add_assoc]]
    exact hh.2.2.2.1
  · rw [show wordAddr (fr.rsp+240) 32 4 = fr.rsp+256 by simp [wordAddr,BitVec.add_assoc]]
    exact hh.2.2.2.2.1
  · rw [show wordAddr (fr.rsp+240) 32 5 = fr.rsp+260 by simp [wordAddr,BitVec.add_assoc]]
    exact hh.2.2.2.2.2.1
  · rw [show wordAddr (fr.rsp+240) 32 6 = fr.rsp+264 by simp [wordAddr,BitVec.add_assoc]]
    exact hh.2.2.2.2.2.2.1
  · rw [show wordAddr (fr.rsp+240) 32 7 = fr.rsp+268 by simp [wordAddr,BitVec.add_assoc]]
    exact hh.2.2.2.2.2.2.2.1
  · rw [show wordAddr (fr.rsp+240) 32 8 = fr.rsp+272 by simp [wordAddr,BitVec.add_assoc]]
    exact hh.2.2.2.2.2.2.2.2.1
  · rw [show wordAddr (fr.rsp+240) 32 9 = fr.rsp+276 by simp [wordAddr,BitVec.add_assoc]]
    exact hh.2.2.2.2.2.2.2.2.2.1
  · rw [show wordAddr (fr.rsp+240) 32 10 = fr.rsp+280 by simp [wordAddr,BitVec.add_assoc]]
    exact hh.2.2.2.2.2.2.2.2.2.2.1
  · rw [show wordAddr (fr.rsp+240) 32 11 = fr.rsp+284 by simp [wordAddr,BitVec.add_assoc]]
    exact hh.2.2.2.2.2.2.2.2.2.2.2.1
  · rw [show wordAddr (fr.rsp+240) 32 12 = fr.rsp+288 by simp [wordAddr,BitVec.add_assoc]]
    exact hh.2.2.2.2.2.2.2.2.2.2.2.2.1
  · rw [show wordAddr (fr.rsp+240) 32 13 = fr.rsp+292 by simp [wordAddr,BitVec.add_assoc]]
    exact hh.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · rw [show wordAddr (fr.rsp+240) 32 14 = fr.rsp+296 by simp [wordAddr,BitVec.add_assoc]]
    exact hh.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  · rw [show wordAddr (fr.rsp+240) 32 15 = fr.rsp+300 by simp [wordAddr,BitVec.add_assoc]]
    exact hh.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1


theorem fullFront (x : Input) (j : BitVec 64) (fr : Activation) (a : lifted.Location)
    (geo : BlockGeo fr.rsp (blockPtr x j) a.store) (hl : a.label = .l100c70)
    (atoms : Atom.All fnCode a.arguments a.store ((Full.layout x j).atoms .setup fr ()))
    (pt : Atom.All fnCode a.arguments a.store (pointers x fr)) :
    Ahead lifted fnCode (fun d => d.label = .l101036 ∧ Atom.All fnCode d.arguments d.store (fixedRegs x j fr) ∧
      RamWriteFrame a.store d.store (blockScratch fr) ∧ ∀ i (hi : i<64),
        Xor.readAt d.store (fr.rsp+176) i =
          (ChaChaRound.stream x.w)[i].toBitVec ^^^ Xor.readAt a.store (blockPtr x j) i) a := by
  let sf := {fr with original := a.store}
  have enter : (Full.layout x j).Rel fnCode sf (unitLoc .setup) a :=
    ⟨hl,⟨(),rfl,rfl,atoms⟩,.refl _ _⟩
  obtain ⟨b,ab,bLabel,⟨_,_,_,bout⟩,bf⟩ := Full.run x j enter
  change RamWriteFrame a.store b.store ((Full.layout x j).regions fr) at bf
  change Atom.All _ _ _ ((Full.layout x j).atoms .finished fr ()) at bout
  have key := sumAtFull bout
  obtain ⟨st,wb,apart,sc,bc⟩ := geo
  have stLow := st.readable.low
  have wbLow := wb.readable.low
  simp only [Full.layout] at bf
  let buf := blockPtr x j
  let v := chunkWords b.store buf
  have iv := qwordsInitial b.store buf b.arguments
  obtain ⟨c,bcs,cl,cout,cf⟩ := Micro.run (loadValid x j fr v) bLabel (by
    have sb := st.of_frame bf
    have db := wb.readable.of_frame bf
    have p := pt.2.2.1
    have p' : memLoad b.store (fr.rsp+104) 64 = x.buf := by
      apply Eq.trans (bf.memLoad_eq _) p
      simp [Outside]; bv_omega
    unpack_atoms bout []
    unpack_atoms iv [buf]
    join_atoms [v,buf]
    all_goals first | assumption | omega)
  change RamWriteFrame b.store c.store [⟨fr.rsp.toNat+304,64⟩,⟨fr.rsp.toNat+176,64⟩] at cf
  have stc := (st.of_frame bf).of_frame cf
  change Atom.All _ _ _ (fixedRegs x j fr ++ [.gpr 1 3] ++ qwords (fr.rsp+304) v) at cout
  rw [Atom.all_append] at cout
  obtain ⟨d,cd,dl,dout,eff⟩ := fullXor x j fr c cl stc (by omega) cout.1
  have keyC := key.of_frame cf (by decide) (by simp [Outside]; bv_omega)
  have fa : RamWriteFrame a.store c.store (blockScratch fr) := by
    apply (RamWriteFrame.refl a.store (blockScratch fr)).trans bf _ |>.trans cf
    all_goals simp [RegionsWithin,blockScratch] <;> omega
  refine ⟨d,jumpTrans ab (jumpTrans bcs cd),dl,dout,fa.trans eff.frame ?_,?_⟩
  · simp [RegionsWithin,blockScratch]; bv_omega
  · intro i hi
    rw [eff.value i hi,sumRead keyC i hi,qwordsRead (src := buf) cout.2 i hi]
    congr 1
    apply bf.memLoad_eq
    have low : (buf+BitVec.ofNat 64 i).toNat = buf.toNat+i :=
      Xor.ptrNat (by change (blockPtr x j).toNat+i < 2^64; omega)
    change Outside _ (buf+BitVec.ofNat 64 i) 1
    change fr.rsp.toNat+368 ≤ buf.toNat ∨ buf.toNat+64 ≤ fr.rsp.toNat at apart
    change buf.toNat+64 ≤ 2^32 at wbLow
    simp [Outside,low]; omega

end ChaCha20Poly1305.Proofs.Decrypt.Stream.Control
