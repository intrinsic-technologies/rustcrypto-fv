import ChaCha20Poly1305.Proofs.Decrypt.FullBlock
import ChaCha20Poly1305.Proofs.Decrypt.ControlWrite
import ChaCha20Poly1305.Proofs.Decrypt.BlockMath

namespace ChaCha20Poly1305.Proofs.Decrypt.Stream.Control
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program
set_option maxHeartbeats 800000
set_option maxRecDepth 6000

@[refine_layout] def nextRegs (x : Input) (j : BitVec 64) (fr : Activation) : List Atom :=
  Full.registers fr ++ [.gpr 7 (j+1),.low 12 32 (x.w[12].toBitVec+1),
    .low 10 32 x.w[4].toBitVec,.low 11 32 x.w[8].toBitVec,.low 8 32 x.w[13].toBitVec]

theorem fullOne (x : Input) (j : BitVec 64) (fr : Activation) (a : lifted.Location) (last : Bool)
    (done : j+1 = x.n >>> 6 ↔ last = true)
    (geo : BlockGeo fr.rsp (blockPtr x j) a.store) (hl : a.label = .l100c70)
    (atoms : Atom.All fnCode a.arguments a.store ((Full.layout x j).atoms .setup fr ()))
    (pt : Atom.All fnCode a.arguments a.store (pointers x fr)) :
    Ahead lifted fnCode (fun b => b.label = (if last then .l1010b3 else .l100c70) ∧
      Atom.All fnCode b.arguments b.store (nextRegs x j fr) ∧
      RamWriteFrame a.store b.store (⟨(blockPtr x j).toNat,64⟩ :: blockScratch fr) ∧ ∀ i (hi : i<64),
        Xor.readAt b.store (blockPtr x j) i =
          (ChaChaRound.stream x.w)[i].toBitVec ^^^ Xor.readAt a.store (blockPtr x j) i) a := by
  obtain ⟨d,steps,dl,ds,df,dv⟩ := fullFront x j fr a geo hl atoms pt
  let v := chunkWords d.store (fr.rsp+176)
  have iv := qwordsInitial d.store (fr.rsp+176) d.arguments
  obtain ⟨stack,buf,apart,sc,bc⟩ := geo
  have ss := stack.readable.low
  have newPt : Atom.All fnCode d.arguments d.store (pointers x fr) := by
    apply ChaChaRound.keepFrame _ df pt
    intro t ht
    simp only [pointers,List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl|rfl|rfl <;> simp [ChaChaRound.pass,Outside,blockScratch] <;> bv_omega
  have hin : Atom.All fnCode d.arguments d.store (writeStep x j fr v last).pre := by
    have sr := stack.readable.of_frame df
    have bw := buf.of_frame df
    have hw : (blockPtr x j).toNat+64 ≤ 0x101036 ∨ 0x1010b3 ≤ (blockPtr x j).toNat := by omega
    apply (Atom.all_append _ _).2 ⟨(Atom.all_append _ _).2 ⟨ds,?_⟩, iv⟩
    exact ⟨newPt.2.1,newPt.1,sr,bw,apart,hw,trivial⟩
  obtain ⟨b,db,bl,post,bf⟩ := Micro.run (writeValid x j fr v last done) dl hin
  change Atom.All _ _ _ (nextRegs x j fr ++ qwords (blockPtr x j) v) at post
  rw [Atom.all_append] at post
  refine ⟨b,jumpTrans steps db,bl,post.1,?_,fun i hi => (qwordsRead post.2 i hi).trans (dv i hi)⟩
  apply (RamWriteFrame.refl a.store _).trans df _ |>.trans bf
  · intro r hr
    change r ∈ [_] at hr
    simp only [List.mem_singleton] at hr
    subst r
    exact ⟨_,.head _,Nat.le_refl _,Nat.le_refl _⟩
  · intro r hr
    exact ⟨r,.tail _ hr,Nat.le_refl _,Nat.le_refl _⟩
end ChaCha20Poly1305.Proofs.Decrypt.Stream.Control
