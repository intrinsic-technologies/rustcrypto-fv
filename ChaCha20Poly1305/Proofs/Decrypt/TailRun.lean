import ChaCha20Poly1305.Proofs.Decrypt.TailOutput
import ChaCha20Poly1305.Proofs.Decrypt.TailResidual

namespace ChaCha20Poly1305.Proofs.Decrypt.Stream.Control
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program
set_option maxHeartbeats 600000
set_option maxRecDepth 5000

def tailFrame (x : Input) (fr : Activation) : List MemoryRegion :=
  [⟨fr.rsp.toNat,124⟩,⟨fr.rdi.toNat+48,4⟩,⟨fr.rdi.toNat+64,64⟩,
    ⟨(tailPtr x).toNat,(Tail.rem64 x.n).toNat⟩]

theorem runTail (x : Input) (fr : Activation) (a : lifted.Location) (s : Scope x fr a.store)
    (pos : 0 < (Tail.rem64 x.n).toNat)
    (hl : a.label = .l1010d5)
    (hin : Atom.All fnCode a.arguments a.store ((Tail.layout x).atoms .setup fr ()))
    (save : Atom.All fnCode a.arguments a.store (tailSaved x fr)) :
    Ahead lifted fnCode (fun d => d.label = .l1014a8 ∧ Atom.All fnCode d.arguments d.store (Full.registers fr) ∧
      RamWriteFrame a.store d.store (tailFrame x fr) ∧ ∀ i (hi : i<(Tail.rem64 x.n).toNat),
        Xor.readAt d.store (tailPtr x) i =
          ((ChaChaRound.stream x.w)[i]'(Nat.lt_of_lt_of_le hi s.tailGeo.small)).toBitVec ^^^ Xor.readAt a.store (tailPtr x) i) a := by
  obtain ⟨b,ab,bl,ba,words,bf⟩ := tailOutput x fr a s hl hin save
  obtain ⟨c,bc,cl,ca,eff⟩ := tailBytes x fr b (s.after bf) pos bl ba
  have sc := (s.after bf).after eff.frame
  obtain ⟨d,cd,dl,da,df⟩ := Micro.run (finishTailValid x fr) cl (by
    have cw := sc.ctx
    have co := sc.ctxCode
    unpack_atoms ca []
    join_atoms []
    all_goals first | assumption | omega)
  have keyLow := s.ctx.readable.low
  have stackLow := s.stack.readable.low
  have bufLow := s.buf.readable.low
  have tailLow := s.tailGeo.buffer.readable.low
  have sa := s.stackBuf
  have ka := s.ctxBuf
  have rel := remNat x
  have floor := baseNat x
  have tp : (tailPtr x).toNat = x.buf.toNat+(Tail.base64 x.n).toNat := by unfold tailPtr; bv_omega
  have baseF := (RamWriteFrame.refl a.store (tailFrame x fr)).trans bf (by simp [RegionsWithin,Tail.layout,tailFrame])
  have nextF := baseF.trans eff.frame (by simp [RegionsWithin,tailFrame])
  refine ⟨d,jumpTrans ab (jumpTrans bc cd),dl,((Atom.all_append _ _).1 da).1,
    nextF.trans df (by simp [RegionsWithin,finishTail,tailFrame]),?_⟩
  intro i hi
  have ip : (tailPtr x+BitVec.ofNat 64 i).toNat = (tailPtr x).toNat+i := Xor.ptrNat (by omega)
  have pre : Xor.readAt b.store (tailPtr x) i = Xor.readAt a.store (tailPtr x) i := by
    apply bf.memLoad_eq
    simp [Outside,Tail.layout,ip,tp] <;> omega
  have post : Xor.readAt d.store (tailPtr x) i = Xor.readAt c.store (tailPtr x) i := by
    apply df.memLoad_eq
    simp [Outside,finishTail,ip,tp] <;> omega
  rw [post,eff.value _ hi,pre,sumRead words i (by omega)]

end ChaCha20Poly1305.Proofs.Decrypt.Stream.Control
