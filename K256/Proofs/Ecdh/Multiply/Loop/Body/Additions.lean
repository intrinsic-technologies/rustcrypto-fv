import K256.Proofs.Ecdh.Multiply.Loop.Body.Additions.Execution

namespace K256.Proofs.Generate.Generator.Multiply

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR
  Standards.SECG.DomainParameters.Secp256k1

theorem peerWindowAdditions (select : type_of% @lookup) (add : type_of% @addCall)
    {fr : Activation} {initial a : Registers} {m : Ram} {d k : Nat} {peer : Projective} {p : Projective}
    (entry : PeerCoreEntry fr initial d peer) (bound : k < 32) (s : PeerRoundState fr d peer k .l11f64e a m)
    (acc : p.Stored m (fr.rsp - 0xb90))
    (left : TableAt m (fr.rsp - 0xcb8 + 0x850) (peerFirstBase d peer))
    (right : TableAt m (fr.rsp - 0xcb8 + 0x490) (peerSecondBase d peer))
    (temp : a[12].get 64 = fr.rsp - 0xcb8 + 0x850) (zero : a[14].get 64 = 0) :
    ∃ b n l r, Reaches .l11f64e a m .l11f6a6 b n ∧ PeerRoundState fr d peer k .l11f6a6 b n ∧
      ((p.add l).add r).Stored n (fr.rsp - 0xb90) ∧ l.valid ∧ r.valid ∧
      l.value = Curve.selectDigit (peerFirstBase d peer) (Curve.radixDigit (Curve.radixRemaining (firstComponent d).natAbs k)) ∧
      r.value = Curve.selectDigit (peerSecondBase d peer) (Curve.radixDigit (Curve.radixRemaining (secondComponent d).natAbs k)) ∧
      b[12].get 64 = fr.rsp - 0xcb8 + 0x490 ∧ b[14].get 64 = 0 := by
  have accSlot : roundSp fr + 0x128 = fr.rsp - 0xb90 := by dsimp [roundSp]; bv_omega
  rw [← accSlot] at acc ⊢
  obtain ⟨a₁,m₁,l,h₁,s₁,acc₁,l₁,lv,leftVal,bp,temp,ptr,zero,_,w₁⟩ :=
    peerWindowLookup (d := d) (k := k) (p := p) select true entry bound s acc (by simpa only [tableOffset,peerWindowBase,↓reduceIte] using left) temp zero (by intro h; contradiction) (by intro h; contradiction)
  obtain ⟨a₂,m₂,h₂,s₂,acc₂,r15,regs,w₂⟩ := peerWindowAddition add true entry s₁ acc₁ l₁ bp (by intro h; contradiction)
  have right' := peerRightTableAfterCalls entry right w₁ w₂
  obtain ⟨a₃,m₃,r,h₃,s₃,acc₃,r₃,rv,rightVal,bp,temp,_,zero,keep,_⟩ :=
    peerWindowLookup (d := d) (k := k) (p := _) select false entry bound s₂ acc₂ (by simpa only [tableOffset,peerWindowBase,Bool.false_eq_true,↓reduceIte] using right')
      ((congrArg (Value.get 64) (regs 12 (by decide))).trans temp)
      ((congrArg (Value.get 64) (regs 14 (by decide))).trans zero)
      (fun _ => (congrArg (Value.get 64) (regs 13 (by decide))).trans ptr)
      (fun _ => (congrArg (Value.get 64) (regs 5 (by decide))).trans bp)
  obtain ⟨b,n,h₄,s₄,acc₄,_,regs,_⟩ := peerWindowAddition add false entry s₃ acc₃ r₃ bp
    (fun _ => (congrArg (Value.get 64) keep).trans r15)
  exact ⟨b,n,l,r,((h₁.trans h₂).trans h₃).trans h₄,s₄,acc₄,lv,rv,
    by simpa only [peerWindowBase,windowIndex,windowComponent,↓reduceIte] using leftVal,
    by simpa only [peerWindowBase,windowIndex,windowComponent,Bool.false_eq_true,↓reduceIte] using rightVal,
    (congrArg (Value.get 64) (regs 12 (by decide))).trans temp,
    (congrArg (Value.get 64) (regs 14 (by decide))).trans zero⟩

end K256.Proofs.Generate.Generator.Multiply
