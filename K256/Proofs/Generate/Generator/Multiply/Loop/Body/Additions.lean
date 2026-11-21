import K256.Proofs.Generate.Generator.Multiply.Loop.Body.Additions.Execution
import K256.Proofs.Generate.Generator.Multiply.AddExecution.Call

namespace K256.Proofs.Generate.Generator.Multiply

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR
  Standards.SECG.DomainParameters.Secp256k1

theorem windowAdditions (select : type_of% @lookup) (add : type_of% @addCall)
    {fr : Activation} {initial a : Registers} {m : Ram} {d k : Nat} {p : Projective}
    (entry : CoreEntry fr initial d) (bound : k < 32) (s : RoundState fr d k .l11f64e a m)
    (acc : p.Stored m (fr.rsp - 0xb90))
    (left : TableAt m (fr.rsp - 0xcb8 + 0x850) (firstBase d))
    (right : TableAt m (fr.rsp - 0xcb8 + 0x490) (secondBase d))
    (temp : a[12].get 64 = fr.rsp - 0xcb8 + 0x850) (zero : a[14].get 64 = 0) :
    ∃ b n l r, Reaches .l11f64e a m .l11f6a6 b n ∧ RoundState fr d k .l11f6a6 b n ∧
      ((p.add l).add r).Stored n (fr.rsp - 0xb90) ∧ l.valid ∧ r.valid ∧
      l.value = Curve.selectDigit (firstBase d) (Curve.radixDigit (Curve.radixRemaining (firstComponent d).natAbs k)) ∧
      r.value = Curve.selectDigit (secondBase d) (Curve.radixDigit (Curve.radixRemaining (secondComponent d).natAbs k)) ∧
      b[12].get 64 = fr.rsp - 0xcb8 + 0x490 ∧ b[14].get 64 = 0 := by
  have accSlot : roundSp fr + 0x128 = fr.rsp - 0xb90 := by dsimp [roundSp]; bv_omega
  rw [← accSlot] at acc ⊢
  obtain ⟨a₁,m₁,l,h₁,s₁,acc₁,l₁,lv,leftVal,bp,temp,ptr,zero,_,w₁⟩ :=
    windowLookup (d := d) (k := k) (p := p) select true entry bound s acc (by simpa only [tableOffset,windowBase,↓reduceIte] using left) temp zero (by intro h; contradiction) (by intro h; contradiction)
  obtain ⟨a₂,m₂,h₂,s₂,acc₂,r15,regs,w₂⟩ := windowAddition add true entry s₁ acc₁ l₁ bp (by intro h; contradiction)
  have right' := rightTableAfterCalls entry right w₁ w₂
  obtain ⟨a₃,m₃,r,h₃,s₃,acc₃,r₃,rv,rightVal,bp,temp,_,zero,keep,_⟩ :=
    windowLookup (d := d) (k := k) (p := _) select false entry bound s₂ acc₂ (by simpa only [tableOffset,windowBase,Bool.false_eq_true,↓reduceIte] using right')
      ((congrArg (Value.get 64) (regs 12 (by decide))).trans temp)
      ((congrArg (Value.get 64) (regs 14 (by decide))).trans zero)
      (fun _ => (congrArg (Value.get 64) (regs 13 (by decide))).trans ptr)
      (fun _ => (congrArg (Value.get 64) (regs 5 (by decide))).trans bp)
  obtain ⟨b,n,h₄,s₄,acc₄,_,regs,_⟩ := windowAddition add false entry s₃ acc₃ r₃ bp
    (fun _ => (congrArg (Value.get 64) keep).trans r15)
  exact ⟨b,n,l,r,((h₁.trans h₂).trans h₃).trans h₄,s₄,acc₄,lv,rv,
    by simpa only [windowBase,windowIndex,windowComponent,↓reduceIte] using leftVal,
    by simpa only [windowBase,windowIndex,windowComponent,Bool.false_eq_true,↓reduceIte] using rightVal,
    (congrArg (Value.get 64) (regs 12 (by decide))).trans temp,
    (congrArg (Value.get 64) (regs 14 (by decide))).trans zero⟩

end K256.Proofs.Generate.Generator.Multiply
