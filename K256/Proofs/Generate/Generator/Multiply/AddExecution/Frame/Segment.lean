import K256.Proofs.Common.Tactic

namespace K256.Proofs.Generate.Generator.Multiply.AddFrame

open Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift
  K256.Proofs.Refine K256.Proofs.Generate.LIR K256.Proofs.Sec1.Affine.Uncompressed

def spills (base : BitVec 64) : List MemoryRegion :=
  [⟨base.toNat, 0x180⟩, ⟨(base + 0x188).toNat, 0x60⟩]

def BodySegment {n k : Nat} (block : Block Op Label signature Reg.count n)
    (tail : Block Op Label signature Reg.count k) : Prop :=
  ∀ {code : CodeMap} (included : ∀ x ∈ fnCode, x ∈ code) {a : Values Value n} {m : Ram}
    {base : BitVec 64} (hn : 65 < n), a[65].get 64 = base → Writable code m base 0x218 →
    ∃ b m', block.eval (dialect code) a m = tail.eval (dialect code) b m' ∧
      a.Prefix b ∧ RamWriteFrame m m' (spills base)

theorem BodySegment.trans {n k j} {b : Block Op Label signature Reg.count n}
    {c : Block Op Label signature Reg.count k} {d : Block Op Label signature Reg.count j}
    (f : BodySegment b c) (g : BodySegment c d) : BodySegment b d := by
  intro code incl a m base hn sp w
  obtain ⟨a', m', e, p, h⟩ := f incl hn sp w
  have hk : 65 < k := Nat.lt_of_lt_of_le hn p.1
  obtain ⟨a'', m'', e', p', h'⟩ := g incl hk ((congrArg (Value.get 64) (p.2 65 hn hk)).trans sp)
    (w.of_frame h)
  exact ⟨a'', m'', e.trans e', ⟨Nat.le_trans p.1 p'.1, fun i hi hi' =>
    (p'.2 i (Nat.lt_of_lt_of_le hi p.1) hi').trans (p.2 i hi _)⟩,
    h.trans h' fun r hr => ⟨r, hr, Nat.le_refl _, Nat.le_refl _⟩⟩

macro "add_body_segment" : tactic => `(tactic| (
  intro code included a m base hn sp win
  have inc := fun x hx => included x (code_l10a410 x hx)
  have hi := win.readable.low
  have upper : Writable code m (base + 0x188) 0x60 := by slot_state region
  refine ⟨?_, ?_, ?ev, ?pref, ?frame⟩
  case ev =>
    arithmetic_prefix [sp, BitVec.add_zero]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using inc)
    rfl
  case pref =>
    repeat' apply Values.Prefix.push
    exact Values.Prefix.refl _
  case frame =>
    unfold spills
    slot_state region))

end K256.Proofs.Generate.Generator.Multiply.AddFrame
