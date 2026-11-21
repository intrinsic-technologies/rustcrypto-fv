import K256.Proofs.Generate.Generator.Multiply.Split.Multiplication.Reduction.Layout

namespace K256.Proofs.Generate.Generator.Multiply.Split.Reduction.Replay

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR K256.Proofs.Common.Tactic
  K256.Proofs.Common.Tactic.Replay K256.Proofs.Common.Point
  K256.Proofs.Sec1.Affine.Uncompressed

open K256.Proofs.Common.Invert.LinearCombination

theorem barrierArguments {b : Registers} {last : Values Value 483} {m n : Ram}
    (run : barrier.eval (dialect Extracted.programImage) last m =
       .call ⟨.l127d50, b, n⟩ (callFrame .l11b864 0x11b864)) :
    b[4] = last[480] ∧ b[7] = last[478] ∧ b[13] = last[476] ∧
    b[12] = last[393] ∧ b[14] = last[424] ∧ b[5] = last[455] ∧
    b[15] = last[359] ∧ b[3] = last[362] ∧ n = m := by
  change Transfer.call _ _ = Transfer.call _ _ at run
  injection run with same _
  cases same
  exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩

theorem terminalValues {a : Registers} {w : Vector (BitVec 64) 8} {fr : Activation}
    {last : Values Value 483} (hv : ValuesMatch (values a fr w) last) :
    last[480] = ⟨64,fr.rsp - 128⟩ ∧ last[478] = ⟨64,v478 w⟩ ∧ last[476] = ⟨64,v476 w⟩ ∧
    last[393] = ⟨64,v393 w⟩ ∧ last[424] = ⟨64,v424 w⟩ ∧ last[455] = ⟨64,v455 w⟩ ∧
    last[359] = ⟨64,v359 w⟩ ∧ last[362] = ⟨64,v362 w⟩ := by
  exact ⟨hv 480,hv 478,hv 476,hv 393,hv 424,hv 455,hv 359,hv 362⟩

set_option maxRecDepth 4000 in
theorem barrierCandidates {a b : Registers} {fr : Activation} {w : Vector (BitVec 64) 8}
    {last : Values Value 483} {m n : Ram}
    (hv : ValuesMatch (values a fr w) last)
    (hm : Atom.All Extracted.programImage (Vector.replicate _ ⟨1, 0⟩) m (memoryAtoms fr w 483))
    (run : barrier.eval (dialect Extracted.programImage) last m =
       .call ⟨.l127d50, b, n⟩ (callFrame .l11b864 0x11b864)) :
    ∀ (r : Limbs × Bool) (d : Limbs × BitVec 64),
    v478 w = carryWord r.2 →
    v476 w = -carryWord (d.2 != 0) →
    v393 w = d.1.l1 →
    v424 w = d.1.l2 →
    v455 w = d.1.l3 →
    v359 w = r.1.l2 →
    v362 w = r.1.l3 →
    v353 w = r.1.l0 →
    v356 w = r.1.l1 →
    v368 w = d.1.l0 →
    Candidates fr b n r.1 d.1 r.2 (d.2 != 0) := by
  intro r d h478 h476 h393 h424 h455 h359 h362 h353 h356 h368
  obtain ⟨sp,ar,sg,d₁,d₂,d₃,r₂,r₃,rfl⟩ := barrierArguments run
  obtain ⟨sp',ar',sg',d₁',d₂',d₃',r₂',r₃'⟩ := terminalValues hv
  obtain ⟨_,_,_,_,_,_,_,_,_,_,ret,_,r₀,_,d₀,_,_,r₁,_⟩ := hm
  have word {v : Value} {x : BitVec 64} (h : v = ⟨64,x⟩) : v.get 64 = x :=
    congrArg (Value.get 64) h
  exact ⟨word (sp.trans sp'), (word (ar.trans ar')).trans h478,
    (word (sg.trans sg')).trans h476, (word (d₁.trans d₁')).trans h393,
    (word (d₂.trans d₂')).trans h424, (word (d₃.trans d₃')).trans h455,
    (word (r₂.trans r₂')).trans h359, (word (r₃.trans r₃')).trans h362,
    r₀.trans h353, r₁.trans h356, d₀.trans h368, ret⟩

end K256.Proofs.Generate.Generator.Multiply.Split.Reduction.Replay
