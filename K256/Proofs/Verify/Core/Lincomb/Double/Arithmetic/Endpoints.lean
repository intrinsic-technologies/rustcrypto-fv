import K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic.Layout
import K256.Proofs.Generate.Generator.Multiply.AddExecution.Replay.Compose.Endpoints

namespace K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  Common.Field Common.Point Common.Point.DoubleWords.Replay Generate.Generator.Multiply

private theorem loadAt {m : Ram} {x y v : Word} (h : memLoad m x 64 = v) (eq : x = y) :
    memLoad m y 64 = v := eq ▸ h

theorem entryAtoms {m : Ram} {q : Word} {w : PointWords} {yy zz : Limbs}
    (window : Writable Extracted.programImage m q 0x1f8)
    (words : PointWordsAt m (q + 0x128) w)
    (squares : ∀ i : Fin 5, memLoad m (q + (#v[0x20,0x28,0x48,0x60,0x40] : Vector Word 5)[i]) 64 = yy[i])
    (z : WordsAt m (q + 0x1d0) 64 zz) :
    Atom.All Extracted.programImage (Vector.replicate _ ⟨1,0⟩) m (memoryAtoms w yy zz q 53) := by
  simp only [memoryAtoms, Atom.All, Atom.Holds]
  refine ⟨window, squares 0, squares 1, squares 4, squares 2, squares 3, ?_⟩
  refine ⟨loadAt (words.1 0 (by decide)) (by simp only [wordAddr]; bv_omega), ?_⟩
  refine ⟨loadAt (words.1 1 (by decide)) (by simp only [wordAddr]; bv_omega), ?_⟩
  refine ⟨loadAt (words.1 2 (by decide)) (by simp only [wordAddr]; bv_omega), ?_⟩
  refine ⟨loadAt (words.1 3 (by decide)) (by simp only [wordAddr]; bv_omega), ?_⟩
  refine ⟨loadAt (words.1 4 (by decide)) (by simp only [wordAddr]; bv_omega), ?_⟩
  refine ⟨loadAt (words.2.1 0 (by decide)) (by simp only [wordAddr]; bv_omega), ?_⟩
  refine ⟨loadAt (words.2.1 1 (by decide)) (by simp only [wordAddr]; bv_omega), ?_⟩
  refine ⟨loadAt (words.2.1 2 (by decide)) (by simp only [wordAddr]; bv_omega), ?_⟩
  refine ⟨loadAt (words.2.1 3 (by decide)) (by simp only [wordAddr]; bv_omega), ?_⟩
  refine ⟨loadAt (words.2.1 4 (by decide)) (by simp only [wordAddr]; bv_omega), ?_⟩
  refine ⟨loadAt (words.2.2 0 (by decide)) (by simp only [wordAddr]; bv_omega), ?_⟩
  refine ⟨loadAt (words.2.2 1 (by decide)) (by simp only [wordAddr]; bv_omega), ?_⟩
  refine ⟨loadAt (words.2.2 2 (by decide)) (by simp only [wordAddr]; bv_omega), ?_⟩
  refine ⟨loadAt (words.2.2 3 (by decide)) (by simp only [wordAddr]; bv_omega), ?_⟩
  refine ⟨loadAt (words.2.2 4 (by decide)) (by simp only [wordAddr]; bv_omega), ?_⟩
  refine ⟨loadAt (z 0 (by decide)) (by simp only [wordAddr]; bv_omega), ?_⟩
  refine ⟨loadAt (z 1 (by decide)) (by simp only [wordAddr]; bv_omega), ?_⟩
  refine ⟨loadAt (z 2 (by decide)) (by simp only [wordAddr]; bv_omega), ?_⟩
  refine ⟨loadAt (z 3 (by decide)) (by simp only [wordAddr]; bv_omega), ?_⟩
  refine ⟨loadAt (z 4 (by decide)) (by simp only [wordAddr]; bv_omega), ?_⟩
  trivial

private theorem fiveWords {m : Ram} {q : Word} (offset : Word) (a b c d e : Word)
    (ha : memLoad m (q + offset) 64 = a)
    (hb : memLoad m (q + (offset + 8)) 64 = b)
    (hc : memLoad m (q + (offset + 16)) 64 = c)
    (hd : memLoad m (q + (offset + 24)) 64 = d)
    (he : memLoad m (q + (offset + 32)) 64 = e) :
    WordsAt m (q + offset) 64 #v[a,b,c,d,e] := by
  intro i hi
  rcases (by omega : i=0 ∨ i=1 ∨ i=2 ∨ i=3 ∨ i=4) with rfl|rfl|rfl|rfl|rfl
  · exact loadAt ha (by simp only [wordAddr]; bv_omega)
  · exact loadAt hb (by simp only [wordAddr]; bv_omega)
  · exact loadAt hc (by simp only [wordAddr]; bv_omega)
  · exact loadAt hd (by simp only [wordAddr]; bv_omega)
  · exact loadAt he (by simp only [wordAddr]; bv_omega)

private theorem resultY (a b c d e f g : Value) (A B C D E F G : Word)
    (ha : a = ⟨64,A⟩) (hb : b = ⟨64,B⟩) (hc : c = ⟨64,C⟩) (hd : d = ⟨64,D⟩)
    (he : e = ⟨64,E⟩) (hf : f = ⟨64,F⟩) (hg : g = ⟨64,G⟩) :
    (#v[A &&& G,B &&& G,C &&& G,D &&& G,(E >>> 52) + F] : Limbs) =
      #v[a.get 64 &&& g.get 64,b.get 64 &&& g.get 64,c.get 64 &&& g.get 64,
        d.get 64 &&& g.get 64,(e.get 64 >>> 52) + f.get 64] := by
  simp only [ha,hb,hc,hd,he,hf,hg,Value.get_mk]

set_option maxRecDepth 4096 in
theorem finalWords {a : Registers} {b : Values Value 3504} {m : Ram} {q : Word}
    {w : PointWords} {yy zz : Limbs} (vals : ValuesMatch (values a w yy zz q) b)
    (atoms : Atom.All Extracted.programImage (Vector.replicate _ ⟨1,0⟩) m (memoryAtoms w yy zz q 3504)) :
    let out := outputWords w yy zz q
    WordsAt m (q + 0x128) 64 out.x ∧ WordsAt m (q + 0x178) 64 out.z ∧
      out.y = #v[b[3482].get 64 &&& b[3368].get 64, b[3488].get 64 &&& b[3368].get 64,
        b[3494].get 64 &&& b[3368].get 64, b[3500].get 64 &&& b[3368].get 64,
        (b[3502].get 64 >>> 52) + b[3474].get 64] ∧ b[3456].width = 64 := by
  intro out
  simp only [memoryAtoms, Atom.All, Atom.Holds] at atoms
  obtain ⟨_, x0,x1,x2,x3,x4,z0,z1,z2,z3,z4,_⟩ := atoms
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact fiveWords 0x128 _ _ _ _ _ x0 x1 x2 x3 x4
  · exact fiveWords 0x178 _ _ _ _ _ z0 z1 z2 z3 z4
  ·
    have r3482 : b[3482] = ⟨64, v2024 w yy zz q⟩ := vals (3482 : Fin 3504)
    have r3368 : b[3368] = ⟨64, w59 w yy zz q⟩ := vals (3368 : Fin 3504)
    have r3488 : b[3488] = ⟨64, v2027 w yy zz q⟩ := vals (3488 : Fin 3504)
    have r3494 : b[3494] = ⟨64, v2030 w yy zz q⟩ := vals (3494 : Fin 3504)
    have r3500 : b[3500] = ⟨64, v2033 w yy zz q⟩ := vals (3500 : Fin 3504)
    have r3502 : b[3502] = ⟨64, v2033 w yy zz q⟩ := vals (3502 : Fin 3504)
    have r3474 : b[3474] = ⟨64, v2021 w yy zz q⟩ := vals (3474 : Fin 3504)
    exact resultY _ _ _ _ _ _ _ _ _ _ _ _ _ _ r3482 r3488 r3494 r3500 r3502 r3474 r3368
  ·
    have r3456 : b[3456] = ⟨64, v2013 w yy zz q⟩ := vals (3456 : Fin 3504)
    exact congrArg Value.width r3456

end K256.Proofs.Verify.Core.Lincomb.Double.Arithmetic
