import K256.Proofs.Sec1.Tactic.Lemma.Refine
import K256.Proofs.Signing.UpdateV.Prepare.Entry
import K256.Proofs.Signing.UpdateV.Prepare.PadLoops
import K256.Proofs.Signing.UpdateV.Prepare.Compress
import K256.Proofs.Signing.UpdateV.Prepare.ContextCopy
import K256.Proofs.Signing.UpdateV.Prepare.Append

namespace K256.Proofs.Signing.UpdateV

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.RFC Standards.NIST.SHA2

theorem prepare {fr : Activation} {a : Values Value Reg.count} {key value : ByteArray}
    (entry : Atom.All Extracted.programImage a fr.original (Fn104970.frameAt .l104970 fr))
    (image : ∀ b ∈ Extracted.programImage, fr.original[b.1]? = some b.2)
    (low : fr.low = fr.rsp - 1200) (depth : 1200 ≤ fr.rsp.toNat)
    (limit : fr.rsp.toNat + 8 < 2^32) (dataLow : fr.rdi.toNat + 64 < 2^32)
    (apart : fr.rdi.toNat + 64 ≤ fr.low.toNat ∨ fr.rsp.toNat + 8 ≤ fr.rdi.toNat)
    (writable : Writable Extracted.programImage fr.original fr.rdi 64)
    (k : (⟨fr.rdi.toNat, 32⟩ : MemoryRegion).HasBytes fr.original key)
    (v : (⟨fr.rdi.toNat + 32, 32⟩ : MemoryRegion).HasBytes fr.original value) :
    ∃ b m, (program.sem (dialect Extracted.programImage)).Reaches
      ⟨⟨.l104970, a, fr.original⟩, []⟩ ⟨⟨.l104c21, b, m⟩, []⟩ ∧
      Frame .l104c21 fr b m ∧ b[14] = ⟨64, fr.rsp - 488 + 272⟩ ∧
      HmacStateAt m (fr.rsp - 488 + 272) key value := by
  let sp := fr.rsp - 488
  have spNat : sp.toNat = fr.rsp.toNat - 488 :=
    BitVec.toNat_sub_of_le (by change 488 ≤ fr.rsp.toNat; omega)
  have addNat (off : Nat) (h : off ≤ 488) :
      (sp + BitVec.ofNat 64 off).toNat = sp.toNat + off := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := off) (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have baseNat : (sp+8).toNat = sp.toNat + 8 := addNat 8 (by decide)
  have lowNat : fr.low.toNat = fr.rsp.toNat - 1200 := by
    rw [low, BitVec.toNat_sub_of_le (by exact depth)]
    rfl
  have withinPad : RegionsWithin [⟨(sp + 8).toNat, 64⟩] [fr.region] := by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨_, List.mem_cons_self, ?_, ?_⟩
    · change fr.low.toNat ≤ (sp + 8).toNat
      omega
    · change (sp + 8).toNat + 64 ≤ fr.low.toNat + (fr.rsp.toNat - fr.low.toNat)
      omega
  have outsidePad (off n : Nat) (lo : 72 ≤ off) (hi : off + n ≤ 488) :
      Outside [⟨(sp + 8).toNat, 64⟩] (sp + BitVec.ofNat 64 off) n := by
    have addr := addNat off (by omega)
    refine ⟨by omega, fun r hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    right
    change (sp + 8).toNat + 64 ≤ _
    omega
  obtain ⟨a₁, m₁, r₁, f₁, w₁, i₁, p₁⟩ :=
    padEntry entry low depth limit dataLow apart writable k
  obtain ⟨a₂, m₂, r₂, f₂, w₂, _, p₂⟩ :=
    padLoop (fr := fr) false f₁ i₁ low depth limit p₁
  obtain ⟨a₃, m₃, r₃, f₃, w₃, i₃, ctx, p₃, hash, used, count⟩ :=
    compressPad f₂ (w₁.trans w₂ withinPad) image low depth limit p₂
  obtain ⟨a₄, m₄, r₄, f₄, w₄, ctx', p₄⟩ :=
    padLoop (fr := fr) true f₃ i₃ low depth limit p₃
  have hash' := WordsAt.of_frame hash.2 w₄ (by decide) (outsidePad 168 32 (by decide) (by decide))
  obtain ⟨a₅, m₅, r₅, f₅, w₅, buf, state⟩ := copyContext f₄ (w₃.trans w₄ withinPad)
    low depth limit (ctx'.trans ctx) p₄ ⟨hash.1, hash'⟩
    ((w₄.memLoad_eq (outsidePad 167 1 (by decide) (by decide))).trans used)
    ((w₄.memLoad_eq (outsidePad 200 8 (by decide) (by decide))).trans count)
  obtain ⟨b, m, r₆, post⟩ :=
    appendValue f₅ w₅ low depth limit dataLow apart writable v buf state
  simp only [Bool.false_eq_true, ↓reduceIte] at r₂
  simp only [↓reduceIte] at r₄
  exact ⟨b, m, r₁.trans (r₂.trans (r₃.trans (r₄.trans (r₅.trans r₆)))), post⟩

end K256.Proofs.Signing.UpdateV
