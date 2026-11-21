import K256.Proofs.Generate.Generator.Multiply.Split.Parameters
import K256.Proofs.Generate.Generator.Multiply.Split.Rounding.Frame
import K256.Proofs.Generate.Generator.Affine.Invert.Core.Callee
import K256.Proofs.Generate.Generator.Sample.Decide.Nonzero.Resume.Flag

namespace K256.Proofs.Generate.Generator.Multiply.Split.Rounding

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR Standards.SECG.DomainParameters.Secp256k1

theorem addOne {fr : Activation} {a b : Registers} {m n : Ram} {u : Nat}
    (add : AddExecution)
    (push : program.runBlock (dialect Extracted.programImage) ⟨.l11b8f0,a,m⟩ =
      .call ⟨.l1109b0,b,n⟩ (Generate.Generator.callFrame .l11badf 0x11badf))
    (entry : Atom.All Extracted.programImage b n (Fn1109b0.frameAt .l1109b0 (addFrame fr b)))
    (image : ∀ v ∈ Extracted.programImage, m[v.1]? = some v.2)
    (initialStack : Writable Extracted.programImage m (fr.rsp - 0xe0) 0xe0)
    (before : RamWriteFrame m n [⟨fr.rsp.toNat - 224,224⟩])
    (s : AdditionFrame fr n) (hu : u < domain.n)
    (words : WordsAt n (fr.rsp - 112) 64 (scalarWords u)) :
    ∃ c p, Reaches .l11b8f0 a m .l11badf c p ∧
      Atom.All Extracted.programImage c p (Fn11b8f0.frameAt .l11badf fr) ∧
      ParseSignature.ArgumentWidths c ∧ c[3] = ⟨64,b[3].get 64⟩ ∧
      c[12] = ⟨64,b[12].get 64⟩ ∧ c[15] = ⟨64,b[15].get 64⟩ ∧
      WordsAt p (fr.rsp - 80) 64 (scalarWords ((u+1)%domain.n)) ∧
      RamWriteFrame m p [⟨fr.rsp.toNat - 224,224⟩] := by
  have room := s.low
  have ofs (k : BitVec 64) (hk : k.toNat ≤ 224) :
      (fr.rsp - k).toNat = fr.rsp.toNat - k.toNat :=
    BitVec.toNat_sub_of_le (by rw [BitVec.le_def]; omega)
  have s224 : (fr.rsp - 224).toNat = fr.rsp.toNat - 224 := ofs 224 (by decide)
  have s160 : (fr.rsp - 160).toNat = fr.rsp.toNat - 160 := ofs 160 (by decide)
  have s112 : (fr.rsp - 112).toNat = fr.rsp.toNat - 112 := ofs 112 (by decide)
  have s80 : (fr.rsp - 80).toNat = fr.rsp.toNat - 80 := ofs 80 (by decide)
  have current := Affine.Invert.Core.stackImage initialStack (s224 ▸ before) image
  have one := parameterAt current (p := 0x202180) (x := 1) (by decide +kernel)
  have win := s.stack
  have separated := one.apart win (by decide)
  have rd : Readable n (fr.rsp - 112) 32 := win.readable.sub (by omega) (by omega)
  have wr : Writable Extracted.programImage n (fr.rsp - 80) 32 := win.sub (by omega) (by omega)
  obtain ⟨o, run, tag, endAtoms, widths, result, writes⟩ := add (fr := addFrame fr b)
    entry current (fun _ => rfl) hu (show 1 < domain.n by decide +kernel) rd one.readable wr
    (show (fr.rsp - 160).toNat + 8 ≤ (fr.rsp - 80).toNat by omega)
    (by
      intro src hs
      change src ∈ [fr.rsp - 112, (0x202180 : BitVec 64)] at hs
      change (_ ≤ (fr.rsp - 160).toNat - 64 ∨ (fr.rsp - 160).toNat + 8 ≤ _) ∧
        (_ ≤ (fr.rsp - 80).toNat ∨ (fr.rsp - 80).toNat + 32 ≤ _)
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
      rcases hs with rfl|rfl <;> constructor <;> omega) words one.words
  obtain ⟨atoms, bx, r12, r15⟩ := s.resume endAtoms writes
  refine ⟨o.values,o.store,Sample.reachesAfterSampleCall push run tag [],atoms,widths,bx,r12,r15,result,
    before.trans writes ?_⟩
  intro r hr
  change r ∈ [⟨(fr.rsp - 160).toNat - 64,64⟩,⟨(fr.rsp - 80).toNat,32⟩] at hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl|rfl <;> refine ⟨_,List.mem_singleton_self _,?_,?_⟩ <;> dsimp only <;> omega

end K256.Proofs.Generate.Generator.Multiply.Split.Rounding
