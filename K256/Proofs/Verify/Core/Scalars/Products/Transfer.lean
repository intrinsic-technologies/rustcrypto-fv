import K256.Proofs.Generate.Generator.Multiply.Split.Multiplication.Execution
import K256.Proofs.Generate.Serialize.Transfer.Relabel
import K256.Proofs.Verify.Core.Scalars.Products.Inputs

namespace K256.Proofs.Verify.Core.ScalarProduct

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  CFG Lift Refine Verify.LIR Generate.Serialize
  Standards.SECG.DomainParameters.Secp256k1 Generate.Generator.Multiply

private def labels : List (Generate.LIR.Label × Verify.LIR.Label) :=
  [(.l1099c0,.l1099c0), (.l109be7,.l109be7), (.l11b510,.l11b510),
   (.l11b53b,.l11b53b), (.l11b5a3,.l11b5a3), (.l11b5ba,.l11b5ba),
   (.l11b864,.l11b864), (.l11b874,.l11b874), (.l11b880,.l11b880),
   (.l11b88c,.l11b88c), (.l127d50,.l127d50)]

private def target : Generate.LIR.Label → Option Verify.LIR.Label
  | .l1099c0 => some .l1099c0
  | .l109be7 => some .l109be7
  | .l11b510 => some .l11b510
  | .l11b53b => some .l11b53b
  | .l11b5a3 => some .l11b5a3
  | .l11b5ba => some .l11b5ba
  | .l11b864 => some .l11b864
  | .l11b874 => some .l11b874
  | .l11b880 => some .l11b880
  | .l11b88c => some .l11b88c
  | .l127d50 => some .l127d50
  | _ => none

private theorem target_mem {a : Generate.LIR.Label} {b : Verify.LIR.Label} (h : target a = some b) :
    (a,b) ∈ labels := by
  unfold target at h
  split at h <;> cases h <;> simp [labels]

set_option maxRecDepth 16384 in
set_option maxHeartbeats 5000000 in
private theorem blocks (a : Generate.LIR.Label) (b : Verify.LIR.Label) (h : target a = some b) :
    Relabel.block target (Generate.LIR.program.blocks a) =
      Relabel.block some (Verify.LIR.program.blocks b) := by
  have pair := target_mem h
  simp only [labels, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at pair
  rcases pair with h|h|h|h|h|h|h|h|h|h|h <;> obtain ⟨rfl,rfl⟩ := h <;> rfl

theorem execution {fr : Activation} {a : Values Value Reg.count} {m : Ram} {x y : Nat}
    (atoms : Atom.All Extracted.programImage (entryInputs a) m (Fn109f60.frameAt .l109f60 fr))
    (loaded : ∀ b ∈ Extracted.programImage, m[b.1]? = some b.2)
    (hx : x < domain.n) (hy : y < domain.n)
    (rx : Readable m fr.rsi 32) (ry : Readable m fr.rdx 32)
    (dst : Writable Extracted.programImage m fr.rdi 32) (above : fr.rsp.toNat + 8 ≤ fr.rdi.toNat)
    (apart : ∀ src ∈ [fr.rsi, fr.rdx],
      (src.toNat + 32 ≤ fr.rsp.toNat - 321 ∨ fr.rsp.toNat + 8 ≤ src.toNat) ∧
      (src.toNat + 32 ≤ fr.rdi.toNat ∨ fr.rdi.toNat + 32 ≤ src.toNat))
    (wx : WordsAt m fr.rsi 64 (scalarWords x)) (wy : WordsAt m fr.rdx 64 (scalarWords y)) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l109f60,a,m⟩,[]⟩ out ∧
      out.tag = some ⟨64,fr.ret⟩ ∧ Atom.All Extracted.programImage out.values out.store
        (Fn109f60.doneAt fr) ∧ ParseSignature.ArgumentWidths out.values ∧
      WordsAt out.store fr.rdi 64 (scalarWords ((x*y) % domain.n)) ∧
      RamWriteFrame m out.store [⟨fr.rsp.toNat - 321,321⟩,⟨fr.rdi.toNat,32⟩] := by
  obtain ⟨out, run, post⟩ := Split.mul (fr := fr) (a := entryInputs a) (m := m) atoms loaded (by intro h; contradiction)
    hx hy rx ry dst above apart wx wy
  have replay : program.Exec (dialect Extracted.programImage) ⟨⟨.l1099c0,entryInputs a,m⟩,[]⟩ out :=
    Relabel.exec blocks run rfl
  have body : program.Exec (dialect Extracted.programImage) ⟨⟨.l1099c0,a,m⟩,[]⟩ out := by
    cases replay with
    | done h => exact .done ((entryInputs_step ..).trans h)
    | next h tail => exact .next ((entryInputs_step ..).trans h) tail
  refine ⟨out, .next (next := ⟨⟨.l1099c0,a,m⟩,[]⟩) ?_ body, post⟩
  have args : a.select (RegMap.args (entryMap (live .l109f60)) 53) = a := by
    apply Vector.ext
    intro i hi
    rw [Values.getElem_select]
    exact congrArg (fun j : Fin 53 => a[j]) ((show ∀ j : Fin 53,
      (RegMap.args (entryMap (live .l109f60)) 53)[j] = j from by decide +kernel) ⟨i,hi⟩)
  exact congrArg (fun v => (Outcome.next ⟨⟨Label.l1099c0,v,m⟩,[]⟩ :
    Outcome Value Ram Label signature Reg.count)) args

end K256.Proofs.Verify.Core.ScalarProduct
