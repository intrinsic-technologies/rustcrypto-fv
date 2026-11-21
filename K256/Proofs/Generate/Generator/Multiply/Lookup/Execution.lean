import K256.Proofs.Generate.Generator.Multiply.Lookup.Initialize
import K256.Proofs.Generate.Generator.Multiply.Lookup.Scan
import K256.Proofs.Generate.Generator.Multiply.Lookup.Finish

namespace K256.Proofs.Generate.Generator.Multiply

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR K256.Proofs.Common.Field
  Standards.SECG.ECC

def TableAt (m : Ram) (base : BitVec 64) (p : Curve.Point) : Prop :=
  ∀ i : Fin 8, ∃ t : Projective, t.valid ∧ t.Stored m (base + BitVec.ofNat 64 (120 * i.val)) ∧
    t.value = Generate.Curve.tableEntry p (i.val + 1)

set_option linter.unusedVariables false in
theorem lookup {fr : Activation} {a : Registers} {m : Ram} {p : Curve.Point} {digit : Int}
    (atoms : Atom.All Extracted.programImage a m (Fn11c510.frameAt .l11c510 fr))
    (image : ∀ b ∈ Extracted.programImage, m[b.1]? = some b.2)
    (src : Readable m fr.rsi 960) (dst : Writable Extracted.programImage m fr.rdi 120)
    (srcAbove : fr.rsp.toNat + 8 ≤ fr.rsi.toNat) (dstAbove : fr.rsp.toNat + 8 ≤ fr.rdi.toNat)
    (apart : fr.rdi.toNat + 120 ≤ fr.rsi.toNat ∨ fr.rsi.toNat + 960 ≤ fr.rdi.toNat)
    (table : TableAt m fr.rsi p) (bounds : -8 ≤ digit ∧ digit ≤ 8)
    (index : fr.rdx.setWidth 8 = BitVec.ofInt 8 digit) :
    ∃ out, ∃ t : Projective, program.Exec (dialect Extracted.programImage) ⟨⟨.l11c510, a, m⟩, []⟩ out ∧
      out.tag = some ⟨64, fr.ret⟩ ∧ Atom.All Extracted.programImage out.values out.store
        (Fn11c510.doneAt fr) ∧ ParseSignature.ArgumentWidths out.values ∧
      t.valid ∧ t.Stored out.store fr.rdi ∧ t.value = Generate.Curve.selectDigit p digit ∧
      RamWriteFrame m out.store [⟨(fr.rsp - 0x1f0).toNat, 0x1f0⟩, ⟨fr.rdi.toNat,120⟩] := by
  obtain ⟨b, n, reach, init⟩ := Lookup.startScan atoms image bounds index
  have scan (i : Nat) (hi : i ≤ 8) :
      ∃ b n t, Reaches .l11c510 a m (Lookup.stage i) b n ∧ Lookup.Scanning fr m digit i b n t ∧
        t.valid ∧ t.value = Generate.Curve.tableEntry p (if digit.natAbs ≤ i then digit.natAbs else 0) := by
    induction i with
    | zero =>
      refine ⟨_, _, _, reach, init, identity_valid, ?_⟩
      by_cases z : digit.natAbs ≤ 0
      · simp only [Nat.le_zero.mp z, Nat.le_refl, ite_true]
        exact identity_value
      · simpa only [z, ite_false] using (show identity.value = Generate.Curve.tableEntry p 0 from identity_value)
    | succ i ih =>
      have stepIndex : i < 8 := by omega
      obtain ⟨b, n, t, reach, state, valid, value⟩ := ih (by omega)
      obtain ⟨u, uv, us, ue⟩ := table ⟨i, stepIndex⟩
      obtain ⟨c, o, call, result⟩ := Lookup.scanEntry ⟨i, stepIndex⟩ state src srcAbove bounds us
      refine ⟨c, o, _, reach.trans call, result, ?_, ?_⟩
      · split <;> assumption
      · by_cases eq : digit.natAbs = i + 1
        · simpa only [eq, ite_true, Nat.le_refl] using ue
        · have order : (digit.natAbs ≤ i + 1) = (digit.natAbs ≤ i) := propext (by omega)
          simpa only [eq, ite_false, order] using value
  obtain ⟨c, o, t, path, state, valid, value⟩ := scan 8 (by decide)
  obtain ⟨out, run, tag, done_, widths, point, writes⟩ := Lookup.finish state dst dstAbove
  have h8 : digit.natAbs ≤ 8 := by omega
  simp only [h8, ite_true] at value
  refine ⟨out, _, Program.Exec.of_sem (path.exec run.sem), tag, done_, widths, ?_, point, ?_, writes⟩
  · split <;> first | exact Projective.neg_valid valid | exact valid
  · by_cases neg : digit < 0 <;> simp [Generate.Curve.selectDigit, neg, Projective.neg_value, value]

end K256.Proofs.Generate.Generator.Multiply
