import K256.Proofs.Generate.Curve
import K256.Proofs.Ecdh.Multiply.Endomorphism.Machine
import K256.Proofs.Ecdh.Multiply.Endomorphism.Reduction

namespace K256.Proofs.Generate.Generator.Multiply.Prepare

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR
  Standards.SECG.DomainParameters.Secp256k1

open Curve.Group.CurveArithmetic K256.Proofs.Common.Field Lean.Grind

private def endomorphismFactor : Fp :=
  ⟨0x7ae96a2b657c07106e64479eac3434e99cf0497512f58995c1396c28719501ee, by decide⟩

private def scalePeer (b : Fp) (p : Projective) : Projective := ⟨p.x * b, p.y, p.z⟩

private theorem scalePeer_valid {p : Projective} (h : p.valid) {b : Fp}
    (cube : b * b * b = 1) (nonzero : b ≠ 0) : (scalePeer b p).valid := by
  obtain ⟨eqn, nz⟩ := h
  dsimp only [scalePeer, Projective.valid]
  refine ⟨?_, nz.imp (fun hx he => (Field.of_mul_eq_zero he).elim hx nonzero) id⟩
  have e : (p.x * b) * (p.x * b) * (p.x * b) = p.x * p.x * p.x * (b * b * b) := by grind only
  rwa [e, cube, Semiring.mul_one]

private theorem scaleCoordinates (x y k : Fp) (z : Nat) :
    (if z = 0 then .infinity else .affine ((x * endomorphismFactor) * k).val (y * k).val) =
    Curve.endomorphism (if z = 0 then .infinity else .affine (x * k).val (y * k).val) := by
  by_cases hz : z = 0
  · simp only [hz, ite_true, Curve.endomorphism]
  · simp only [ite_eq_right hz, Curve.endomorphism, Standards.SECG.ECC.Curve.Point.affine.injEq, and_true]
    have swap (a b c : Fp) : a * b * c = a * c * b := by grind only
    exact congrArg Fin.val (swap x endomorphismFactor k)

private theorem valueScale (x y z : Fp) :
    Affine.toAffine (x * endomorphismFactor) y z = Curve.endomorphism (Affine.toAffine x y z) :=
  scaleCoordinates x y (Affine.inverse z) z.val

private theorem scalePeer_value (p : Projective) :
    (scalePeer endomorphismFactor p).value = Curve.endomorphism p.value := by
  cases p with
  | mk x y z => exact valueScale x y z

private theorem beta_repr (x : Limbs) {v : Fp} (hx : FieldRepr x v 1) :
    FieldRepr (Endomorphism.betaMulWords x) (v * endomorphismFactor) 1 := by
  rw [Endomorphism.betaMulWords_eq x hx]
  exact mulWords_repr x Endomorphism.betaLimbs v endomorphismFactor (hx.mono (by decide))
    (by unfold FieldRepr; decide +kernel)

private theorem peerResult {m : Ram} {dst : Word} {p : Projective} (valid : p.valid)
    {x y z : Limbs} (wx : WordsAt m dst 64 (Endomorphism.betaMulWords x))
    (wy : WordsAt m (dst + 40) 64 y) (wz : WordsAt m (dst + 80) 64 z)
    (rx : FieldRepr x p.x 1) (ry : FieldRepr y p.y 1) (rz : FieldRepr z p.z 1) :
    ∃ q : Projective, q.valid ∧ q.Stored m dst ∧ q.value = Curve.endomorphism p.value := by
  cases p with
  | mk px py pz =>
    refine ⟨_, scalePeer_valid valid (b := endomorphismFactor) (by decide +kernel) (by decide +kernel),
      ?_, scalePeer_value _⟩
    exact ⟨_, _, _, wx, wy, wz, beta_repr x rx, ry, rz⟩

set_option linter.unusedVariables false in
theorem peerEndomorphismCall {fr : Activation} {a : Registers} {m : Ram}
    (atoms : Atom.All Extracted.programImage a m (Fn10e010.frameAt .l10e010 fr))
    (loaded : ∀ v ∈ Extracted.programImage, m[v.1]? = some v.2)
    (src : Readable m fr.rsi 120) (dst : Writable Extracted.programImage m fr.rdi 120)
    (aboveSrc : fr.rsp.toNat + 8 ≤ fr.rsi.toNat) (aboveDst : fr.rsp.toNat + 8 ≤ fr.rdi.toNat)
    (apart : fr.rsi.toNat + 120 ≤ fr.rdi.toNat ∨ fr.rdi.toNat + 120 ≤ fr.rsi.toNat)
    {peer : Projective} (valid : peer.valid) (input : peer.Stored m fr.rsi) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l10e010, a, m⟩, []⟩ out ∧
      out.tag = some ⟨64,fr.ret⟩ ∧ Atom.All Extracted.programImage out.values out.store (Fn10e010.doneAt fr) ∧
      ParseSignature.ArgumentWidths out.values ∧
      RamWriteFrame m out.store [⟨fr.rsp.toNat - 128,128⟩,⟨fr.rdi.toNat,120⟩] ∧
      ∃ p : Projective, p.valid ∧ p.Stored out.store fr.rdi ∧ p.value = Curve.endomorphism peer.value := by
  obtain ⟨x, y, z, wx, wy, wz, rx, ry, rz⟩ := input.coordinates
  obtain ⟨out, run, tag, done_, widths, frame, wx', wy', wz'⟩ :=
    Endomorphism.runPeer atoms src dst aboveSrc aboveDst apart wx wy wz
  exact ⟨out, run, tag, done_, widths, frame, peerResult valid wx' wy' wz' rx ry rz⟩

end K256.Proofs.Generate.Generator.Multiply.Prepare
