import K256.Proofs.Common.Invert.Correct
import K256.Proofs.Verify.Core.Scalars.Inverse.ModularShift.Call
import K256.Proofs.Verify.Core.Scalars.Inverse.ModularShift.Subtract
import K256.Proofs.Verify.Core.Scalars.Inverse.ModularShift.Select
import K256.Proofs.Verify.Core.Scalars.Inverse.Correction.Result

namespace K256.Proofs.Verify.Core.Scalars.Inverse

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
open K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Field K256.Proofs.Verify.LIR

open K256.Proofs.Generate.Generator.Affine.Invert.Core (CalleeFrame CalleeResult LinearArgs signedAt)
open Common.Invert.ModularShift (wideValue)
open Correction
open Standards.SECG.DomainParameters.Secp256k1
open Correction.Arithmetic

theorem modularShift {a : Registers} {m : Ram} {sp dst ret : Word} {x y : Int} {u v : Word} {shift : Nat}
    (fr : CalleeFrame a m sp dst ret 304 33)
    (args : LinearArgs a m sp dst 304 33 x y u v)
    (hs : a[9].get 32 = BitVec.ofNat 32 shift) (pos : 0 < shift) (hshift : shift ≤ 62)
    (stackArgs : Readable m (sp + 8) 16)
    (argHigh : sp.toNat + 24 ≤ 2^32)
    (argApart : dst.toNat + 33 ≤ sp.toNat ∨ sp.toNat + 24 ≤ dst.toNat)
    (modPtr : memLoad m (sp + 8) 64 = 0x2021a0)
    (inv : memLoad m (sp + 16) 64 = 0xb4f20099aa774ec1)
    (bound : (x * u.toInt + y * v.toInt).natAbs < 2^shift * domain.n) :
    ∃ out r, CalleeExec .l108980 a m out ∧ CalleeResult a m sp dst ret 304 33 out ∧
      signedAt out.store dst r ∧ r.natAbs < domain.n ∧
      ((2 : Int)^shift * r) % domain.n = (x * u.toInt + y * v.toInt) % domain.n := by
  obtain ⟨p, b, mb, params, shiftEq, ⟨neg, sign, mag⟩, call, tf, atoms⟩ :=
    ModularShift.linearCall fr args hs pos hshift stackArgs argHigh argApart modPtr inv
  obtain ⟨c, mc, subtract, tc, ac⟩ :=
    ModularShift.subtract fr params tf stackArgs argHigh argApart (shiftEq ▸ pos) (shiftEq ▸ hshift) atoms
  obtain ⟨out, select, frame, words, byte⟩ :=
    ModularShift.select fr tc stackArgs argHigh argApart (shiftEq ▸ pos) (shiftEq ▸ hshift) ac
  have magnitude : K256.Proofs.Common.Invert.LinearCombination.wideValue p.magnitude =
      wideValue (wideLow p) (wideHigh p) := by
    simp only [K256.Proofs.Common.Invert.LinearCombination.wideValue,
      K256.Proofs.Common.Invert.LinearCombination.packFive, Vector.getElem_map, wideValue, wideLow,
      wideHigh, K256.Proofs.Common.Invert.LinearCombination.Limbs.toNat]
    omega
  rw [magnitude] at mag
  have spec := result_correct p neg _ sign mag (shiftEq ▸ hshift) (by rw [params, order_modulus, shiftEq]; exact bound)
  rw [params, order_modulus, shiftEq] at spec
  obtain ⟨signEq, small, congr⟩ := spec
  refine ⟨out, _, Program.Exec.of_sem (call.exec (subtract.exec select.sem)), frame, ⟨_, _, words, byte.trans signEq, ?_⟩,
    small, congr⟩
  rw [Common.Invert.Correct.limbs_value]

end K256.Proofs.Verify.Core.Scalars.Inverse
