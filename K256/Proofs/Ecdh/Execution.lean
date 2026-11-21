import K256.Proofs.Ecdh.Wrapper.Scalar
import K256.Proofs.Ecdh.Wrapper.Decode
import K256.Proofs.Ecdh.Wrapper.Convert
import K256.Proofs.Ecdh.Wrapper.Pair
import K256.Proofs.Ecdh.Wrapper.Tables
import K256.Proofs.Ecdh.Wrapper.Multiply
import K256.Proofs.Ecdh.Wrapper.Affine
import K256.Proofs.Ecdh.Curve
import K256.Proofs.Ecdh.Output

namespace K256.Proofs.Ecdh

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine Ecdh.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1

open Wrapper

theorem execution {s : RamState} {secret key : ByteArray}
    (call : ValidCall ecdhDiffieHellman s [secret, key]) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨lifted.locationOf .l101660 s, []⟩ out ∧
      Common.Returned s (regions s) out ∧ (outputRegion ecdhDiffieHellman s).HasBytes
        out.store (K256.Spec.Secp256k1.sharedSecret secret key) := by
  have accepted : (K256.Spec.Secp256k1.groupPoint key).isSome = true := call.inputsHoldValues.2.1
  obtain ⟨p, hp⟩ := Option.isSome_iff_exists.mp accepted
  have onCurve := Curve.groupPoint_onCurve key p hp
  obtain ⟨d, a, m, prefixPath, hs, pos, bound, state, ptr, words⟩ := scalarPrefix call
  obtain ⟨b, n, decodePath, state, words, point⟩ := decodePeer call state ptr words hp
  obtain ⟨c, q, peer, convertPath, state, ptr, words, stored, valid, value⟩ :=
    convertPeer call state words point onCurve
  obtain ⟨e, r, pairPath, state, copy, pair, words, stored⟩ := copyPair call state ptr words stored
  obtain ⟨f, t, tablePath, state, pair, table, words, stored⟩ :=
    initializeTables call state copy pair words stored
  obtain ⟨g, u, mulPath, state, ptr, product⟩ := multiplyPeer call state pair table words stored valid pos bound
  change Generate.Generator.Affine.ProjectiveAt u _ (Curve.peerWindow peer.value d) at product
  rw [value, Curve.peerWindow_eq_scalarMul p onCurve d bound] at product
  obtain ⟨j, v, affinePath, mem, sp, r14, bx, df, x⟩ := convertProduct call state ptr product
  obtain ⟨out, ret, post, bytes⟩ := Output.execution call mem.frame mem.saved sp r14 bx df x
  rw [Curve.sharedSecret_eq_x secret key p d hs hp]
  have path := prefixPath.trans <| decodePath.trans <| convertPath.trans <|
    pairPath.trans <| tablePath.trans <| mulPath.trans affinePath
  exact ⟨out, Program.Exec.of_sem (path.exec ret.sem), post, bytes⟩

end K256.Proofs.Ecdh
