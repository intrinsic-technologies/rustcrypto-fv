import K256.Proofs.Ecdh.Wrapper.State
import K256.Proofs.Ecdh.Wrapper.AffineReturn
import K256.Proofs.Ecdh.Affine
import K256.Proofs.Ecdh.Transfer
import K256.Proofs.Ecdh.CallSite
import K256.Proofs.Ecdh.Scalar.Calls

namespace K256.Proofs.Ecdh.Wrapper

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine Ecdh.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1

theorem convertProduct {s : RamState} {secret key : ByteArray} {p : Curve.Point}
    {a : Arguments} {m : Ram}
    (call : ValidCall ecdhDiffieHellman s [secret, key]) (state : Caller s a m)
    (r12 : a[12] = ⟨64, localSp s + 0x158⟩)
    (source : Generate.Generator.Affine.ProjectiveAt m (localSp s + 0x158) p) :
    ∃ b n, Reaches .l101afa a m .l101b0d b n ∧ Scalar.Memory s n ∧
      b[4].get 64 = localSp s ∧ b[14].get 64 = localSp s + 4184 ∧
      b[3] = ⟨64, s.regValue .rdi⟩ ∧ b[22] = ⟨1, 0⟩ ∧ Affine.XAt n (localSp s + 4184) p := by
  have entry := affineEntry call state.frame state.df (fun i hi => state.widths i (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at *
    omega)) state.mxcsr state.ftw state.fcw
  have src := affineSourceAt source (0x101b0d : BitVec 64)
  rw [← affineSource s a m] at src
  obtain ⟨out, child, tag, done_, writes, x⟩ := Affine.execution entry src
  have run := Ecdh.Transfer.generateExec (dst := .l10fe50) (by decide) rfl child
  have guard := (callSite call state.toMemory 6160 (by decide) (by decide)
    0x101afa bytes_l101afa 14 5
    (fun v hv => Common.fnCode_subset_programImage v (code_l101afa v hv))
    (by decide) 0x101b0d).1
  change StoreOk Extracted.programImage m (returnSlot s) 8 0x101b08 5 at guard
  rw [← localSp_sub_eight] at guard
  have push := affineCallBlock (sp := localSp s) (congrArg (Value.get 64) state.rsp)
    (congrArg (Value.get 64) r12) guard
  rw [localSp_sub_eight] at push
  obtain ⟨saved, frame⟩ := affineReturnFrame call state.saved state.frame writes
  simp only [Generate.LIR.Fn10fe50.doneAt, Atom.All, Atom.Holds, Atom.gpr,
    Fin.getElem_fin] at done_
  obtain ⟨rsp, df, rbx, _, _, _, r14, _⟩ := done_
  rw [affineDest] at x
  refine ⟨out.values, out.store, Scalar.resumeCall push run tag, ⟨frame, saved⟩, ?_, ?_, ?_, df, x⟩
  · apply (congrArg (Value.get 64) rsp).trans
    change s.regValue .rsp - 6160 + 8 = s.regValue .rsp - 6152
    bv_omega
  · apply (congrArg (Value.get 64) r14).trans
    change (affineArgs a (localSp s))[14].get 64 = _
    simp [affineArgs]
  · apply rbx.trans
    simp [affineActivation, childActivation, affineArgs, state.output]

end K256.Proofs.Ecdh.Wrapper
