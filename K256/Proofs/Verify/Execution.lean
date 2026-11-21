import K256.Proofs.Common.StatusExecution
import K256.Proofs.Verify.Wrapper.ParseSignature
import K256.Proofs.Verify.Wrapper.HashUpdate
import K256.Proofs.Verify.Wrapper.HashFinalize
import K256.Proofs.Verify.Wrapper.Projective
import K256.Proofs.Verify.Wrapper.Verification
import K256.Proofs.Verify.Hash.Compression.Execution
import K256.Proofs.Verify.LIR

namespace K256.Proofs.Verify

open K256.Spec K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift

theorem execution [bindings : Bindings] (stride : UnitStringStride bindings)
    {initial : RamState} {key message signature : ByteArray}
    (call : ValidCall verifyingKeyVerify initial [key, message, signature]) :
    ∃ (program : Lifted) (entry : program.Label) (out : Output Value Ram Reg.count),
      program.address entry = verifyingKeyVerify.entryAddress ∧
      (∀ l, LiftedBlock Extracted.programImage program l) ∧
      (∀ r ∈ [0, 3, 4, 5, 12, 13, 14, 15, 22], Live program.retLive r) ∧
      program.program.Exec (dialect Extracted.programImage) ⟨program.locationOf entry initial, []⟩ out ∧
      Common.Returned initial #v[Stack.region initial verifyingKeyVerify.minStackBytes] out ∧
      out.values[0] = ⟨64, if Ecdsa.verifies key message signature then 0 else 1⟩ := by
  obtain ⟨p, r, s, keyOk, sigOk⟩ := Wrapper.decodedInputs call
  obtain ⟨a, m, keyRun, atoms, mem, widths, tag, point⟩ := Wrapper.keyPrefix call keyOk
  obtain ⟨b, n, sigRun, input⟩ := Wrapper.parseSignature call sigOk atoms mem widths tag point
  obtain ⟨c, t, update, buffer⟩ := Wrapper.hashUpdate Hash.Compression.execute call input
  obtain ⟨d, u, finalize, hash⟩ := Wrapper.hashFinalize Hash.Compression.execute call buffer
  obtain ⟨e, w, project, prepared⟩ := Wrapper.makeProjective call keyOk hash
  obtain ⟨out, tailRun, frame, status⟩ := Wrapper.verificationSuffix call keyOk sigOk prepared
  refine ⟨LIR.lifted, .l102fc0, out, rfl, LIR.blocks stride _ Common.fnCode_subset_programImage,
    ?_, Program.Exec.of_sem ((keyRun.trans (sigRun.trans (update.trans (finalize.trans project)))).exec
      tailRun.sem), frame, ?_⟩
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide
  · rw [verifies_of_decoded keyOk sigOk]
    exact status

end K256.Proofs.Verify
