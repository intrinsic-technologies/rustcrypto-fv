import Hkdf.Proofs.NewExpand.Extract.Normalize
import Hkdf.Proofs.NewExpand.Extract.Initialize
import Hkdf.Proofs.NewExpand.Extract.Update
import Hkdf.Proofs.NewExpand.Extract.Finish

namespace Hkdf.Proofs.NewExpand

theorem extract_correct [X86.Machine.Bindings] : ExtractContract := by
  intro initial boundary salt ikm pre
  obtain ⟨normalized, key⟩ := Extract.normalize pre
  obtain ⟨initialized, context⟩ := Extract.initialize_hmac pre key
  obtain ⟨updated, message⟩ := Extract.update pre context
  exact Extract.finish pre message

end Hkdf.Proofs.NewExpand
