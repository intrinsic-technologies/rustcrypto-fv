import P256.Proofs.Sec1Serialize.Composition
import P256.Proofs.Sec1Serialize.Tail.Prepare
import P256.Proofs.Sec1Serialize.Tail.Initialize
import P256.Proofs.Sec1Serialize.Tail.Selection
import P256.Proofs.Sec1Serialize.Tail.Finish

set_option autoImplicit false

namespace P256.Proofs.Sec1Serialize

open P256.Spec P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

theorem tail_correct [bindings : Bindings] : TailCorrect bindings := by
  intro s t boundary x y infinity pre state rip converted hx hy rdi compress saved flag run
  obtain ⟨u, encoded⟩ := prepare_encoding pre state rip converted hx hy rdi compress saved flag run
  obtain ⟨v, initialized⟩ := finish_preparation pre encoded
  obtain ⟨w, selected⟩ := select_bytes pre initialized
  exact finish_serialization pre selected

end P256.Proofs.Sec1Serialize
