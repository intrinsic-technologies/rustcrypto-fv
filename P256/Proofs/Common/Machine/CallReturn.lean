import X86Proofs.Program.Execution

set_option autoImplicit false

namespace P256.Proofs.Common.Machine

open Prelude X86 X86.Machine X86.UserProcess X86Proofs

macro "component_not_mem" : tactic => `(tactic| first
  | (simp; done)
  | (simp [*]; done)
  | (intro h; repeat' (first | cases h | (rename_i h; cases h))))

end P256.Proofs.Common.Machine
