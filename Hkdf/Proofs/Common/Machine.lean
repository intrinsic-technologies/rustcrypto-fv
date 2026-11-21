import Hkdf.Proofs.Common.Machine.CallReturn
import Hkdf.Proofs.Common.Machine.Code
import Hkdf.Proofs.Common.Machine.Entry
import Hkdf.Proofs.Common.Machine.Interfaces
import Hkdf.Proofs.Common.Machine.MemoryFrame
import Hkdf.Proofs.Common.Machine.StackFrame
import Hkdf.Proofs.Common.Machine.StackRegion

namespace Hkdf.Proofs.Common.Machine

theorem preservesABI_trans {a b c : X86.Machine.RamState}
    (h₁ : Hkdf.Proofs.Program.PreservesABI a b)
    (h₂ : Hkdf.Proofs.Program.PreservesABI b c) :
    Hkdf.Proofs.Program.PreservesABI a c := by
  rcases h₁ with ⟨f₁, d₁, m₁, c₁⟩
  rcases h₂ with ⟨f₂, d₂, m₂, c₂⟩
  refine ⟨?_, d₂, m₂.trans m₁, c₂.trans c₁⟩
  intro register member
  exact (f₂ register member).trans (f₁ register member)

end Hkdf.Proofs.Common.Machine
