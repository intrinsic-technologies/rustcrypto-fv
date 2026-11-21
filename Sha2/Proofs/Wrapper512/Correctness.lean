import Sha2.Proofs.Common.SHA512.Compression.Correctness
import Sha2.Proofs.Wrapper512.Machine.Initialize
import Sha2.Proofs.Wrapper512.Machine.Contract
import Sha2.Proofs.Wrapper512.Absorb.Correctness
import Sha2.Proofs.Wrapper512.Finish.Run

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512

open X86.Machine
open Sha2.Proofs.Common.SHA512

theorem wrapper_contract [Bindings] (v : Variant) : WrapperContract v := by
  exact Machine.contract_of_stages Compression.block_correct
    (fun ctx => Machine.«initialize» ctx)
    (fun ctx => Absorb.step Compression.block_correct ctx)
    (fun body => Finish.run body)

end Sha2.Proofs.Wrapper512
