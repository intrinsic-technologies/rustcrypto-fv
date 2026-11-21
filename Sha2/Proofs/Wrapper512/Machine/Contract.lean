import Sha2.Proofs.Common.SHA512.Compression.Interface
import Sha2.Proofs.Wrapper512.API
import Sha2.Proofs.Wrapper512.Absorb.Contract
import Sha2.Proofs.Wrapper512.Finish.Contract

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper512.Machine

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess
  X86Proofs
open Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.SHA512
open Sha2.Proofs.Wrapper512

theorem dispatch_of_stages [Bindings] {v : Variant}
    (initializer : ∀ {initial : RamState} {inputs : Array Input},
      Context v initial inputs →
        ∃ s, Buffered v initial s ByteArray.empty ∧
          s.RIP = v.pc 0xd0 ∧ s.regValue .rsi = BitVec.ofNat 64 inputs.size)
    (absorber : ∀ {initial : RamState} {inputs : Array Input},
      Context v initial inputs → Absorb.Step v initial inputs) :
    DispatchContract v := by
  exact Absorb.contract_of_step initializer absorber

theorem finish_of_stages [Bindings] {v : Variant}
    (body : Compression.BlockCorrect)
    (finisher : ∀ (_body : Compression.BlockCorrect)
      {initial s : RamState} {inputs : Array Input},
      Context v initial inputs → Buffered v initial s (message inputs) → s.RIP = v.pc 0x218 →
        ∃ final, FinishResult v initial final inputs) :
    FinishContract v := by
  exact Finish.finishContract (finisher body)

theorem contract_of_stages [Bindings] {v : Variant}
    (body : Compression.BlockCorrect)
    (initializer : ∀ {initial : RamState} {inputs : Array Input},
      Context v initial inputs →
        ∃ s, Buffered v initial s ByteArray.empty ∧
          s.RIP = v.pc 0xd0 ∧ s.regValue .rsi = BitVec.ofNat 64 inputs.size)
    (absorber : ∀ {initial : RamState} {inputs : Array Input},
      Context v initial inputs → Absorb.Step v initial inputs)
    (finisher : ∀ (_body : Compression.BlockCorrect)
      {initial s : RamState} {inputs : Array Input},
      Context v initial inputs → Buffered v initial s (message inputs) → s.RIP = v.pc 0x218 →
        ∃ final, FinishResult v initial final inputs) :
    WrapperContract v := by
  exact WrapperContract.of_parts (dispatch_of_stages initializer absorber)
    (finish_of_stages body finisher)

theorem run_of_stages [Bindings] {v : Variant}
    (body : Compression.BlockCorrect)
    (initializer : ∀ {initial : RamState} {inputs : Array Input} ,
      Context v initial inputs →
        ∃ s, Buffered v initial s ByteArray.empty ∧
          s.RIP = v.pc 0xd0 ∧ s.regValue .rsi = BitVec.ofNat 64 inputs.size)
    (absorber : ∀ {initial : RamState} {inputs : Array Input},
      Context v initial inputs → Absorb.Step v initial inputs)
    (finisher : ∀ (_body : Compression.BlockCorrect)
      {initial s : RamState} {inputs : Array Input},
      Context v initial inputs → Buffered v initial s (message inputs) → s.RIP = v.pc 0x218 →
        ∃ final, FinishResult v initial final inputs)
    {initial : RamState} {inputs : Array Input}
    (ctx : Context v initial inputs) :
    ∃ final, FinishResult v initial final inputs := by
  exact (contract_of_stages body initializer absorber finisher).run ctx

end Sha2.Proofs.Wrapper512.Machine
