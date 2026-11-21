import Sha2.Proofs.Wrapper.Absorb.Short
import Sha2.Proofs.Wrapper.Absorb.Empty
import Sha2.Proofs.Wrapper.Absorb.Fill
import Sha2.Proofs.Wrapper.Absorb.Blocks.Run
import Sha2.Proofs.Wrapper.Absorb.Next

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper.Absorb

open Sha2.Spec Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem absorb_one {v : Variant} [Bindings] {initial s : RamState} {inputs : Array Input} {index : Nat}
    (ctx : Context (v := v) initial inputs) (state : LoopState (v := v) initial s inputs index) :
    ∃ t, LoopState (v := v) initial t inputs (index+1) ∨
      (Buffered (v := v) initial t (message inputs) ∧ t.RIP=(v.pc 0x1bb)) := by
  obtain ⟨a,loaded⟩ := load_slice ctx state
  obtain ⟨b,selected,ripB⟩ := select_size ctx loaded
  by_cases small : (inputs[index]'state.remaining).bytes.size < 64-(prefixMessage inputs index).size%64
  · have rip : b.RIP=(v.pc 0xa0) := by simpa only [small,ite_true] using ripB
    obtain ⟨c,buffered,ripC,indexC,countC⟩ := short ctx selected.toSliceState rip small
    exact advance_iteration ctx buffered false ripC indexC countC state.remaining
  · have rip : b.RIP=(v.pc 0xfe) := by simpa only [small,ite_false] using ripB
    obtain ⟨c,selectedC,ripC⟩ := select_empty ctx selected rip
    have pending : ∃ u consumed, Blocks.Input (v := v) initial u inputs index consumed ∧
        (u.RIP=(v.pc 0x14c) ∨ u.RIP=(v.pc 0x1b0)) := by
      by_cases zero : (prefixMessage inputs index).size%64=0
      · have entry : c.RIP=(v.pc 0x1ad) := by simpa only [zero,ite_true] using ripC
        obtain ⟨u,inputU,ripU⟩ := empty ctx selectedC entry zero
        exact ⟨u,0,inputU,Or.inr ripU⟩
      · have entry : c.RIP=(v.pc 0x107) := by simpa only [zero,ite_false] using ripC
        obtain ⟨u,inputU,ripU⟩ := fill ctx selectedC entry (by omega)
        exact ⟨u,_,inputU,Or.inl ripU⟩
    obtain ⟨u,consumed,inputU,ripU⟩ := pending
    obtain ⟨v,result⟩ := Blocks.run ctx inputU ripU
    exact advance_iteration ctx result.toBuffered true result.rip
      result.indexRegister result.countRegister state.remaining

theorem absorb_all {v : Variant} [Bindings] {initial s : RamState} {inputs : Array Input} {index : Nat}
    (ctx : Context (v := v) initial inputs) (state : LoopState (v := v) initial s inputs index) :
    ∃ t, Buffered (v := v) initial t (message inputs) ∧ t.RIP=(v.pc 0x1bb) := by
  generalize remainingEq : inputs.size-index = remaining
  induction remaining generalizing s index with
  | zero => have := state.remaining; omega
  | succ remaining ih =>
    obtain ⟨t,more|done⟩ := absorb_one ctx state
    · exact ih more (by have := state.remaining; omega)
    · exact ⟨t,done⟩

end Sha2.Proofs.Wrapper.Absorb
