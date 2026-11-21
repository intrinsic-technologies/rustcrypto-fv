import P256.Proofs.Verifying.Core.Interface
import P256.Proofs.Program.ScalarFrame.Memory
import P256.Proofs.Program.ScalarFrame.Output
import P256.Proofs.Common.Encoding.Serialize.Convert.SavePointer

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Output

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Program ScalarFrame
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem after_write [Bindings] {s t u : RamState} {boundary : ReturnBoundary} {off : Nat}
    (pre : Core.Pre s boundary) (state : Core.Frame s t) (ready : ReadyToStep u)
    (agrees : AgreesExcept [.mem (s.regValue .rdi + BitVec.ofNat 64 off) 8, .reg 0, .reg 1, .rip] t u)
    (bound : off + 8 ≤ 24) : Core.Frame s u := by
  apply state.after_effect pre.toCalleePre (by decide) ready agrees
  · intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    · exact ⟨registerRegion s .rdi 24, by simp, output_contains pre.toCalleePre bound ha⟩
    · exact ha.elim
    · exact ha.elim
    · exact ha.elim
  · simp

theorem preserves_error {s t : RamState} {address : BitVec 64}
    (frame : AgreesExcept [.mem address 8, .reg 0, .reg 1, .rip] s t) :
    memLoad t.external (address + 8) 64 = memLoad s.external (address + 8) 64 := by
  apply P256.Proofs.Common.Encoding.Serialize.read_mem_of_agrees frame
  intro i hi c hc hv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl
  · obtain ⟨j, hj, he⟩ := hv
    have apart : OffsetsApart 0 8 8 8 := by unfold OffsetsApart; decide +kernel
    apply apart.ne address hj hi (by decide)
    change address + 0#64 + BitVec.ofNat 64 j = _
    rw [BitVec.add_zero]
    exact he.symm
  · exact hv.elim
  · exact hv.elim
  · exact hv.elim

end P256.Proofs.Verifying.Core.Output
