import Hkdf.Proofs.NewExpand.Extract.Finish.Call
import Hkdf.Proofs.NewExpand.Extract.Finish.Return
import Hkdf.Proofs.NewExpand.Extract.Frame
import Hkdf.Proofs.Standard.Finalize.Suffix.WithState

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Extract

open Hkdf.Spec Hkdf.Spec.Program Hkdf.Proofs.Common Hkdf.Proofs.Common.Machine
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

open CallFrame

theorem finish [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {salt : Option ByteArray} {ikm : ByteArray} (pre : ExtractPre initial boundary salt ikm) (state : Updated initial s boundary salt ikm) :
    ∃ t, CalleeResult initial t boundary 176 2264 ∧
      HmacAt t (initial.regValue .rdi + 32) (RFC5869.extract .sha256 salt ikm) ByteArray.empty := by
  obtain ⟨u, call⟩ := enter_finalize pre state
  obtain ⟨finalizePre, stackWithin, stackApart⟩ := finalize_regions pre call
  have messageSize : 64 + ikm.size < 2^61 := by
    have bound := pre.ikmBytes.1
    change (initial.regValue .rcx).toNat + ikm.size < 2^32 at bound
    omega
  obtain ⟨v, result, _, hmac⟩ :=
    Standard.Finalize.Suffix.finalize_correct_with_state finalizePre call.hmac messageSize
  have outRegion : registerRegion u .rdi 176 = registerRegion initial .rdi 176 := by
    simp only [registerRegion, call.outputPtr]
  let regions := #v[registerRegion initial .rdi 176, Stack.region initial 2264]
  have runningU : Running initial boundary regions u :=
    { call.toRunning with
      frame := frame_mono call.frame (by
        intro region member addr ha
        have eq : region = Stack.region initial 2264 := by simpa using member
        exact ⟨Stack.region initial 2264, by simp [regions], eq ▸ ha⟩) }
  have runningV := runningU.of_callee result (by
    intro region member addr ha
    have cases : region = registerRegion u .rdi 176 ∨ region = Stack.region u 1264 := by
      simpa using member
    rcases cases with rfl | rfl
    · exact ⟨registerRegion initial .rdi 176, by simp [regions], outRegion ▸ ha⟩
    · exact ⟨Stack.region initial 2264, by simp [regions], stackWithin addr ha⟩)
  have savedStart : (stackPtr initial - 48).toNat = (stackPtr initial).toNat - 48 :=
    stack_sub_toNat pre.call.stack (offset := 48) (by decide)
  have savedBound := stack_bounds pre.call.stack
  have savedInStack : ∀ a, (⟨(stackPtr initial - 48).toNat, 56⟩ : MemoryRegion).Contains a →
      (Stack.region initial 2264).Contains a := by
    intro a ⟨left, right⟩
    change (stackPtr initial - 48).toNat ≤ a at left
    change a < (stackPtr initial - 48).toNat + 56 at right
    rw [savedStart] at left right
    change (stackPtr initial).toNat - 2264 ≤ a ∧
      a < (Stack.region initial 2264).start + (Stack.region initial 2264).size
    rw [stack_region_end]
    constructor <;> omega
  have slots : (Component.mem (stackPtr initial - 48) 56).Agrees u v := by
    apply frame_agrees_of_disjoint result.frame (by rw [savedStart]; omega)
    intro region member
    have cases : region = registerRegion u .rdi 176 ∨ region = Stack.region u 1264 := by
      simpa using member
    rcases cases with rfl | rfl
    · rw [outRegion]
      exact fun a ha hb ↦ pre.call.writesStackDisjoint 0 a hb (savedInStack a ha)
    · exact stackApart
  have savedV := call.toSaved.of_agrees slots result.abi.2.2.1 result.abi.2.2.2
  have rip : v.RIP = 0x10fcf6 := result.rip.trans (congrArg ReturnBoundary.rip call.ret)
  have rsp : stackPtr v = base initial := result.rsp.trans (congrArg ReturnBoundary.rsp call.ret)
  obtain ⟨t, restored, mem⟩ := restore pre runningV savedV rip rsp
  refine ⟨t, restored, ?_⟩
  rw [call.outputPtr] at hmac
  exact hmac.of_copy (fun i hi ↦ by rw [mem])

end Hkdf.Proofs.NewExpand.Extract
