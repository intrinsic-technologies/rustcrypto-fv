import Hkdf.Proofs.NewExpand.Wrapper.Copy.State
import Hkdf.Proofs.NewExpand.Wrapper.Copy.Memcpy.Setup
import Hkdf.Proofs.NewExpand.Wrapper.Prologue.Call
import Hkdf.Proofs.NewExpand.Wrapper.CalleeFrame
import Hkdf.Proofs.Common.Memory.Copy
import Hkdf.Proofs.Common.Memory.Pointers

namespace Hkdf.Proofs.NewExpand.Wrapper.Copy

open Hkdf.Spec Hkdf.Spec.Program Hkdf.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common Hkdf.Proofs.Common.Machine Hkdf.Proofs.Common.CallFrame

private abbrev copyLayout : StackCallLayout hkdfSha256NewExpandMinStackBytes 144 144 0 :=
  ⟨368, 328, 184, by decide, by decide, by decide, by decide, by decide, by decide, .inl (by decide)⟩

theorem copyKey [bindings : Bindings]
    {initial : RamState} {salt : Option ByteArray} {ikm info : ByteArray} {length : Nat}
    (hCall : ValidDeriveKeyCall Extracted.hkdfSha256NewExpandAddress
      hkdfSha256NewExpandMinStackBytes initial salt ikm info length)
    {s : RamState} (start : ExtractReturn initial s (RFC5869.extract .sha256 salt ikm))
    (stride : UnitStringStride bindings) :
    ∃ t, Copied initial t (RFC5869.extract .sha256 salt ikm) := by
  have outside := outerBoundary hCall.returnAddress
  let stack := Stack.region initial hkdfSha256NewExpandMinStackBytes
  have stackAvoid := (hCall.stackSeparation.2 stack (by simp [stack])).2
  have avoids : ∀ r ∈ #v[stack], r.Avoids InProgram := by
    intro r hr
    obtain rfl := Vector.mem_singleton.mp hr
    exact fun a ha h ↦ stackAvoid a ha (.inl h)
  obtain ⟨_, u, run, ready, _, setup⟩ := Memcpy.setup_run _ outside s
    (supportedMachine_readyToStep start.run.machine) (Memcpy.setup_code start.run.loaded) start.rip
  have noMem : ∀ c ∈ (Memcpy.setupEffect s).components, ∀ a, ¬ c.Covers a := by
    simp [Memcpy.setupEffect, Effect.components, Component.Covers]
  have runningU := start.run.of_agrees run ready setup.agrees
    (fun c hc a ha ↦ (noMem c hc a ha).elim) avoids (by simp [Memcpy.setupEffect, Effect.components])
  have values := setup.writes
  change u.regValue .rsi = stackPtr s + 32 ∧ u.regValue .r13 = stackPtr s + 176 ∧
    u.regValue .rdx = 144 ∧ u.regValue .rdi = stackPtr s + 176 at values
  have source : stackPtr s + 32 = stackPtr initial - 328 := by
    rw [start.rsp, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.sub_eq_add_neg]
    rfl
  have dest : stackPtr s + 176 = stackPtr initial - 184 := by
    rw [start.rsp, BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.sub_eq_add_neg]
    rfl
  have rspU : stackPtr u = stackPtr initial - 360 :=
    (setup.agrees.read (n := 64) (r := 4) (by simp [Memcpy.setupEffect, Effect.components])).trans start.rsp
  have push : pushAddr u = stackPtr initial - 368 := by
    rw [pushAddr, rspU, BitVec.sub_sub]
    rfl
  have pointer := Common.Memory.memcpy_pointer runningU.loaded
  have target : callMemPtr 0x10201f (.rip 0xff2f3) u = 0x10dd60 := pointer.2
  obtain ⟨a, runningA, call, boundaryA⟩ := runningU.call_stack
    hCall.stack stackAvoid (depth := 360) rspU (by decide) (by decide)
    0x201f 6 (by decide) setup.rip
    (call_m64_effect_step 0x10201f (.rip 0xff2f3) (by decide) rfl rfl)
    (programText_slice (programLoaded_codeIn runningU.loaded) 0x201f
      (encodeCallM64 (.rip 0xff2f3)) (by decide +kernel) (by decide +kernel))
    (fun pushed ↦ ⟨⟨pushed, by rw [target]; decide⟩, pointer.1⟩)
    (by rw [target]; exact boundary_ne_program outside (inProgram_of_textOffset 0xdd60 (by decide)))
  have rspA : stackPtr a = stackPtr initial - 368 := call.writes.1.trans push
  have callFrame : AgreesExcept [.reg 4, .mem (stackPtr initial - 368) 8, .rip] u a := by
    simpa only [callEffect, pushEffect_components, push] using call.agrees
  have inputA : a.regValue .rsi = stackPtr initial - 328 :=
    (callFrame.read (n := 64) (r := 6) (by simp)).trans (values.1.trans source)
  have outputA : a.regValue .rdi = stackPtr initial - 184 :=
    (callFrame.read (n := 64) (r := 7) (by simp)).trans (values.2.2.2.trans dest)
  have lengthA : a.regValue .rdx = 144 :=
    (callFrame.read (n := 64) (r := 2) (by simp)).trans values.2.2.1
  have pre := callee_pre_of_stack stride hCall.stack stackAvoid outside
    runningA.machine runningA.directionFlag runningA.loaded runningA.allocated copyLayout
    (call.rip.trans target) rspA inputA outputA
    (by rw [boundaryA]; exact inProgram_of_textOffset 0x2025 (by decide))
  obtain ⟨t, result, bytes, _⟩ := Common.Memory.memcpy_correct pre lengthA (by decide)
  have runningT := runningA.of_callee result (by
    intro r hr addr ha
    exact ⟨stack, by simp [stack], stack_layout_within hCall.stack copyLayout rspA outputA r hr addr ha⟩)
  have inputHmac : HmacAt a (stackPtr initial - 328) (RFC5869.extract .sha256 salt ikm) ByteArray.empty := by
    apply start.hmac.of_copy
    intro i hi
    rw [← setup.agrees.external noMem]
    apply callFrame.byte
    intro c hc covered
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact covered.elim
    · obtain ⟨j, hj, eq⟩ := covered
      apply OffsetsApart.ne (c₁ := -328) (len₁ := 144) (c₂ := -368) (len₂ := 8)
        (by unfold OffsetsApart; decide +kernel) (stackPtr initial) hi hj (by decide)
      simpa only [BitVec.sub_eq_add_neg] using eq
    · exact covered.elim
  have hmac : HmacAt t (stackPtr initial - 184) (RFC5869.extract .sha256 salt ikm) ByteArray.empty := by
    apply inputHmac.of_copy
    simpa only [inputA, outputA] using bytes
  have setupFrame : AgreesExcept [.reg 6, .reg 13, .reg 2, .reg 7, .rip] s u := setup.agrees
  have keep := setupFrame.trans callFrame
  have savedRbp : t.regValue .rbp = s.regValue .rbp :=
    (result.abi.1 .rbp (by simp)).trans (keep.read (n := 64) (r := 5) (by simp))
  have totalFrame : MemoryWriteFrame s t #v[registerRegion a .rdi 144, Stack.region a 0] := by
    apply memoryWriteFrame_trans (t := u) _ (call_result pre call result runningU.directionFlag).1
    exact setup.agrees.memoryWriteFrame (fun c hc addr ha ↦ (noMem c hc addr ha).elim)
  have saved : SavedFrame initial t := by
    apply savedFrame_of_frame start.saved savedRbp hCall.stack totalFrame
    intro addr lo hi r hr contains
    obtain ⟨destStart, _, stackEnd⟩ := stack_layout_bounds hCall.stack copyLayout rspA outputA
    have low : 2632 ≤ (stackPtr initial).toNat := hCall.stack.2.2.1
    have options : r = registerRegion a .rdi 144 ∨ r = Stack.region a 0 := by simpa using hr
    rcases options with rfl | rfl
    · have bound : addr < (registerRegion a .rdi 144).start + 144 := contains.2
      rw [destStart] at bound
      change addr < (stackPtr initial).toNat - 184 + 144 at bound
      omega
    · have bound := contains.2
      rw [stackEnd] at bound
      change addr < (stackPtr initial).toNat - 368 + 8 at bound
      omega
  refine ⟨t, runningT, saved, ?_, ?_, ?_, ?_, hmac⟩
  · exact ⟨(result.abi.1 .r14 (by simp)).trans ((keep.read (n := 64) (r := 14) (by simp)).trans start.args.info),
      (result.abi.1 .rbx (by simp)).trans ((keep.read (n := 64) (r := 3) (by simp)).trans start.args.infoLength),
      (result.abi.1 .r15 (by simp)).trans ((keep.read (n := 64) (r := 15) (by simp)).trans start.args.output),
      (result.abi.1 .r12 (by simp)).trans ((keep.read (n := 64) (r := 12) (by simp)).trans start.args.length)⟩
  · rw [result.rip, boundaryA]; rfl
  · rw [show stackPtr t = _ from result.rsp, boundaryA]; rfl
  · exact (result.abi.1 .r13 (by simp)).trans
      ((callFrame.read (n := 64) (r := 13) (by simp)).trans (values.2.1.trans dest))

end Hkdf.Proofs.NewExpand.Wrapper.Copy
