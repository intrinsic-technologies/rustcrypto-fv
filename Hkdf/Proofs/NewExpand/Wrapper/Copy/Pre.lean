import Hkdf.Proofs.NewExpand.Wrapper.Copy.State
import Hkdf.Proofs.NewExpand.Wrapper.Prologue.Call
import Hkdf.Proofs.Common.CallFrame.Stack
import Hkdf.Proofs.Common.Model

namespace Hkdf.Proofs.NewExpand.Wrapper.Copy

open Hkdf.Spec Hkdf.Spec.Program Hkdf.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

open Hkdf.Proofs.Common Hkdf.Proofs.Common.CallFrame Hkdf.Proofs.Common.Machine

theorem expandEntry [bindings : Bindings]
    {initial : RamState} {salt : Option ByteArray} {ikm info : ByteArray} {length : Nat}
    (hCall : ValidDeriveKeyCall Extracted.hkdfSha256NewExpandAddress
      hkdfSha256NewExpandMinStackBytes initial salt ikm info length)
    {s : RamState} (start : AtExpand initial s (RFC5869.extract .sha256 salt ikm))
    (stride : UnitStringStride bindings) :
    ExpandEntry initial s (RFC5869.extract .sha256 salt ikm) info length := by
  let layout : StackCallLayout hkdfSha256NewExpandMinStackBytes 16 144 2264 :=
    ⟨368, 360, 184, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
  have outside := outerBoundary hCall.returnAddress
  have outerAvoid := (hCall.stackSeparation.2 _ (Vector.mem_singleton_self _)).2
  have pc : InProgram (returnBoundary s).rip := by
    rw [start.boundary]
    exact inProgram_of_textOffset 0x2044 (by decide)
  have localPre := callee_pre_of_stack stride hCall.stack outerAvoid outside start.run.machine
    start.run.directionFlag start.run.loaded start.run.allocated layout start.rip start.rsp
    start.descriptor start.key pc
  have within := stack_layout_within hCall.stack layout start.rsp start.key
  have subStack := within _ (show Stack.region s 2264 ∈ _ from by simp)
  have subKey := within _ (show registerRegion s .rdi 144 ∈ _ from by simp)
  have subDesc (a) (contains : (registerRegion s .rsi 16).Contains a) :
      (Stack.region initial hkdfSha256NewExpandMinStackBytes).Contains a := by
    have low : 2632 ≤ (stackPtr initial).toNat := hCall.stack.2.2.1
    change (s.regValue .rsi).toNat ≤ a ∧ a < (s.regValue .rsi).toNat + 16 at contains
    rw [start.descriptor, show (stackPtr initial - 360).toNat = (stackPtr initial).toNat - 360
      from stack_sub_toNat hCall.stack (show 360 ≤ 2632 by decide)] at contains
    unfold MemoryRegion.Contains
    rw [stack_region_end]
    change (stackPtr initial).toNat - 2632 ≤ a ∧ _
    exact (show ∀ p a : Nat, 2632 ≤ p → p - 360 ≤ a ∧ a < p - 360 + 16 →
      p - 2632 ≤ a ∧ a < p + 8 by omega) _ _ low contains
  have readsStack (r) (hr : r ∈ [registerRegion s .rdi 144, registerRegion s .rsi 16]) :
      r.Disjoint (Stack.region s 2264) := by
    rcases (show r = registerRegion s .rdi 144 ∨ r = registerRegion s .rsi 16 by simpa using hr)
      with rfl | rfl
    · exact localPre.separation ⟨1, by decide⟩ ⟨2, by decide⟩ (by decide)
    · exact localPre.separation ⟨0, by decide⟩ ⟨2, by decide⟩ (by decide)
  have out : registerRegion s .rcx length = deriveKeyOutputRegion initial length := by
    unfold registerRegion deriveKeyOutputRegion
    rw [start.output]
  refine ⟨start.run, ?_, start.saved, start.rsp, start.output, start.boundary⟩
  refine {
    call := ⟨stride, start.run.machine, start.run.directionFlag, start.run.loaded, start.rip,
      ?_, ?_, by simp, by simp, localPre.stack, by simp [MemoryRegion.PairwiseDisjoint],
      fun i => Fin.elim0 i, by simp, localPre.avoids _ (by simp), outside, pc⟩
    keySize := extract_sha256_size salt ikm
    hmac := start.hmac
    count := start.count
    pointer := start.pointer
    infoLength := ?_
    lengthFits := hCall.infoLengthArgumentMatchesInfo ▸ (initial.regValue .r9).isLt
    lengthArg := start.length ▸ hCall.outputLengthArgumentMatchesLength
    stackSeparation := ?_
    infoBytes := ?_
    output := ?_
    separation := ?_ }
  · intro r hr
    rcases (show r = registerRegion s .rdi 144 ∨ r = registerRegion s .rsi 16 by simpa using hr)
      with rfl | rfl
    · exact localPre.outputBounded
    · exact localPre.inputBounded
  · intro r hr
    rcases (show r = registerRegion s .rdi 144 ∨ r = registerRegion s .rsi 16 by simpa using hr)
      with rfl | rfl
    · exact localPre.outputAllocated
    · exact localPre.inputAllocated
  · rw [← hCall.infoLengthArgumentMatchesInfo]
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using start.infoLength
  · refine ⟨by simp [MemoryRegion.PairwiseDisjoint], fun r hr => ?_⟩
    obtain rfl := Vector.mem_singleton.mp hr
    exact ⟨readsStack, localPre.avoids _ (by simp)⟩
  · intro hp hb
    change ValidInput s.external (infoRegion initial info) info
    have h := hCall.infoInMemoryIfWritten hp hb
    refine ⟨h.1, frame_hasBytes start.run.frame ?_ (by have := h.1; unfold MemoryRegion.Bounded userAddressLimit at this; omega) h.2⟩
    intro r hr
    obtain rfl := Vector.mem_singleton.mp hr
    exact ((hCall.separationIfWritten hp hb).2 _ (by simp)).1 _ (by simp)
  · intro hp hb
    rw [out]
    obtain ⟨bound, alloc⟩ := hCall.outputInMemoryIfWritten hp hb
    exact ⟨bound, fun a ha => Option.isSome_iff_exists.mp (start.run.allocated a
      (Option.isSome_iff_exists.mpr (alloc a ha)))⟩
  · intro hp hb
    rw [out]
    have sep := hCall.separationIfWritten hp hb
    have ds := sep.1 ⟨0, by decide⟩ ⟨1, by decide⟩ (by decide)
    change (deriveKeyOutputRegion initial length).Disjoint (Stack.region initial _) at ds
    have stackInfo := (sep.2 (Stack.region initial hkdfSha256NewExpandMinStackBytes) (by simp)).1 (infoRegion initial info) (by simp)
    have outInfo := (sep.2 (deriveKeyOutputRegion initial length) (by simp)).1 (infoRegion initial info) (by simp)
    constructor
    · intro i j hij
      have hi : i = 0 := Fin.ext (by have := i.isLt; have := j.isLt; change i.val < j.val at hij; omega)
      have hj : j = 1 := Fin.ext (by have := i.isLt; have := j.isLt; change i.val < j.val at hij; omega)
      subst i j
      exact fun a ha hs => ds a ha (subStack a hs)
    · intro r hr
      rcases (show r = deriveKeyOutputRegion initial length ∨ r = Stack.region s 2264 by simpa using hr)
        with rfl | rfl
      · refine ⟨?_, (sep.2 _ (by simp)).2⟩
        intro read hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact fun a hk ho => ds a ho (subKey a hk)
        · exact fun a hd ho => ds a ho (subDesc a hd)
        · exact outInfo
      · refine ⟨?_, localPre.avoids _ (by simp)⟩
        intro read hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl
        · exact readsStack _ (by simp)
        · exact readsStack _ (by simp)
        · exact fun a hi hs => stackInfo a hi (subStack a hs)

end Hkdf.Proofs.NewExpand.Wrapper.Copy
