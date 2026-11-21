import Hkdf.Proofs.NewExpand.Wrapper.Frame
import Hkdf.Proofs.Common.CallFrame.Stack

namespace Hkdf.Proofs.NewExpand.Wrapper

open Hkdf.Spec Hkdf.Spec.Program Hkdf.Proofs.Program Hkdf.Proofs.Common
open Hkdf.Proofs.Common.CallFrame Hkdf.Proofs.Common.Machine
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem extractPreAtCall [bindings : Bindings]
    {initial s : RamState} {salt : Option ByteArray} {ikm info : ByteArray} {length : Nat}
    (hCall : ValidDeriveKeyCall Extracted.hkdfSha256NewExpandAddress
      hkdfSha256NewExpandMinStackBytes initial salt ikm info length)
    (stride : UnitStringStride bindings) (run : Running initial s)
    (outside : ¬ InProgram (returnBoundary initial).rip) (rip : s.RIP = 0x10fa80)
    (boundary : returnBoundary s = ⟨0x10200a, stackPtr initial - 360⟩)
    (rsp : stackPtr s = stackPtr initial - 368)
    (dest : s.regValue .rdi = stackPtr initial - 360)
    (saltPtr : s.regValue .rsi = initial.regValue .rdi)
    (saltLen : s.regValue .rdx = initial.regValue .rsi)
    (ikmPtr : s.regValue .rcx = initial.regValue .rdx)
    (ikmLen : s.regValue .r8 = initial.regValue .rcx) :
    ExtractPre s (returnBoundary initial) salt ikm := by
  let layout : StackCallLayout hkdfSha256NewExpandMinStackBytes 0 176 2264 :=
    ⟨368, 360, 360, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩
  have pc : InProgram (returnBoundary s).rip := by
    rw [boundary]
    exact inProgram_of_textOffset 0x200a (by decide)
  have separation := hCall.stackSeparation.2 _ (Vector.mem_singleton_self _)
  have saltRegion (k : ByteArray) : registerRegion s .rsi k.size = inputRegion initial k := by
    unfold inputRegion registerRegion
    rw [saltPtr]
  have secret : registerRegion s .rcx ikm.size = secretRegion initial ikm := by
    unfold secretRegion registerRegion
    rw [ikmPtr]
  have saltBound : (registerRegion s .rsi 0).Bounded := by
    cases salt with
    | none =>
      change (s.regValue .rsi).toNat + 0 < userAddressLimit
      rw [saltPtr, (hCall.saltPointerArgumentIsNullIffNoSalt).2 rfl]
      decide
    | some k =>
      have hk := (hCall.saltInMemory k (by simp)).1
      change (initial.regValue .rdi).toNat + k.size < userAddressLimit at hk
      change (s.regValue .rsi).toNat + 0 < userAddressLimit
      rw [saltPtr]
      omega
  have empty (a : Nat) : ¬ (registerRegion s .rsi 0).Contains a := by
    simp [MemoryRegion.Contains, registerRegion]
  have localPre := callee_pre_of_stack_output stride hCall.stack separation.2 outside
    run.machine run.directionFlag run.loaded run.allocated layout rip rsp dest pc saltBound
    (fun a ha => (empty _ ha).elim) (fun a ha => (empty _ ha).elim)
  have within := stack_layout_within hCall.stack layout rsp dest
  have transfer (region : MemoryRegion) (bytes : ByteArray)
      (member : region ∈ secretRegion initial ikm :: salt.toList.map (inputRegion initial))
      (valid : ValidInput initial.external region bytes) : ValidInput s.external region bytes := by
    refine ⟨valid.1, frame_hasBytes run.frame ?_ ?_ valid.2⟩
    · intro r hr
      obtain rfl := Vector.mem_singleton.mp hr
      exact separation.1 region member
    · have bound : region.start + region.size < 2^32 := valid.1
      omega
  have apart := localPre.separation ⟨1, by decide⟩ ⟨2, by decide⟩ (by decide)
  change (registerRegion s .rdi 176).Disjoint (Stack.region s 2264) at apart
  refine {
    call := ⟨stride, run.machine, run.directionFlag, run.loaded, rip, by simp, by simp,
      fun r hr => (Vector.mem_singleton.mp hr) ▸ localPre.outputBounded,
      fun r hr => (Vector.mem_singleton.mp hr) ▸ localPre.outputAllocated,
      localPre.stack, by simp [MemoryRegion.PairwiseDisjoint], ?_, ?_,
      localPre.avoids _ (by simp), outside, pc⟩
    saltNull := saltPtr ▸ hCall.saltPointerArgumentIsNullIffNoSalt
    saltLength := fun k hk => saltLen ▸ hCall.saltLengthArgumentMatchesSalt k hk
    saltBytes := ?_
    ikmLength := ikmLen ▸ hCall.secretLengthArgumentMatchesSecret
    ikmBytes := secret ▸ transfer _ _ (by simp) hCall.secretInMemory
    separation := ?_ }
  · intro i
    have e : i = 0 := Subsingleton.elim _ _
    subst i
    exact apart
  · intro r hr
    obtain rfl := Vector.mem_singleton.mp hr
    exact localPre.avoids _ (by simp)
  · intro k hk
    rw [saltRegion]
    apply transfer _ _ _ (hCall.saltInMemory k hk)
    exact List.mem_cons_of_mem _ (List.mem_map.mpr ⟨k, by simpa using hk, rfl⟩)
  · constructor
    · intro i j hij
      have hi : i = 0 := Fin.ext (by have := i.isLt; have := j.isLt; change i.val < j.val at hij; omega)
      have hj : j = 1 := Fin.ext (by have := i.isLt; have := j.isLt; change i.val < j.val at hij; omega)
      subst i j
      exact apart
    · intro r hr
      refine ⟨?_, fun a ha => separation.2 a (within r hr a.toNat ha)⟩
      intro read hread a ha hw
      apply separation.1 read _ a ha (within r hr a hw)
      simpa only [secret, saltRegion] using hread

end Hkdf.Proofs.NewExpand.Wrapper
