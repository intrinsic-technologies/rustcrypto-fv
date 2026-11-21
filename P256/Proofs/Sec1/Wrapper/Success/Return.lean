import P256.Proofs.Sec1.Wrapper.Success.Call

set_option autoImplicit false

namespace P256.Proofs.Sec1.Wrapper.Success

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [Bindings] {initial s entry t : RamState} {inputs : List ByteArray}
  {slices : Array Input} {inputBytes outputBytes reserve : Nat}
  {site : CallSite inputBytes outputBytes reserve}

theorem result_byte
    (valid : ValidCallWithSlices publicKeyFromSec1Bytes initial inputs slices)
    (called : Called initial s entry site)
    (result : CalleeResult entry t (returnBoundary initial) outputBytes reserve)
    {offset len i : Nat} (ho : offset ≤ 232) (hl : len ≤ offset + 8)
    (apart : offset + outputBytes ≤ site.layout.outputOffset ∨
      site.layout.outputOffset + len ≤ offset) (hi : i < len) :
    t.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      s.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  have bounds := stack_bounds valid.stackAvailable.1
  change 4048 ≤ (stackPtr initial).toNat ∧ (stackPtr initial).toNat + 8 < 2^32 at bounds
  have limit := site.layout.capacity
  have above := site.layout.outputAbove
  rw [site.stack] at limit above
  have sp : (stackPtr entry).toNat = (stackPtr initial).toNat - 240 := by
    rw [called.rsp]
    exact stack_sub_toNat valid.stackAvailable.1 (by decide)
  have dst : (entry.regValue .rdi).toNat =
      (stackPtr initial).toNat - site.layout.outputOffset := by
    rw [called.output]
    exact stack_sub_toNat valid.stackAvailable.1 (by change site.layout.outputOffset ≤ 4048; omega)
  have base := stack_sub_toNat valid.stackAvailable.1 (offset := offset) (by change offset ≤ 4048; omega)
  have addr : (stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat =
      (stackPtr initial).toNat - offset + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : i < 2^64),
      base, Nat.mod_eq_of_lt (by omega)]
  apply Eq.trans (result.frame _ ?_) (called.bytes offset len ho hl i hi)
  intro region hr hin
  have cases : region = registerRegion entry .rdi outputBytes ∨
      region = Stack.region entry reserve := by simpa using hr
  rcases cases with rfl | rfl
  · change (entry.regValue .rdi).toNat ≤ _ ∧ _ <
      (entry.regValue .rdi).toNat + outputBytes at hin
    rw [dst, addr] at hin
    omega
  · change (stackPtr entry).toNat - reserve ≤ _ ∧ _ <
      (Stack.region entry reserve).start + (Stack.region entry reserve).size at hin
    rw [stack_region_end, sp, addr] at hin
    omega

theorem result_frame
    (valid : ValidCallWithSlices publicKeyFromSec1Bytes initial inputs slices)
    (called : Called initial s entry site)
    (result : CalleeResult entry t (returnBoundary initial) outputBytes reserve) :
    MemoryWriteFrame s t #v[Stack.region initial 4048] := by
  apply memoryWriteFrame_trans called.frame
  intro a ha
  apply result.frame a
  intro region hr hin
  apply ha (Stack.region initial 4048) (by simp)
  apply site.layout.regions_within valid.stackAvailable.1
    (by rw [site.stack]; exact called.rsp) called.input called.output region ?_ a.toNat hin
  have cases : region = registerRegion entry .rdi outputBytes ∨
      region = Stack.region entry reserve := by simpa using hr
  rcases cases with rfl | rfl <;> simp

theorem returned
    (valid : ValidCallWithSlices publicKeyFromSec1Bytes initial inputs slices)
    (state : ReturnState initial s) (called : Called initial s entry site)
    (result : CalleeResult entry t (returnBoundary initial) outputBytes reserve)
    (saved : outputBytes + 24 ≤ site.layout.outputOffset)
 :
    ReturnState initial t ∧
      t.RIP = Extracted.textAddress + BitVec.ofNat 64 site.codeOffset + (5 : BitVec 64) ∧
      (∀ r ∈ [Syntax.Reg.rbx, .rbp, .r12, .r13, .r14, .r15],
        t.regValue r = s.regValue r) := by
  have regs : ∀ r ∈ [Syntax.Reg.rbx, .rbp, .r12, .r13, .r14, .r15],
      t.regValue r = s.regValue r := by
    intro r hr
    apply (result.calleeSaved r hr).trans (called.registers r ?_)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  have load {offset : Nat} (ho : offset ≤ 232)
      (apart : offset + outputBytes ≤ site.layout.outputOffset ∨
        site.layout.outputOffset + 8 ≤ offset) :
      memLoad t.external (stackPtr initial - BitVec.ofNat 64 offset) 64 =
        memLoad s.external (stackPtr initial - BitVec.ofNat 64 offset) 64 := by
    apply memLoad_congr
    intro i hi
    change (t.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?).getD 0 =
      (s.external[stackPtr initial - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?).getD 0
    rw [result_byte valid called result ho (by omega) apart hi]
  refine ⟨⟨result.bindingsSupported, result.machine, result.loaded, result.directionFlag, ?_,
    (load (offset := 24) (by decide) (Or.inl (by omega))).trans state.savedRbx,
    (load (offset := 16) (by decide) (Or.inl (by omega))).trans state.savedR14,
    (load (offset := 8) (by decide) (Or.inl (by omega))).trans state.savedR15,
    ?_, ?_, fun a ha => result.allocated a (called.allocated a ha)⟩,
    result.rip.trans called.ret,regs⟩
  · have sp : stackPtr t = stackPtr entry + 8 := result.rsp
    rw [sp, called.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  · have h := load (offset := 0) (by decide) (Or.inl (by omega))
    simp only [BitVec.sub_zero] at h
    exact h.trans state.returnAddress
  · intro r hr
    exact (regs r (by simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢; rcases hr with rfl | rfl | rfl <;> simp)).trans
      (state.otherRegisters r hr)

end P256.Proofs.Sec1.Wrapper.Success
