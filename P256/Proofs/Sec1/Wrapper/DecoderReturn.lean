import P256.Proofs.Sec1.Wrapper.ReturnState
import P256.Proofs.Sec1.Wrapper.Interface
import P256.Proofs.Program.WrapperReturn.State
import P256.Proofs.Program.Stack

set_option autoImplicit false

namespace P256.Proofs.Sec1.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [Bindings] {initial s t : RamState} {input : ByteArray} {boundary : ReturnBoundary}

theorem decoder_region_bounds (hs : Stack.Valid initial 4048)
    (entry : DecoderEntry initial s input boundary)
    {region : MemoryRegion}
    (hr : region ∈ #v[registerRegion s .rdi 80, Stack.region s 3680]) :
    (stackPtr initial).toNat - 4048 ≤ region.start ∧
      region.start + region.size ≤ (stackPtr initial).toNat - 24 := by
  have hn := stack_bounds hs
  have hp : (stackPtr s).toNat = (stackPtr initial).toNat - 240 := by
    rw [entry.rsp]
    exact stack_sub_toNat hs (by decide)
  have hd : (s.regValue .rdi).toNat = (stackPtr initial).toNat - 232 := by
    rw [entry.destination]
    exact stack_sub_toNat hs (by decide)
  have hr' : region = registerRegion s .rdi 80 ∨ region = Stack.region s 3680 := by
    simpa using hr
  rcases hr' with rfl | rfl
  · change _ ≤ (s.regValue .rdi).toNat ∧ (s.regValue .rdi).toNat + 80 ≤ _
    rw [hd]
    constructor <;> omega
  · rw [stack_region_end]
    change _ ≤ (stackPtr s).toNat - 3680 ∧ (stackPtr s).toNat + 8 ≤ _
    rw [hp]
    constructor <;> omega

theorem decoder_preserves_word (hs : Stack.Valid initial 4048)
    (entry : DecoderEntry initial s input boundary)
    (result : CalleeResult s t boundary 80 3680) {off : Nat} (ho : off ≤ 24) :
    memLoad t.external (stackPtr initial - BitVec.ofNat 64 off) 64 =
      memLoad s.external (stackPtr initial - BitVec.ofNat 64 off) 64 := by
  apply memLoad_congr
  intro i hi
  have hn := stack_bounds hs
  have ha : (stackPtr initial - BitVec.ofNat 64 off + BitVec.ofNat 64 i).toNat =
      (stackPtr initial).toNat - off + i := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, stack_sub_toNat hs (by omega)]
    omega
  change (t.external[stackPtr initial - BitVec.ofNat 64 off + BitVec.ofNat 64 i]?).getD 0 = _
  have hf := result.frame (stackPtr initial - BitVec.ofNat 64 off + BitVec.ofNat 64 i)
  have heq := hf (by
    intro region hr hc
    have he := (decoder_region_bounds hs entry hr).2
    have hc' := hc.2
    rw [ha] at hc'
    omega)
  rw [heq]
  rfl

theorem decoder_return_state (hs : Stack.Valid initial 4048)
    (entry : DecoderEntry initial s input boundary)
    (result : CalleeResult s t boundary 80 3680) : ReturnState initial t := by
  refine ⟨result.bindingsSupported, result.machine, result.loaded, result.directionFlag,
    ?_, ?_, ?_, ?_, ?_, ?_, fun a ha ↦ result.allocated a (entry.allocated a ha)⟩
  · change t.regValue .rsp = _
    rw [result.rsp]
    change stackPtr s + 8 = _
    rw [entry.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  · exact (decoder_preserves_word hs entry result (off := 24) (by decide)).trans entry.savedRbx
  · exact (decoder_preserves_word hs entry result (off := 16) (by decide)).trans entry.savedR14
  · exact (decoder_preserves_word hs entry result (off := 8) (by decide)).trans entry.savedR15
  · have h := decoder_preserves_word hs entry result (off := 0) (by decide)
    simp only [BitVec.sub_zero] at h
    exact h.trans entry.returnAddress
  · intro r hr
    apply (result.calleeSaved r ?_).trans (entry.otherRegisters r hr)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl <;> simp

theorem decoder_return_frame (hs : Stack.Valid initial 4048)
    (entry : DecoderEntry initial s input boundary)
    (result : CalleeResult s t boundary 80 3680) :
    MemoryWriteFrame initial t
      #v[allocatorStateRegion, randomSourceRegion, callStack publicKeyFromSec1Bytes initial] := by
  apply memoryWriteFrame_trans entry.frame
  intro a ha
  apply result.frame a
  intro region hr hc
  apply ha (callStack publicKeyFromSec1Bytes initial) (by simp)
  have hb := decoder_region_bounds hs entry hr
  change (stackPtr initial).toNat - 4048 ≤ a.toNat ∧
    a.toNat < (stackPtr initial).toNat - 4048 +
      ((stackPtr initial).toNat + 16 - ((stackPtr initial).toNat - 4048))
  have hn := stack_bounds hs
  constructor <;> have hlo := hc.1 <;> have hhi := hc.2 <;> omega

theorem decoder_return_execution (entry : DecoderEntry initial s input boundary)
    (result : CalleeResult s t boundary 80 3680) :
    ∃ fuel, Advances boundary fuel initial t := by
  obtain ⟨n, hn⟩ := entry.execution
  obtain ⟨m, hm⟩ := result.execution
  exact ⟨n + m, hn.trans hm⟩

end P256.Proofs.Sec1.Wrapper
