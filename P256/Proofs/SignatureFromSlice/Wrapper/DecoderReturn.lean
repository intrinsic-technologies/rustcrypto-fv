import P256.Proofs.SignatureFromSlice.Wrapper.Interface
import P256.Proofs.SignatureFromSlice.Wrapper.Epilogue.State
import P256.Proofs.Program.Stack

set_option autoImplicit false

namespace P256.Proofs.SignatureFromSlice.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [Bindings] {initial s t : RamState} {input : ByteArray} {boundary : ReturnBoundary}

theorem decoder_region_bounds (hs : Stack.Valid initial 656)
    (entry : DecoderEntry initial s input boundary)
    {region : MemoryRegion}
    (hr : region ∈ #v[registerRegion s .rdi 72, Stack.region s 560]) :
    (stackPtr initial).toNat - 656 ≤ region.start ∧
      region.start + region.size ≤ (stackPtr initial).toNat - 16 := by
  have hn := stack_bounds hs
  have hp : (stackPtr s).toNat = (stackPtr initial).toNat - 96 := by
    rw [entry.rsp]
    exact stack_sub_toNat hs (by decide)
  have hd : (s.regValue .rdi).toNat = (stackPtr initial).toNat - 88 := by
    rw [entry.destination]
    exact stack_sub_toNat hs (by decide)
  have hr' : region = registerRegion s .rdi 72 ∨ region = Stack.region s 560 := by
    simpa using hr
  rcases hr' with rfl | rfl
  · change _ ≤ (s.regValue .rdi).toNat ∧ (s.regValue .rdi).toNat + 72 ≤ _
    rw [hd]
    constructor <;> omega
  · rw [stack_region_end]
    change _ ≤ (stackPtr s).toNat - 560 ∧ (stackPtr s).toNat + 8 ≤ _
    rw [hp]
    constructor <;> omega

theorem decoder_preserves_word (hs : Stack.Valid initial 656)
    (entry : DecoderEntry initial s input boundary)
    (result : CalleeResult s t boundary 72 560) {off : Nat} (ho : off ≤ 16) :
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

theorem decoder_return_state (hs : Stack.Valid initial 656)
    (entry : DecoderEntry initial s input boundary)
    (result : CalleeResult s t boundary 72 560) : Return.State initial t 88 := by
  have state : Return.State initial s 96 :=
    ⟨entry.pre.bindingsSupported, entry.pre.machine, entry.pre.loaded, entry.pre.directionFlag,
      entry.rsp, entry.output, entry.capacity, entry.savedRbx, entry.savedR14,
      entry.returnAddress, entry.otherRegisters, entry.allocated⟩
  apply state.after_callee result
  intro off ho
  exact decoder_preserves_word hs entry result (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
    omega)

theorem decoder_return_frame (hs : Stack.Valid initial 656)
    (entry : DecoderEntry initial s input boundary)
    (result : CalleeResult s t boundary 72 560) :
    MemoryWriteFrame initial t
      #v[allocatorStateRegion, randomSourceRegion, callStack signatureFromSlice initial] := by
  apply memoryWriteFrame_trans entry.frame
  intro a ha
  apply result.frame a
  intro region hr hc
  apply ha (callStack signatureFromSlice initial) (by simp)
  have hb := decoder_region_bounds hs entry hr
  change (stackPtr initial).toNat - 656 ≤ a.toNat ∧
    a.toNat < (stackPtr initial).toNat - 656 +
      ((stackPtr initial).toNat + 16 - ((stackPtr initial).toNat - 656))
  have hn := stack_bounds hs
  constructor <;> have hlo := hc.1 <;> have hhi := hc.2 <;> omega

theorem decoder_return_execution (entry : DecoderEntry initial s input boundary)
    (result : CalleeResult s t boundary 72 560) :
    ∃ fuel, Advances boundary fuel initial t := by
  obtain ⟨n, hn⟩ := entry.execution
  obtain ⟨m, hm⟩ := result.execution
  exact ⟨n + m, hn.trans hm⟩

end P256.Proofs.SignatureFromSlice.Wrapper
