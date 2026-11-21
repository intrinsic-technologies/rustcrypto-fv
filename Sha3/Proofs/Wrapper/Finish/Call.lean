import Sha3.Proofs.Wrapper.Setup.Prologue
import Sha3.Proofs.Calls

namespace Sha3.Proofs.Wrapper.Finish

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

theorem stackSub_ne_returnBoundary (initial : RamState) (offset : BitVec 64)
    (hOffset : (8 : BitVec 64) + offset ≠ 0) :
    initial.regValue .rsp - offset ≠ (returnBoundary initial).rsp := by
  intro he
  have hh := congrArg (fun x : BitVec 64 ↦ x + offset) he
  change initial.regValue .rsp - offset + offset = initial.regValue .rsp + 8 + offset at hh
  rw [BitVec.sub_add_cancel, BitVec.add_assoc] at hh
  have hz : (0 : BitVec 64) = 8 + offset :=
    (BitVec.add_right_inj (initial.regValue .rsp)).mp ((BitVec.add_zero _).trans hh)
  exact hOffset hz.symm


theorem callAt [bindings : Bindings] {initial s : RamState} {v : Variant} {mode : Mode}
    {keccak fullState : Bool}
    {inputs : Array Input} {split : Nat} (offset length : Nat) (load : Bool)
    (next target : BitVec 64)
    (hCall : ValidInvocation bindings v mode initial inputs split keccak fullState)
    (hBudget : offset + 8 ≤ (mode.entry v keccak fullState).minStackBytes)
    (hInv : Invariant initial v mode s keccak fullState)
    (hRsp : stackPtr s = initial.regValue .rsp - .ofNat 64 offset)
    (hStep : Machine.step s = some (.next (afterStep s length fun t ↦
      callState (callFrom load t next) next target))) :
    ∃ t, Advances (returnBoundary initial) 1 s t ∧ Invariant initial v mode t keccak fullState ∧
      t.RIP = target ∧ stackPtr t = initial.regValue .rsp - .ofNat 64 (offset + 8) ∧
      stackTop t = next ∧
      AgreesExcept [.reg 4, .mem (initial.regValue .rsp - .ofNat 64 (offset + 8)) 8, .rip] s t ∧
      (callEffect (fun _ ↦ target) next s).Holds s t := by
  have hPush : pushAddr s = (initial.regValue .rsp - .ofNat 64 (offset + 8)) := by
    rw [pushAddr, hRsp]
    rw [BitVec.sub_sub, BitVec.ofNat_add]
    rfl
  have hWrites : ∀ i, i < 8 → ∃ region ∈ writeRegions initial v mode keccak fullState,
      region.Contains (pushAddr s + BitVec.ofNat 64 i).toNat := by
    intro i hi
    refine ⟨Stack.region initial (mode.entry v keccak fullState).minStackBytes, stack_mem_writeRegions initial v mode keccak fullState, ?_⟩
    rw [hPush]
    exact stack_sub_contains (offset := offset + 8) hCall.stackAvailable hBudget (by omega)
  have hAvoid : ∀ region ∈ writeRegions initial v mode keccak fullState, region.Avoids InPageTables := by
    intro region hr address hc ht
    exact writeRegions_avoid hCall region hr address hc (.inr ht)
  let t := afterStep s length fun t ↦ callState (callFrom load t next) next
    target
  have ha : AgreesExcept [.reg 4, .mem (initial.regValue .rsp - .ofNat 64 (offset + 8)) 8, .rip] s t := by
    have hh := AgreesExcept.afterStep_call s load length next
      target
    rw [hPush] at hh
    exact hh
  have hr : ReadyToStep t := afterStep_call_readyToStep_of_avoids hInv.ready load length
    next target (writeRegions initial v mode keccak fullState) hWrites hAvoid
  have hi : Invariant initial v mode t keccak fullState := by
    apply hInv.of_agreesExcept hCall hr ha
    intro component hcomponent address hcover
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hcomponent
    rcases hcomponent with rfl | rfl | rfl
    · exact hcover.elim
    · obtain ⟨i, hi, he⟩ := hcover
      rw [he, ← hPush]
      exact hWrites i hi
    · exact hcover.elim
  have hsp : stackPtr t = (initial.regValue .rsp - .ofNat 64 (offset + 8)) :=
    (Operand.read_afterStep_call_rsp s load length _ _).trans hPush
  have hret : stackTop t = next := by
    rw [stackTop, hsp, ← hPush]
    exact Operand.read_afterStep_call_mem s load length _ _
  have he : (callEffect (fun _ ↦ target) next s).Holds s t :=
    ⟨afterStep_call_rip _ _ _ _ _, ⟨Operand.read_afterStep_call_rsp _ _ _ _ _,
      Operand.read_afterStep_call_mem _ _ _ _ _⟩, trivial,
      (pushEffect_components _ _ s).symm ▸ AgreesExcept.afterStep_call _ _ _ _ _⟩
  refine ⟨t, Advances.of_step hStep (.inr ?_), hi, he.rip, hsp, hret, ha, he⟩
  change stackPtr t ≠ _
  rw [hsp]
  apply stackSub_ne_returnBoundary
  intro he
  have hlow := hCall.stackAvailable.1
  simp only [Stack.region, Stack.returnAddressBytes, MemoryRegion.Bounded,
    userAddressLimit] at hlow
  have hmin : (mode.entry v keccak fullState).minStackBytes ≤ (initial.regValue .rsp).toNat :=
    hCall.stackAvailable.2.2.1
  have hn := congrArg BitVec.toNat he
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, BitVec.reduceToNat] at hn
  omega

theorem directCallAt [bindings : Bindings] {initial s : RamState} {v : Variant} {mode : Mode}
    {keccak fullState : Bool}
    {inputs : Array Input} {split : Nat} (offset : Nat) (p : BitVec 64) (disp : BitVec 32)
    (hCall : ValidInvocation bindings v mode initial inputs split keccak fullState) (hBudget : offset + 8 ≤ (mode.entry v keccak fullState).minStackBytes)
    (hAligned : offset % 8 = 0)
    (hInv : Invariant initial v mode s keccak fullState) (hRip : s.RIP = p)
    (hRsp : stackPtr s = (initial.regValue .rsp - .ofNat 64 offset))
    (hImage : ∀ x ∈ codeRange p (encodeCallRel32 disp), x ∈ Extracted.programImage)
    (hTarget : (branchTarget p 5 (disp.signExtend 64)).toNat < 2^32) :
    ∃ t, Advances (returnBoundary initial) 1 s t ∧ Invariant initial v mode t keccak fullState ∧
      t.RIP = branchTarget p 5 (disp.signExtend 64) ∧
      stackPtr t = (initial.regValue .rsp - .ofNat 64 (offset + 8)) ∧ stackTop t = p + 5 ∧
      AgreesExcept [.reg 4, .mem (initial.regValue .rsp - .ofNat 64 (offset + 8)) 8, .rip] s t ∧
      (callEffect (fun _ ↦ branchTarget p 5 (disp.signExtend 64)) (p + 5) s).Holds s t := by
  have hoffset : 8 * (offset / 8) = offset := by omega
  have hMem := stack_push_readable_after (n := offset / 8) hInv hCall.stackAvailable
    (by omega) (by simpa only [hoffset] using hRsp)
  have hc := hInv.code.mono hImage
  have hs := call_rel32_step_of_readable s hInv.ready disp
    (hRip ▸ hc.bytesAt) (hRip ▸ hc.low (by simp [encodeCallRel32]) (by simp [encodeCallRel32]))
    (hRip ▸ hTarget) hMem.1 hMem.2
  rw [hRip] at hs
  exact callAt offset 5 false (p + 5) (branchTarget p 5 (disp.signExtend 64))
    hCall hBudget hInv hRsp hs

theorem indirectCallAt [bindings : Bindings] {initial s : RamState} {v : Variant} {mode : Mode}
    {keccak fullState : Bool}
    {inputs : Array Input} {split : Nat} (offset : Nat) (p : BitVec 64) (disp : BitVec 32)
    (hCall : ValidInvocation bindings v mode initial inputs split keccak fullState)
    (hBudget : offset + 8 ≤ (mode.entry v keccak fullState).minStackBytes) (hAligned : offset % 8 = 0)
    (hInv : Invariant initial v mode s keccak fullState) (hRip : s.RIP = p)
    (hRsp : stackPtr s = initial.regValue .rsp - .ofNat 64 offset)
    (hImage : ∀ x ∈ codeRange p (encodeCallM64 (.rip disp)), x ∈ Extracted.programImage)
    (hRead : MemReadable s ((AddrMode.rip disp).addr s (p + 6)) 8)
    (hTarget : (callMemPtr p (.rip disp) s).toNat < 2^32) :
    ∃ t, Advances (returnBoundary initial) 1 s t ∧ Invariant initial v mode t keccak fullState ∧
      t.RIP = callMemPtr p (.rip disp) s ∧
      stackPtr t = initial.regValue .rsp - .ofNat 64 (offset + 8) ∧ stackTop t = p + 6 ∧
      AgreesExcept [.reg 4, .mem (initial.regValue .rsp - .ofNat 64 (offset + 8)) 8, .rip] s t ∧
      (callEffect (fun _ ↦ callMemPtr p (.rip disp) s) (p + 6) s).Holds s t := by
  have hoffset : 8 * (offset / 8) = offset := by omega
  have hMem := stack_push_readable_after (n := offset / 8) hInv hCall.stackAvailable
    (by omega) (by simpa only [hoffset] using hRsp)
  have hc := hInv.code.mono hImage
  have hread : MemReadable s ((AddrMode.rip disp).addrAt s 6) 8 := by
    unfold AddrMode.addrAt
    rw [hRip]
    exact hRead
  have htarget : ((Operand.mem ((AddrMode.rip disp).addrAt s 6) : Operand 64).read s).toNat <
      2^32 := by
    unfold AddrMode.addrAt
    rw [hRip]
    exact hTarget
  have hlow : s.RIP.toNat + (0 + 2 + (AddrMode.rip disp).tail.length) ≤ 2^32 := by
    have hl := hc.low (by simp [encodeCallM64]) (by simp [encodeCallM64, AddrMode.tail])
    have ht : (AddrMode.rip disp).tail.length = 4 := by simp [AddrMode.tail]
    simpa only [hRip, encodeCallM64, List.length_cons, ht, Nat.reduceAdd] using hl
  have hs := call_m64_step_of_readable s hInv.ready [] (by simp) (by simp) rfl rfl rfl
    (.rip disp) trivial (AddrContext.legacy _ _ rfl rfl)
    (hRip ▸ hc.bytesAt) hlow hread htarget hMem.1 hMem.2
  have hstep : Machine.step s = some (.next (afterStep s 6 fun t ↦
      callState (callFrom true t (p + 6)) (p + 6) (callMemPtr p (.rip disp) s))) := by
    have ht : (AddrMode.rip disp).tail.length = 4 := by simp [AddrMode.tail]
    simp only [List.length_nil, ht, Nat.reduceAdd, AddrMode.addrAt, hRip] at hs
    exact hs
  exact callAt offset 6 true (p + 6) (callMemPtr p (.rip disp) s)
    hCall hBudget hInv hRsp hstep

theorem callMemory_above {s t : RamState} {target : RamState → BitVec 64} {ret : BitVec 64}
    (h : (callEffect target ret s).Holds s t) {offset count : Nat}
    (hBound : 8 + offset + count ≤ 2^64) :
    ∀ i < count, t.external[stackPtr s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      s.external[stackPtr s + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  have hBase : stackPtr s + BitVec.ofNat 64 offset =
      pushAddr s + BitVec.ofNat 64 (8 + offset) := by
    rw [BitVec.ofNat_add, ← BitVec.add_assoc]
    exact congrArg (· + BitVec.ofNat 64 offset)
      (show stackPtr s = pushAddr s + 8 from (BitVec.sub_add_cancel _ _).symm)
  intro i hi
  apply h.agrees.byte
  intro c hc hCover
  simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact hCover.elim
  · obtain ⟨j, hj, he⟩ := hCover
    have hApart := RangeApart.offsets (pushAddr s) (a := 8 + offset) (len := count)
      (b := 0) (count := 8) hBound (by decide) (.inr (by omega))
    apply hApart i hi j hj
    simpa only [BitVec.add_zero, hBase] using he
  · exact hCover.elim

theorem callRead_above {s t : RamState} {target : RamState → BitVec 64} {ret : BitVec 64}
    (h : (callEffect target ret s).Holds s t) {offset width : Nat}
    (hBound : 8 + offset + width / 8 ≤ 2^64) :
    (Operand.mem (stackPtr s + BitVec.ofNat 64 offset) : Operand width).read t =
      (Operand.mem (stackPtr s + BitVec.ofNat 64 offset) : Operand width).read s := by
  apply memLoad_congr
  intro i hi
  exact congrArg (fun x : Option UInt8 ↦ x.getD 0) (callMemory_above h hBound i hi)

end Sha3.Proofs.Wrapper.Finish
