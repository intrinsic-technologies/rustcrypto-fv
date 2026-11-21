import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Clone
import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.StackWrites
import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Length
import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Inputs
import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.PreviousBranch
import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Counter.Frame

namespace Hkdf.Proofs.NewExpand.Expand

open Hkdf.Spec.Program Hkdf.Proofs.Common Hkdf.Proofs.Common.CallFrame Hkdf.Proofs.Common.Machine
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

private theorem clonePre [Bindings] {entry s : RamState} {boundary : ReturnBoundary}
    {key info : ByteArray} {ptr : BitVec 64} {length : Nat}
    (pre : ExpandPre entry boundary key info ptr length) (pos : 0 < length) (bound : length ≤ 8160)
    (saved : SavedFrame entry s boundary length)
    (pc : s.RIP = 0x10f5a0) (context : slot s 240 = entry.regValue .rdi)
    (inner : slot s 424 = entry.regValue .rdi + 64)
    (outer : slot s 416 = entry.regValue .rdi + 104) :
    ContextClone.Pre s (entry.regValue .rdi) := by
  have ctx := Counter.StackContext.of_pre pre pos bound
  have sp : rspOf s = Counter.base entry := saved.sp
  have stack := pre.call.stack
  have bounded := pre.call.readsBounded (registerRegion entry .rdi 144) (by simp)
  have source := memoryRegion_memReadable (addr := entry.regValue .rdi) (len := 144) bounded
    (pre.call.readsAllocated _ (by simp)) (Nat.le_refl _) (Nat.le_refl _)
  have dest : ContextClone.destination s = stackPtr entry - 264 := by
    change rspOf s + 272 = _
    rw [sp, Counter.base]
    bv_omega
  have address (word : Nat) (hw : word < 18) :
      ContextClone.destination s + BitVec.ofNat 64 (8*word) =
        stackPtr entry - BitVec.ofNat 64 (264 - 8*word) := by
    rw [dest, ← BitVec.ofNat_sub_ofNat_of_le 264 (8*word) (by omega) (by omega)]
    change stackPtr entry - 264 + _ = stackPtr entry - (264 - _)
    bv_omega
  refine ⟨pc, Encoding.Serialize.readable_of_grow source saved.allocated, ?_, ?_,
    context, inner, outer, ?_, ?_⟩
  · intro i hi j hj eq
    have inside := memoryRegion_contains_add bounded (addr := entry.regValue .rdi) (len := 144)
      (Nat.le_refl _) (Nat.le_refl _) hi
    apply (pre.stackSeparation.2 (Stack.region entry 2264) (by simp)).1
      (registerRegion entry .rdi 144) (by simp) _ inside
    rw [eq, dest]
    exact stackRegion_contains_sub stack.2.2.1 (offset := 264) (len := 144)
      (by decide) (by decide) ⟨j, hj, rfl⟩
  · intro off member
    rw [sp]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl
    all_goals exact Counter.read_stack ctx saved.toRunning (off := _) (by decide) (by decide)
  · intro word hw
    rw [address word hw]
    exact stack_writable8 stack pre.call.stackAvoid saved.allocated (by omega) (by omega)
  · intro word hw
    rw [address word hw]
    apply stack_codeApart (codeOffset := 0xf5a0) stack (fun a ha hp ↦ pre.call.stackAvoid a ha (.inl hp))
      (by omega) (by omega)
    decide +kernel

def preparationComponents (s : RamState) : List Component :=
  [.reg 1,.reg 2,.reg 3,.reg 6,.reg 7,.flags,.rip,
    .mem (stackPtr s + 8) 8,.mem (stackPtr s + 264) 8,.mem (stackPtr s + 272) 144]

theorem prepareRound [Bindings] {entry s : RamState} {boundary : ReturnBoundary}
    {key info : ByteArray} {ptr : BitVec 64} {length n : Nat}
    (pre : ExpandPre entry boundary key info ptr length)
    (head : LoopState entry s boundary key info length n)
    (more : 32*n < length) (bound : length ≤ 8160) :
    ∃ t, SavedFrame entry t boundary length ∧
      t.RIP = (if n = 0 then 0x10f6c3 else 0x10f682) ∧
      (n ≠ 0 → t.regValue .rbx = 0) ∧ HmacAt t (stackPtr t + 272) key ByteArray.empty ∧
      slot t 8 = BitVec.ofNat 64 (length - 32*n) ∧
      slot t 264 = BitVec.ofNat 64 (min (length - 32*n) 32) ∧
      AgreesExcept (preparationComponents s) s t := by
  obtain ⟨u, stepU, readyU, pcU, remaining, chunk, frameU⟩ := roundLength pre head more bound
  have writesU : StackWrites [.reg 1,.flags,.mem (stackPtr s + 8) 8,.mem (stackPtr s + 264) 8,.rip]
      (stackPtr s) [(8,8),(264,8)] := by
    intro c hc a ha
    change c ∈ [.reg 1, .flags, .mem (stackPtr s + 8) 8, .mem (stackPtr s + 264) 8, .rip] at hc
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals first | exact ha.elim | exact ⟨(8,8), by decide, ha⟩ | exact ⟨(264,8), by decide, ha⟩
  have savedU := (writesU.saved pre (by omega) bound head.toSavedFrame stepU readyU frameU
    (by decide) (by simp)).1
  have spU : stackPtr u = stackPtr s := frameU.read (n := 64) (r := 4) (by simp)
  have slotU (off : Nat) (low : 272 ≤ off ∨ (16 ≤ off ∧ off + 8 ≤ 264)) (hi : off ≤ 536) :
      slot u (BitVec.ofNat 64 off) = slot s (BitVec.ofNat 64 off) := by
    change memLoad u.external (stackPtr u + _) 64 = _
    rw [spU]
    apply agrees_memLoad (writesU.agrees frameU (by omega) (by decide) ?_)
    intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl <;> dsimp <;> omega
  have geometry := clonePre pre (by omega) bound savedU pcU
    ((slotU 240 (by decide) (by decide)).trans head.contextPtr)
    ((slotU 424 (by decide) (by decide)).trans head.innerPtr)
    ((slotU 416 (by decide) (by decide)).trans head.outerPtr)
  obtain ⟨v, stepV, readyV, pcV, frameV, hmacV⟩ := ContextClone.clone_hmac geometry readyU
    savedU.loaded pre.call.outerBoundary (roundInputs pre savedU.frame (by omega) bound).1
  have writesV : StackWrites (ContextClone.components u) (stackPtr u) [(272,144)] := by
    intro c hc a ha
    simp only [ContextClone.components, List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | exact ha.elim | exact ⟨(272,144), by decide, ha⟩
  have savedV := (writesV.saved pre (by omega) bound savedU stepV readyV frameV (by decide)
    (by simp [ContextClone.components])).1
  have spV : stackPtr v = stackPtr u := frameV.read (n := 64) (r := 4) (by simp [ContextClone.components])
  have ctx := Counter.StackContext.of_pre pre (by omega) bound
  have read : MemReadable v (stackPtr v + 335) 1 := by
    rw [show stackPtr v = Counter.base entry from savedV.sp]
    exact Counter.read_stack ctx savedV.toRunning (off := 335) (by decide) (by decide)
  have flag : (v.regValue .rax).setWidth 8 = _ := (congrArg (fun x : BitVec 64 ↦ x.setWidth 8)
    (show v.regValue .rax = s.regValue .rax from (frameU.trans frameV).read
      (n := 64) (r := 0) (by simp [ContextClone.components]))).trans head.flag
  obtain ⟨fuel, t, stepT, readyT, pcT, bx, frameT⟩ := previousBranch readyV savedV.loaded pcV
    pre.call.outerBoundary flag hmacV read
  have noWrites : StackWrites [.reg 3,.flags,.rip] (stackPtr v) [] := by
    intro c hc a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl <;> exact ha.elim
  have savedT := (noWrites.saved pre (by omega) bound savedV stepT readyT frameT (by simp) (by decide)).1
  have spT : stackPtr t = stackPtr v := frameT.read (r := 4) (n := 64) (by decide)
  have memT := frameT.external (by simp [Component.Covers])
  have stable (off : Nat) (hi : off + 8 ≤ 272) : slot t (BitVec.ofNat 64 off) = slot u (BitVec.ofNat 64 off) := by
    change memLoad t.external (stackPtr t + _) 64 = _
    rw [spT, spV, memT]
    exact agrees_memLoad (writesV.agrees frameV (by omega) (by decide) (by
      intro r hr
      obtain rfl := List.mem_singleton.mp hr
      exact Or.inl hi))
  refine ⟨t, savedT, pcT, bx, ?_, (stable 8 (by decide)).trans remaining,
    (stable 264 (by decide)).trans chunk, ?_⟩
  · change HmacAt t (stackPtr t + 272) key ByteArray.empty
    rw [spT]
    apply hmacV.of_copy
    intro i hi
    rw [memT]
    rfl
  · have allFrames := (frameU.trans frameV).trans frameT
    change AgreesExcept (_ ++ [.reg 1,.reg 2,.reg 6,.reg 7,.mem (stackPtr u + 272) 144,.rip] ++ _) s t at allFrames
    rw [spU] at allFrames
    exact allFrames.mono (by simp [preparationComponents])

end Hkdf.Proofs.NewExpand.Expand
