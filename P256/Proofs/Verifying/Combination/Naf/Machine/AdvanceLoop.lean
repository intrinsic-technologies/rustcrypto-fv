import P256.Proofs.Verifying.Combination.Naf.Interface
import P256.Proofs.Verifying.Combination.Naf.Machine.LoopState
import P256.Proofs.Verifying.Combination.Naf.Machine.Header
import P256.Proofs.Verifying.Combination.Naf.Iterator.Advance

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Machine

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Proofs.Program

theorem header_index {i : Nat} (hi : i < 256) :
    (BitVec.ofNat 64 i >>> 6) = BitVec.ofNat 64 (i/64) ∧
      (((BitVec.ofNat 64 i).setWidth 32 &&& 63).setWidth 64) = BitVec.ofNat 64 (i%64) := by
  constructor
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_ushiftRight, BitVec.toNat_ofNat, Nat.shiftRight_eq_div_pow]
    change i % 18446744073709551616 / 64 = i/64 % 18446744073709551616
    omega
  · apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_and, BitVec.toNat_ofNat]
    change ((i % 18446744073709551616 % 4294967296) &&& (2^6-1)) % 18446744073709551616 =
      i%64%18446744073709551616
    rw [Nat.and_two_pow_sub_one_eq_mod]
    omega

theorem advance_pre [Bindings] {s t : RamState} {boundary : ReturnBoundary} {q : Nat}
    (pre : Pre s boundary) (state : FrameState s t 144)
    (rip : t.RIP = 0x1181b0) (dst : t.regValue .rdi = stackPtr s-88)
    (requested : t.regValue .rsi = BitVec.ofNat 64 q) (bound : q < 4)
    (ret : InProgram (returnBoundary t).rip) :
    Iterator.AdvancePre t boundary (s.regValue .rdx) := by
  have bounds := stack_bounds pre.stack
  have hsp : (stackPtr t).toNat = (stackPtr s).toNat-144 := by
    rw [state.rsp]
    exact stack_sub_toNat pre.stack (by decide)
  have hout : (t.regValue .rdi).toNat = (stackPtr s).toNat-88 := by
    rw [dst]
    exact stack_sub_toNat pre.stack (by decide)
  refine ⟨iterator_pre pre state rip dst ?_ ?_ ?_ ret, pre.sourceBounded, ?_, ?_, ?_⟩
  · change (t.regValue .rsi).toNat+0 < 2^32
    rw [requested, BitVec.toNat_ofNat]
    omega
  · intro a ha
    change (t.regValue .rsi).toNat ≤ a.toNat ∧ a.toNat < (t.regValue .rsi).toNat+0 at ha
    omega
  · intro a ha
    change (t.regValue .rsi).toNat ≤ a ∧ a < (t.regValue .rsi).toNat+0 at ha
    omega
  · intro a ha
    exact Option.isSome_iff_exists.mp (state.allocated a
      (Option.isSome_iff_exists.mpr (pre.sourceAllocated a ha)))
  · intro a hin ho
    apply pre.sourceStack a hin
    change (t.regValue .rdi).toNat ≤ a ∧ a < (t.regValue .rdi).toNat+40 at ho
    change (stackPtr s).toNat-168 ≤ a ∧ a < (Stack.region s 168).start+(Stack.region s 168).size
    rw [hout] at ho
    rw [stack_region_end]
    constructor <;> omega
  · intro a hin hs
    apply pre.sourceStack a hin
    change (stackPtr t).toNat-24 ≤ a ∧ a < (Stack.region t 24).start+(Stack.region t 24).size at hs
    change (stackPtr s).toNat-168 ≤ a ∧ a < (Stack.region s 168).start+(Stack.region s 168).size
    rw [stack_region_end, hsp] at hs
    rw [stack_region_end]
    constructor <;> omega

theorem advance_loop [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {n i k c : Nat} {ds : List Int} (pre : Pre s boundary)
    (input : Nat256At s (s.regValue .rdx) n) (state : LoopState s t n i k c ds) :
    ∃ fuel u, Advances boundary fuel t u ∧ LoopState s u n i (i/64) c ds 0x10f3fe ∧
      u.regValue .rax = Iterator.word n (i/64) ∧
      u.regValue .rdx = Iterator.word n (i/64+1) ∧
      u.regValue .rbx = BitVec.ofNat 64 (i%64) := by
  obtain ⟨fuelH, h, runH, readyH, _, effectH⟩ := header_block boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0xf3e7 headerBytes
      (by decide) (by decide +kernel)) state.rip
  have noMem : ∀ comp ∈ (headerEffect t).components, ∀ a, ¬comp.Covers a := by
    simp [headerEffect, Effect.components, Component.Covers]
  have stateH := state.toFrameState.after_registers readyH effectH.agrees noMem
    (by simp [headerEffect, Effect.components])
  have memH := effectH.agrees.external noMem
  have hw := effectH.writes
  change h.regValue .rsi = t.regValue .r15 >>> 6 ∧
    h.regValue .rbx = ((t.regValue .r15).setWidth 32 &&& 63).setWidth 64 ∧
    h.regValue .rdi = stackPtr t+48#64 at hw
  rw [state.r15, (header_index state.indexBound).1, (header_index state.indexBound).2,
    stack_address state.rsp (offset := 48) (by decide)] at hw
  obtain ⟨entry, runC, readyC, rawC⟩ := direct_call pre.toCalleePre stateH 0xf3f9 0x8db2
    (by decide) (by decide +kernel) (by decide +kernel)
    (inProgram_of_textOffset 0x181b0 (by decide)) effectH.rip
  have effectC : (callEffect (fun _ => 0x1181b0) 0x10f3fe h).Holds h entry := rawC
  have stateC := FrameState.after_call pre.toCalleePre stateH readyC effectC
  have dst : entry.regValue .rdi = stackPtr s-88 :=
    (effectC.agrees.read (n := 64) (r := 7) (by simp)).trans hw.2.2
  have req : entry.regValue .rsi = BitVec.ofNat 64 (i/64) :=
    (effectC.agrees.read (n := 64) (r := 6) (by simp)).trans hw.1
  have ret : (returnBoundary entry).rip = 0x10f3fe := (callEffect_stack effectC).1
  have cp := advance_pre pre stateC effectC.rip dst req
    (by have := state.indexBound; omega)
    (by rw [ret]; exact inProgram_of_textOffset 0xf3fe (by decide))
  have iteratorC : Iterator.StateAt entry (entry.regValue .rdi) (s.regValue .rdx) n k := by
    rw [dst]
    have read (offset : Nat) (bound : offset ≤ 136) :
        memLoad entry.external (stackPtr s-BitVec.ofNat 64 offset) 64 =
          memLoad t.external (stackPtr s-BitVec.ofNat 64 offset) 64 := by
      have hc := call_read stateH effectC (n := 64) bound (by omega)
      change memLoad entry.external _ 64 = memLoad h.external _ 64 at hc
      rw [hc, memH]
    have addr (a : BitVec 64) (o : BitVec 64) : a-88+o = a-(88-o) := by
      simp only [BitVec.sub_eq_add_neg, BitVec.neg_add, BitVec.neg_neg, BitVec.add_assoc]
    constructor
    · exact (read 88 (by decide)).trans state.iterator.pointer
    · rw [addr]
      exact (read 80 (by decide)).trans (by simpa only [addr, BitVec.reduceSub] using state.iterator.remaining)
    · rw [addr]
      exact (read 72 (by decide)).trans (by simpa only [addr, BitVec.reduceSub] using state.iterator.index)
    · rw [addr]
      exact (read 64 (by decide)).trans (by simpa only [addr, BitVec.reduceSub] using state.iterator.low)
    · rw [addr]
      exact (read 56 (by decide)).trans (by simpa only [addr, BitVec.reduceSub] using state.iterator.high)
  obtain ⟨u, result, iteratorU, ux, ud, sourceU⟩ := Iterator.advance_correct cp
    (source_preserved pre stateC input) iteratorC req state.cachedIndex
    (by have := state.indexBound; omega)
  have stateU := FrameState.after_iterator pre stateC result dst
  rw [dst] at iteratorU
  have preserved (r : Syntax.Reg) (hr : r ∈ [Syntax.Reg.rbx, .rbp, .r12, .r13, .r14, .r15]) :
      u.regValue r = h.regValue r := by
    apply (result.calleeSaved r hr).trans
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact effectC.agrees.read (n := 64) (r := 3) (by simp)
    · exact effectC.agrees.read (n := 64) (r := 5) (by simp)
    · exact effectC.agrees.read (n := 64) (r := 12) (by simp)
    · exact effectC.agrees.read (n := 64) (r := 13) (by simp)
    · exact effectC.agrees.read (n := 64) (r := 14) (by simp)
    · exact effectC.agrees.read (n := 64) (r := 15) (by simp)
  have localRead {offset width : Nat} (ho : offset ≤ 136) (hl : width/8 ≤ offset+8)
      (apart : offset+40 ≤ 88 ∨ 88+width/8 ≤ offset) :
      memLoad u.external (stackPtr s-BitVec.ofNat 64 offset) width =
        memLoad t.external (stackPtr s-BitVec.ofNat 64 offset) width := by
    have hc := call_read stateH effectC (n := width) ho hl
    change memLoad entry.external _ width = memLoad h.external _ width at hc
    rw [iterator_result_read pre stateC result dst ho hl apart, hc, memH]
  have frameH : MemoryWriteFrame t h #v[Stack.region s 168] := by
    intro a _
    rw [memH]
  have frameC := effectC.agrees.memoryWriteFrame (call_writes pre.toCalleePre stateH)
  have frameU := iterator_result_stack pre stateC result dst
  have memory := memoryWriteFrame_trans (memoryWriteFrame_trans frameH frameC) frameU
  have outputU : DigitsAt u (s.regValue .rdi) ds := by
    intro j hj
    apply Eq.trans ?_ (state.output j hj)
    apply memLoad_congr
    intro k hk
    have zero : k=0 := by omega
    subst k
    simp only [BitVec.add_zero]
    change (u.external[s.regValue .rdi+BitVec.ofNat 64 j]?).getD 0 = _
    rw [memory _]
    · rfl
    · intro region hr hin
      have eq : region = Stack.region s 168 := by simpa using hr
      subst region
      exact pre.separation (1 : Fin 3) (2 : Fin 3) (by decide) _
        (memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) hj) hin
  obtain ⟨fuelA, runA⟩ := result.execution
  refine ⟨fuelH+1+fuelA, u, (runH.trans runC).trans runA, ?_, ux, ud,
    (preserved .rbx (by simp)).trans hw.2.1⟩
  refine ⟨stateU, result.rip.trans ret, state.indexBound, state.carryBound, Or.inl rfl,
    state.dsLength, state.specification, sourceU, outputU, iteratorU, ?_, ?_, ?_, ?_, ?_,
    (localRead (by decide) (by decide) (by decide)).trans state.outputLength,
    (localRead (by decide) (by decide) (by decide)).trans state.outputPointer,
    (localRead (by decide) (by decide) (by decide)).trans state.bits,
    (localRead (by decide) (by decide) (by decide)).trans state.half,
    (localRead (by decide) (by decide) (by decide)).trans state.mask,
    (localRead (by decide) (by decide) (by decide)).trans state.byteWindow⟩
  · exact (preserved .r12 (by simp)).trans ((effectH.agrees.read (n := 64) (r := 12)
      (by simp [headerEffect, Effect.components])).trans state.r12)
  · exact (preserved .r13 (by simp)).trans ((effectH.agrees.read (n := 64) (r := 13)
      (by simp [headerEffect, Effect.components])).trans state.r13)
  · exact (preserved .r14 (by simp)).trans ((effectH.agrees.read (n := 64) (r := 14)
      (by simp [headerEffect, Effect.components])).trans state.r14)
  · exact (preserved .r15 (by simp)).trans ((effectH.agrees.read (n := 64) (r := 15)
      (by simp [headerEffect, Effect.components])).trans state.r15)
  · exact (preserved .rbp (by simp)).trans ((effectH.agrees.read (n := 64) (r := 5)
      (by simp [headerEffect, Effect.components])).trans state.rbp)

end P256.Proofs.Verifying.Combination.Naf.Machine
