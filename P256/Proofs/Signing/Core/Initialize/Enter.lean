import P256.Proofs.Signing.Core.Initialize.CallState
import P256.Proofs.Signing.Core.Initialize.Memory
import P256.Proofs.Program.Push
import P256.Proofs.Program.ScalarFrame.CallStep
import P256.Proofs.Common.EffectCompose.Memory

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Initialize

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open NextNonce (scalarFrame coreFrame base_add base_nat)

theorem word_after_push {s t u : RamState} {a : BitVec 64} {written offset : Nat}
    (agrees : AgreesExcept [.reg 4, .mem a 8, .rip] t u)
    (address : a = stackPtr s - BitVec.ofNat 64 written)
    (apart : OffsetsApart (-(BitVec.ofNat 64 written)) 8 (-(BitVec.ofNat 64 offset)) 8) :
    memLoad u.external (stackPtr s - BitVec.ofNat 64 offset) 64 =
      memLoad t.external (stackPtr s - BitVec.ofNat 64 offset) 64 := by
  apply memLoad_congr
  intro i hi
  apply congrArg (fun x : Option UInt8 => x.getD 0)
  apply agrees.memory
  intro c hc cover
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact cover.elim
  · obtain ⟨j, hj, eq⟩ := cover
    apply OffsetsApart.ne apart (stackPtr s) hj hi (by decide)
    simpa only [address, BitVec.sub_eq_add_neg] using eq.symm
  · exact cover.elim

theorem enter [Bindings] {s t : RamState} {boundary : ReturnBoundary} {secret : Nat}
    (pre : SignPre s boundary) (input : CallInput s t secret) (rip : t.RIP = 0x10ca68) :
    ∃ u, Advances boundary 3 t u ∧ Entered s t u := by
  obtain ⟨v, run1, ready1, loaded1, rip1, rsp1, agrees1, mem1⟩ :=
    push_exists pre.stack (pre.avoids _ (by simp)) pre.outerBoundary
      (readyToStep input.frame.machine input.frame.bindingsSupported) input.frame.loaded input.frame.allocated
      0 2280 0xca68 input.frame.rsp rip (by decide) (by decide) (by decide) (by decide +kernel)
  obtain ⟨w, run2, ready2, loaded2, rip2, rsp2, agrees2, mem2⟩ :=
    push_exists pre.stack (pre.avoids _ (by simp)) pre.outerBoundary ready1 loaded1
      (fun a ha => agrees1.grow a (input.frame.allocated a ha))
      3 2288 0xca69 rsp1 rip1 (by decide) (by decide) (by decide) (by decide +kernel)
  have address : pushAddr w = stackPtr s - 2304 := by
    rw [pushAddr, rsp2, BitVec.sub_sub]
    rfl
  obtain ⟨u, run3, ready3, effect⟩ := ScalarFrame.call_step pre.toCalleePre
    (frameOffset := 2296) (by decide) (by decide) ready2 loaded2
    (fun a ha => agrees2.grow a (agrees1.grow a (input.frame.allocated a ha)))
    rsp2 0xca6a 0xffffad21 (by decide) (by decide +kernel) (by decide)
    (inProgram_of_textOffset 0x7790 (by decide)) rip2
  change (callEffect (fun _ => 0x107790) 0x10ca6f w).Holds w u at effect
  have agrees : AgreesExcept [.reg 4, .mem (stackPtr s - 2288) 8,
      .mem (stackPtr s - 2296) 8, .mem (stackPtr s - 2304) 8, .rip] t u := by
    apply ((agrees1.trans agrees2).trans effect.agrees).mono
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      pushEffect_components, address]
    intro c hc
    rcases hc with ((rfl | rfl | rfl) | (rfl | rfl | rfl)) | (rfl | rfl | rfl) <;> simp
  have bytes (offset : Nat) (bound : offset < 2288) :
      u.external[frameBase s + BitVec.ofNat 64 offset]? =
        t.external[frameBase s + BitVec.ofNat 64 offset]? := by
    apply agrees.memory
    intro c hc cover
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact cover.elim
    all_goals
      obtain ⟨i, hi, eq⟩ := cover
      simp only [frameBase] at eq
      have eqn := congrArg BitVec.toNat
        ((BitVec.add_right_inj (stackPtr s)).mp (by
          simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc] using eq))
      simp only [BitVec.toNat_add, BitVec.toNat_neg, BitVec.toNat_ofNat, BitVec.reduceToNat] at eqn
      omega
  have sub2288 : (stackPtr s - 2288).toNat = (stackPtr s).toNat - 2288 :=
    stack_sub_toNat pre.stack (by decide)
  have sub2296 : (stackPtr s - 2296).toNat = (stackPtr s).toNat - 2296 :=
    stack_sub_toNat pre.stack (by decide)
  have sub2304 : (stackPtr s - 2304).toNat = (stackPtr s).toNat - 2304 :=
    stack_sub_toNat pre.stack (by decide)
  have writes : WritesWithin [.reg 4, .mem (stackPtr s - 2288) 8,
      .mem (stackPtr s - 2296) 8, .mem (stackPtr s - 2304) 8, .rip]
      #v[registerRegion s .rdi 65, Stack.region s 4584] := by
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    all_goals
      obtain ⟨i, hi, rfl⟩ := ha
      refine ⟨Stack.region s 4584, by simp, ?_⟩
      apply memoryRegion_contains_add pre.stack.1 (len := 8) _ _ hi
      · first | rw [sub2288] | rw [sub2296] | rw [sub2304]
        change (stackPtr s).toNat - 4584 ≤ _
        omega
      · rw [stack_region_end]
        first | rw [sub2288] | rw [sub2296] | rw [sub2304]
        omega
  have rsp : stackPtr u = frameBase s - 24 := by
    exact effect.writes.1.trans (address.trans (by simp only [frameBase, BitVec.sub_sub]; rfl))
  have total := memoryWriteFrame_trans input.frame.frame (agrees.memoryWriteFrame writes)
  have saved : ∀ entry ∈ Program.savedRegisters,
      (Operand.mem (stackPtr s - BitVec.ofNat 64 entry.2) : Operand 64).read u = s.regValue entry.1 := by
    intro entry he
    apply Eq.trans ?_ (input.frame.saved entry he)
    have bound : entry.2 ≤ 48 := by
      simp only [Program.savedRegisters, List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    have addr : stackPtr s - BitVec.ofNat 64 entry.2 = frameBase s + BitVec.ofNat 64 (2280-entry.2) :=
      (base_add s (by omega)).trans (by congr 2; omega) |>.symm
    rw [addr]
    apply memLoad_congr
    intro i hi
    change (u.external[_]?).getD 0 = (t.external[_]?).getD 0
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, bytes _ (by omega)]
  have ret : (Operand.mem (stackPtr s) : Operand 64).read u =
      (Operand.mem (stackPtr s) : Operand 64).read s := by
    apply Eq.trans ?_ input.frame.returnAddress
    have addr : stackPtr s = frameBase s + BitVec.ofNat 64 2280 := by
      simp only [frameBase, BitVec.ofNat_eq_ofNat, BitVec.sub_add_cancel]
    rw [addr]
    apply memLoad_congr
    intro i hi
    change (u.external[_]?).getD 0 = (t.external[_]?).getD 0
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, bytes _ (by omega)]
  refine ⟨u, (run1.trans run2).trans run3,
    ⟨⟨bindingsSupported_of_ready_agrees input.frame.bindingsSupported ready3 agrees,
      supportedMachine_of_ready_agrees input.frame.machine ready3 agrees,
      ScalarFrame.loaded_of_frame pre.toCalleePre total,
      agrees.directionFlagClear (by simp) input.frame.directionFlag,
      fun a ha => agrees.grow a (input.frame.allocated a ha), total,
      effect.writes.1.trans address, saved, ret,
      (agrees.mxcsr (by simp)).trans input.frame.mxcsr,
      (agrees.fcw (by simp)).trans input.frame.fp87⟩,
      bytes, ?_, effect.rip, (callEffect_stack effect).1, ?_, ?_⟩⟩
  · intro r hr
    have h : (Operand.reg (BitVec.ofNat 5 r.fin.val) : Operand 64).read u =
        (Operand.reg (BitVec.ofNat 5 r.fin.val) : Operand 64).read t :=
      agrees.read (by cases r <;> simp_all [Syntax.Reg.fin] <;> decide)
    cases r <;> exact h
  · have readable := readable_of_grow
      (stack_sub_readable pre.stack
        (offset := 2296) (len := 8) (by decide) (by decide))
      (fun a ha => agrees.grow a (input.frame.allocated a ha))
    have load : memLoad u.external (stackPtr s - 2296) 64 = 0 := by
      have copy : memLoad u.external (stackPtr s - 2296) 64 =
          memLoad w.external (stackPtr s - 2296) 64 :=
        word_after_push (t := w) (u := u) (written := 2304) (offset := 2296) (by simpa only [pushEffect_components] using effect.agrees) address (by unfold OffsetsApart; decide +kernel :
        OffsetsApart (-(2304 : BitVec 64)) 8 (-2296) 8)
      rw [copy, mem2]
      change memLoad (memStore v.external (stackPtr s - 2296) (v.regValue .rbx))
        (stackPtr s - 2296) 64 = 0
      rw [memLoad_memStore _ _ (by decide) (by decide)]
      exact (agrees1.read (n := 64) (r := 3) (by simp)).trans input.rbx
    have addr : u.regValue .rsp + 8 = stackPtr s - 2296 := by
      change stackPtr u + 8 = _
      rw [rsp, frameBase, BitVec.sub_sub]
      simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
      rfl
    rw [addr]
    exact (Bytes.of_memLoad (n := 64) readable.mem).loadBytes64.trans (congrArg Except.ok load)
  · have readable := readable_of_grow
      (stack_sub_readable pre.stack
        (offset := 2288) (len := 8) (by decide) (by decide))
      (fun a ha => agrees.grow a (input.frame.allocated a ha))
    have load : memLoad u.external (stackPtr s - 2288) 64 = frameBase s + 272 := by
      have copy : memLoad u.external (stackPtr s - 2288) 64 =
          memLoad w.external (stackPtr s - 2288) 64 :=
        word_after_push (t := w) (u := u) (written := 2304) (offset := 2288) (by simpa only [pushEffect_components] using effect.agrees) address (by unfold OffsetsApart; decide +kernel :
        OffsetsApart (-(2304 : BitVec 64)) 8 (-2288) 8)
      rw [copy, mem2]
      simp only [BitVec.sub_eq_add_neg]
      rw [memLoad_memStore_apart _ _ _ _ _ 64
        (by unfold OffsetsApart; decide +kernel : OffsetsApart (-(2296 : BitVec 64)) 8 (-2288) 8)
        (by decide) (by decide)]
      rw [mem1]
      simp only [← BitVec.sub_eq_add_neg, Nat.reduceAdd, BitVec.reduceSetWidth]
      rw [show (2288 : BitVec 64) = BitVec.ofNat 64 2288 from rfl]
      rw [memLoad_memStore _ _ (n := 64) (by decide) (by decide)]
      exact input.rax
    have addr : u.regValue .rsp + 16 = stackPtr s - 2288 := by
      change stackPtr u + 16 = _
      rw [rsp, frameBase, BitVec.sub_sub]
      simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
      rfl
    rw [addr]
    exact (Bytes.of_memLoad (n := 64) readable.mem).loadBytes64.trans (congrArg Except.ok load)

end P256.Proofs.Signing.Core.Initialize
