import Hkdf.Proofs.Common.CallFrame.Stack
import Hkdf.Proofs.Common.Machine.StackRegion
import X86Proofs.Instructions.MovStore.Triple

set_option autoImplicit false

namespace Hkdf.Proofs.Common.ExtractCaller.Spill

open Hkdf.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.CallFrame

theorem store [bindings : Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {reserve offset codeOffset : Nat} {src : BitVec 5} {am : AddrMode} {bytes : List UInt8}
    (stack : Stack.Valid initial reserve)
    (avoid : (Stack.region initial reserve).Avoids
      (fun a ↦ InProgram a ∨ Hkdf.Proofs.Program.InPageTables a))
    (running : Running initial boundary #v[Stack.region initial reserve] s)
    (outside : ¬ InProgram boundary.rip)
    (step : StepEffect
      (StorePre (Extracted.textAddress + BitVec.ofNat 64 codeOffset) (3 + am.tail.length)
        (storeAddrAt (Extracted.textAddress + BitVec.ofNat 64 codeOffset) am (3 + am.tail.length)) 8)
      (codeRange (Extracted.textAddress + BitVec.ofNat 64 codeOffset) bytes)
      (movM64R64Effect (Extracted.textAddress + BitVec.ofNat 64 codeOffset) src am))
    (code : CodeIn (codeRange (Extracted.textAddress + BitVec.ofNat 64 codeOffset) bytes) s)
    (rip : s.RIP = Extracted.textAddress + BitVec.ofNat 64 codeOffset)
    (address : storeAddrAt (Extracted.textAddress + BitVec.ofNat 64 codeOffset) am
      (3 + am.tail.length) s = stackPtr initial - BitVec.ofNat 64 offset)
    (capacity : offset ≤ reserve) (room : 8 ≤ offset) (aligned : offset % 8 = 0)
    (bounded : codeOffset + (3 + am.tail.length) < 115149) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧
      Running initial boundary #v[Stack.region initial reserve] t ∧
      (movM64R64Effect (Extracted.textAddress + BitVec.ofNat 64 codeOffset) src am s).Holds s t ∧
      t.RIP = Extracted.textAddress + BitVec.ofNat 64 codeOffset +
        BitVec.ofNat 64 (3 + am.tail.length) ∧ stackPtr t = stackPtr s := by
  have writable : MemWritable s (storeAddrAt
      (Extracted.textAddress + BitVec.ofNat 64 codeOffset) am (3 + am.tail.length) s) 8 := by
    rw [address]
    exact stack_writable8 stack avoid running.allocated capacity aligned
  have apart : RangeApart (storeAddrAt
      (Extracted.textAddress + BitVec.ofNat 64 codeOffset) am (3 + am.tail.length) s) 8
      (Extracted.textAddress + BitVec.ofNat 64 codeOffset) (3 + am.tail.length) := by
    rw [address]
    exact stack_codeApart stack (fun a ha hp ↦ avoid a ha (.inl hp)) capacity
      (by omega) (by omega)
  obtain ⟨t, run, ready, effect⟩ := step.advances
    (Hkdf.Proofs.Common.Machine.supportedMachine_readyToStep running.machine) code
    ⟨rip, writable, apart⟩ (by
      change Extracted.textAddress + BitVec.ofNat 64 codeOffset +
        BitVec.ofNat 64 (3 + am.tail.length) ≠ boundary.rip
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact boundary_ne_program outside (inProgram_of_textOffset _ bounded))
  have writes : WritesWithin
      (movM64R64Effect (Extracted.textAddress + BitVec.ofNat 64 codeOffset) src am s).components
      #v[Stack.region initial reserve] := by
    intro c hc a ha
    simp only [movM64R64Effect_components, address, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact ⟨Stack.region initial reserve, by simp,
        Hkdf.Proofs.Common.Machine.stackRegion_contains_sub stack.2.2.1 capacity room ha⟩
    · exact ha.elim
  refine ⟨t, run, ready, running.of_agrees run ready effect.agrees writes ?_ ?_,
    effect, effect.rip, ?_⟩
  · intro region member
    have equal : region = Stack.region initial reserve := by simpa using member
    subst region
    exact fun a ha hp ↦ avoid a ha (.inl hp)
  · simp only [movM64R64Effect_components, List.mem_cons, List.not_mem_nil,
      or_false, reduceCtorEq, not_false_eq_true]
  · exact effect.agrees.read (n := 64) (r := 4) (by simp)

def standardEffect (s : RamState) : Effect :=
  { rip := 0x101445
    writes := [
      ⟨(.mem (rspOf s + 96) : Operand 64), (Operand.reg 9 : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 112) : Operand 64), (Operand.reg 2 : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 8) : Operand 64), (Operand.reg 6 : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 104) : Operand 64), (Operand.reg 7 : Operand 64).read s⟩] }

def simpleEffect (s : RamState) : Effect :=
  { rip := 0x105c9c
    writes := [
      ⟨(.mem (rspOf s + 232) : Operand 64), (Operand.reg 9 : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 248) : Operand 64), (Operand.reg 2 : Operand 64).read s⟩,
      ⟨(.reg 12 : Operand 64), (Operand.reg 6 : Operand 64).read s⟩,
      ⟨(.mem (rspOf s + 240) : Operand 64), (Operand.reg 7 : Operand 64).read s⟩] }

theorem standard [bindings : Bindings] {initial s : RamState}
    {salt : Option ByteArray} {inputs : Array Input}
    (call : ValidExtractCall hkdfSha256Extract initial salt inputs)
    (running : Running initial (returnBoundary initial)
      #v[Stack.region initial hkdfSha256Extract.minStackBytes] s)
    (outside : ¬ InProgram (returnBoundary initial).rip)
    (rsp : stackPtr s = stackPtr initial - 520)
    (rip : s.RIP = 0x101431) :
    ∃ t, Advances (returnBoundary initial) 4 s t ∧ ReadyToStep t ∧
      Running initial (returnBoundary initial)
        #v[Stack.region initial hkdfSha256Extract.minStackBytes] t ∧
      (standardEffect s).Holds s t ∧ stackPtr t = stackPtr s ∧
      t.RIP = 0x101445 ∧
      t.regValue .rcx = s.regValue .rcx ∧ t.regValue .r8 = s.regValue .r8 := by
  have avoid : (Stack.region initial hkdfSha256Extract.minStackBytes).Avoids
      (fun a ↦ InProgram a ∨ Hkdf.Proofs.Program.InPageTables a) :=
    (call.stackSeparation.2 _ (by simp)).2
  obtain ⟨s1, run1, ready1, running1, effect1, ip1, sp1⟩ :=
    store (offset := 424) (codeOffset := 0x1431) (src := 9)
      (am := .sib 4 none 0 (.d8 96)) call.stack avoid running outside
      (mov_m64_r64_effect_step 0x101431 0x4c (by simp [RexWPrefix]) 1
        (.sib 4 none 0 (.d8 96)) (by decide) rfl rfl)
      (programText_slice (programLoaded_codeIn running.loaded) 0x1431 _
        (by decide) (by decide +kernel)) rip (by
        change stackPtr s + 96 = stackPtr initial - 424
        rw [rsp]
        simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd])
      (by decide +kernel) (by decide) (by decide) (by decide)
  have rsp1 : stackPtr s1 = stackPtr initial - 520 := sp1.trans rsp
  obtain ⟨s2, run2, ready2, running2, effect2, ip2, sp2⟩ :=
    store (offset := 408) (codeOffset := 0x1436) (src := 2)
      (am := .sib 4 none 0 (.d8 112)) call.stack avoid running1 outside
      (mov_m64_r64_effect_step 0x101436 0x48 (by simp [RexWPrefix]) 2
        (.sib 4 none 0 (.d8 112)) (by decide) rfl rfl)
      (programText_slice (programLoaded_codeIn running1.loaded) 0x1436 _
        (by decide) (by decide +kernel)) ip1 (by
        change stackPtr s1 + 112 = stackPtr initial - 408
        rw [rsp1]
        simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd])
      (by decide +kernel) (by decide) (by decide) (by decide)
  have rsp2 : stackPtr s2 = stackPtr initial - 520 := sp2.trans rsp1
  obtain ⟨s3, run3, ready3, running3, effect3, ip3, sp3⟩ :=
    store (offset := 512) (codeOffset := 0x143b) (src := 6)
      (am := .sib 4 none 0 (.d8 8)) call.stack avoid running2 outside
      (mov_m64_r64_effect_step 0x10143b 0x48 (by simp [RexWPrefix]) 6
        (.sib 4 none 0 (.d8 8)) (by decide) rfl rfl)
      (programText_slice (programLoaded_codeIn running2.loaded) 0x143b _
        (by decide) (by decide +kernel)) ip2 (by
        change stackPtr s2 + 8 = stackPtr initial - 512
        rw [rsp2]
        simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd])
      (by decide +kernel) (by decide) (by decide) (by decide)
  have rsp3 : stackPtr s3 = stackPtr initial - 520 := sp3.trans rsp2
  obtain ⟨s4, run4, ready4, running4, effect4, ip4, sp4⟩ :=
    store (offset := 416) (codeOffset := 0x1440) (src := 7)
      (am := .sib 4 none 0 (.d8 104)) call.stack avoid running3 outside
      (mov_m64_r64_effect_step 0x101440 0x48 (by simp [RexWPrefix]) 7
        (.sib 4 none 0 (.d8 104)) (by decide) rfl rfl)
      (programText_slice (programLoaded_codeIn running3.loaded) 0x1440 _
        (by decide) (by decide +kernel)) ip3 (by
        change stackPtr s3 + 104 = stackPtr initial - 416
        rw [rsp3]
        simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd])
      (by decide +kernel) (by decide) (by decide) (by decide)
  have rsp4 : stackPtr s4 = stackPtr initial - 520 := sp4.trans rsp3
  have composed := ((effect1.seq (by x86_local) (by apply Effect.Local.full; repeat first | (solve | x86_local) | apply Effect.Local.seq) effect2).seq
    (by x86_local) (by apply Effect.Local.full; repeat first | (solve | x86_local) | apply Effect.Local.seq) effect3).seq (by x86_local) (by apply Effect.Local.full; repeat first | (solve | x86_local) | apply Effect.Local.seq) effect4
  have effect : (standardEffect s).Holds s s4 := by
    apply composed.weaken
    · x86_norm [standardEffect, rspOf]
    · x86_norm [standardEffect, rspOf]
    · intro i
      cases i <;> x86_norm [standardEffect, rspOf]
    · x86_norm [standardEffect, rspOf]
  refine ⟨s4, ((run1.trans run2).trans run3).trans run4, ready4, running4, effect,
    ((sp4.trans sp3).trans sp2).trans sp1, effect.rip, ?_, ?_⟩
  · exact effect.agrees.read (n := 64) (r := 1) (by simp [standardEffect, Effect.components])
  · exact effect.agrees.read (n := 64) (r := 8) (by simp [standardEffect, Effect.components])

theorem simple [bindings : Bindings] {initial s : RamState}
    {salt : Option ByteArray} {inputs : Array Input}
    (call : ValidExtractCall simpleHkdfSha256Extract initial salt inputs)
    (running : Running initial (returnBoundary initial)
      #v[Stack.region initial simpleHkdfSha256Extract.minStackBytes] s)
    (outside : ¬ InProgram (returnBoundary initial).rip)
    (rsp : stackPtr s = stackPtr initial - 536)
    (rip : s.RIP = 0x105c81) :
    ∃ t, Advances (returnBoundary initial) 4 s t ∧ ReadyToStep t ∧
      Running initial (returnBoundary initial)
        #v[Stack.region initial simpleHkdfSha256Extract.minStackBytes] t ∧
      (simpleEffect s).Holds s t ∧ stackPtr t = stackPtr s ∧
      t.RIP = 0x105c9c ∧
      t.regValue .rcx = s.regValue .rcx ∧ t.regValue .r8 = s.regValue .r8 := by
  have avoid : (Stack.region initial simpleHkdfSha256Extract.minStackBytes).Avoids
      (fun a ↦ InProgram a ∨ Hkdf.Proofs.Program.InPageTables a) :=
    (call.stackSeparation.2 _ (by simp)).2
  obtain ⟨s1, run1, ready1, running1, effect1, ip1, sp1⟩ :=
    store (offset := 304) (codeOffset := 0x5c81) (src := 9)
      (am := .sib 4 none 0 (.d32 232)) call.stack avoid running outside
      (mov_m64_r64_effect_step 0x105c81 0x4c (by simp [RexWPrefix]) 1
        (.sib 4 none 0 (.d32 232)) (by decide) rfl rfl)
      (programText_slice (programLoaded_codeIn running.loaded) 0x5c81 _
        (by decide) (by decide +kernel)) rip (by
        change stackPtr s + 232 = stackPtr initial - 304
        rw [rsp]
        simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd])
      (by decide +kernel) (by decide) (by decide) (by decide)
  have rsp1 : stackPtr s1 = stackPtr initial - 536 := sp1.trans rsp
  obtain ⟨s2, run2, ready2, running2, effect2, ip2, sp2⟩ :=
    store (offset := 288) (codeOffset := 0x5c89) (src := 2)
      (am := .sib 4 none 0 (.d32 248)) call.stack avoid running1 outside
      (mov_m64_r64_effect_step 0x105c89 0x48 (by simp [RexWPrefix]) 2
        (.sib 4 none 0 (.d32 248)) (by decide) rfl rfl)
      (programText_slice (programLoaded_codeIn running1.loaded) 0x5c89 _
        (by decide) (by decide +kernel)) ip1 (by
        change stackPtr s1 + 248 = stackPtr initial - 288
        rw [rsp1]
        simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd])
      (by decide +kernel) (by decide) (by decide) (by decide)
  have rsp2 : stackPtr s2 = stackPtr initial - 536 := sp2.trans rsp1
  obtain ⟨s3, run3, ready3, effect3⟩ :=
    (mov_r64_r64_effect_step 0x105c91 0x49 0xf4
      (by simp [RexWPrefix]) rfl).advances ready2
      (programText_slice (programLoaded_codeIn running2.loaded) 0x5c91
        [0x49, 0x89, 0xf4] (by decide) (by decide +kernel)) ip2
      (boundary_ne_program outside (inProgram_of_textOffset 0x5c94 (by decide)))
  change (movR64R64Effect 0x105c91 12 6 s2).Holds s2 s3 at effect3
  have running3 := running2.of_agrees run3 ready3 effect3.agrees (by
    intro c hc a ha
    have cases : c = .reg 12 ∨ c = .rip := by simpa using hc
    rcases cases with rfl | rfl <;> exact ha.elim) (by
      intro region member
      have eq : region = Stack.region initial simpleHkdfSha256Extract.minStackBytes := by simpa using member
      subst region
      exact fun a ha hp ↦ avoid a ha (.inl hp)) (by simp)
  have sp3 : stackPtr s3 = stackPtr s2 :=
    effect3.agrees.read (n := 64) (r := 4) (by simp)
  have rsp3 : stackPtr s3 = stackPtr initial - 536 := sp3.trans rsp2
  have ip3 : s3.RIP = 0x105c94 := effect3.rip
  obtain ⟨s4, run4, ready4, running4, effect4, ip4, sp4⟩ :=
    store (offset := 296) (codeOffset := 0x5c94) (src := 7)
      (am := .sib 4 none 0 (.d32 240)) call.stack avoid running3 outside
      (mov_m64_r64_effect_step 0x105c94 0x48 (by simp [RexWPrefix]) 7
        (.sib 4 none 0 (.d32 240)) (by decide) rfl rfl)
      (programText_slice (programLoaded_codeIn running3.loaded) 0x5c94 _
        (by decide) (by decide +kernel)) ip3 (by
        change stackPtr s3 + 240 = stackPtr initial - 296
        rw [rsp3]
        simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg, BitVec.reduceAdd])
      (by decide +kernel) (by decide) (by decide) (by decide)
  have rsp4 : stackPtr s4 = stackPtr initial - 536 := sp4.trans rsp3
  have composed := ((effect1.seq (by x86_local) (by apply Effect.Local.full; repeat first | (solve | x86_local) | apply Effect.Local.seq) effect2).seq
    (by x86_local) (by apply Effect.Local.full; repeat first | (solve | x86_local) | apply Effect.Local.seq) effect3).seq (by x86_local) (by apply Effect.Local.full; repeat first | (solve | x86_local) | apply Effect.Local.seq) effect4
  have effect : (simpleEffect s).Holds s s4 := by
    apply composed.weaken
    · x86_norm [simpleEffect, rspOf]
    · x86_norm [simpleEffect, rspOf]
    · intro i
      cases i <;> x86_norm [simpleEffect, rspOf]
    · x86_norm [simpleEffect, rspOf]
  refine ⟨s4, ((run1.trans run2).trans run3).trans run4, ready4, running4, effect,
    ((sp4.trans sp3).trans sp2).trans sp1, effect.rip, ?_, ?_⟩
  · exact effect.agrees.read (n := 64) (r := 1) (by simp [simpleEffect, Effect.components])
  · exact effect.agrees.read (n := 64) (r := 8) (by simp [simpleEffect, Effect.components])

end Hkdf.Proofs.Common.ExtractCaller.Spill
