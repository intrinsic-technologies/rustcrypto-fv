import Hkdf.Proofs.Common.CallFrame.Push
import Hkdf.Proofs.NewExpand.Wrapper.Frame

namespace Hkdf.Proofs.NewExpand.Wrapper

open Hkdf.Spec.Program Hkdf.Proofs.Program Hkdf.Proofs.Common
open Hkdf.Proofs.Common.CallFrame Hkdf.Proofs.Common.Machine
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

private abbrev unchangedRegisters (initial s : RamState) :=
  ∀ r : Syntax.Reg, r ≠ .rsp → s.regValue r = initial.regValue r

private theorem pushRegister [Bindings] {initial s : RamState}
    (stack : Stack.Valid initial hkdfSha256NewExpandMinStackBytes)
    (avoid : (Stack.region initial hkdfSha256NewExpandMinStackBytes).Avoids
      (fun a ↦ InProgram a ∨ InPageTables a))
    (outer : ¬ InProgram (returnBoundary initial).rip)
    (run : Wrapper.Running initial s) (regs : unchangedRegisters initial s)
    (src : Syntax.Reg) (notRsp : src ≠ .rsp) (offset codeOffset : Nat)
    (rsp : stackPtr s = stackPtr initial - BitVec.ofNat 64 offset)
    (rip : s.RIP = Extracted.textAddress + BitVec.ofNat 64 codeOffset)
    (capacity : offset + 8 ≤ 48) (aligned : (offset + 8) % 8 = 0)
    (bound : codeOffset + (encodePushR64 (BitVec.ofNat 4 src.fin.val)).length < 115149)
    (bytes : Extracted.textBytes.toListFrom codeOffset
        (encodePushR64 (BitVec.ofNat 4 src.fin.val)).length =
      encodePushR64 (BitVec.ofNat 4 src.fin.val)) :
    ∃ t, Wrapper.Running initial t ∧ unchangedRegisters initial t ∧
      t.RIP = Extracted.textAddress + BitVec.ofNat 64
        (codeOffset + (encodePushR64 (BitVec.ofNat 4 src.fin.val)).length) ∧
      stackPtr t = stackPtr initial - BitVec.ofNat 64 (offset + 8) ∧
      t.external = memStore s.external (stackPtr initial - BitVec.ofNat 64 (offset + 8))
        (initial.regValue src) := by
  have push := CallFrame.push_steps stack (by decide) avoid outer
  obtain ⟨t, step, ready, _, ip, sp, frame, mem⟩ := push.run
    (supportedMachine_readyToStep run.machine) run.loaded run.allocated
    (BitVec.ofNat 4 src.fin.val) offset codeOffset rsp rip capacity aligned bound bytes
  have writes : WritesWithin
      [.reg 4, .mem (stackPtr initial - BitVec.ofNat 64 (offset + 8)) 8, .rip]
      #v[Stack.region initial hkdfSha256NewExpandMinStackBytes] := by
    apply CallFrame.stack_slot_within stack (offset := offset + 8) (len := 8)
      (Nat.le_trans capacity (by decide)) (by omega)
    intro c hc a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl
    · exact ha.elim
    · exact ha
    · exact ha.elim
  refine ⟨t, run.of_agrees step ready frame writes (CallFrame.stack_avoids avoid)
    (by simp), ?_, ip, sp, ?_⟩
  · intro r hr
    apply Eq.trans _ (regs r hr)
    have index : BitVec.ofNat 5 r.fin.val ≠ 4 := by
      cases r <;> first | decide | exact (hr rfl).elim
    have same := frame.read (n := 64) (r := BitVec.ofNat 5 r.fin.val)
      (by simpa using index)
    cases r <;> exact same
  · have read : (Operand.reg ((BitVec.ofNat 4 src.fin.val).setWidth 5) : Operand 64).read s =
        s.regValue src := by cases src <;> rfl
    rwa [read, regs src notRsp] at mem

theorem saveRegisters [bindings : Bindings]
    {initial : RamState} {salt : Option ByteArray} {ikm info : ByteArray} {length : Nat}
    (hCall : ValidDeriveKeyCall Extracted.hkdfSha256NewExpandAddress
      hkdfSha256NewExpandMinStackBytes initial salt ikm info length)
    (machine : SupportedMachine bindings initial) (outer : ¬ InProgram (returnBoundary initial).rip) :
    ∃ t, Wrapper.Running initial t ∧ t.RIP = 0x101fd9 ∧
      stackPtr t = stackPtr initial - 40 ∧ SavedFrame initial t ∧
      (∀ r : Syntax.Reg, r ≠ .rsp → t.regValue r = initial.regValue r) := by
  have avoid := (hCall.stackSeparation.2 _ (Vector.mem_singleton_self _)).2
  have start : Wrapper.Running initial initial :=
    CallFrame.Running.initial machine hCall.programLoaded hCall.directionFlagUnset
  obtain ⟨s1, run1, regs1, ip1, sp1, mem1⟩ :=
    pushRegister hCall.stack avoid outer start (fun _ _ ↦ rfl) .r15 (by decide) 0 0x1fd0
      (by simp) hCall.entry (by decide) (by decide) (by decide) (by decide +kernel)
  obtain ⟨s2, run2, regs2, ip2, sp2, mem2⟩ :=
    pushRegister hCall.stack avoid outer run1 regs1 .r14 (by decide) 8 0x1fd2
      sp1 ip1 (by decide) (by decide) (by decide) (by decide +kernel)
  obtain ⟨s3, run3, regs3, ip3, sp3, mem3⟩ :=
    pushRegister hCall.stack avoid outer run2 regs2 .r13 (by decide) 16 0x1fd4
      sp2 ip2 (by decide) (by decide) (by decide) (by decide +kernel)
  obtain ⟨s4, run4, regs4, ip4, sp4, mem4⟩ :=
    pushRegister hCall.stack avoid outer run3 regs3 .r12 (by decide) 24 0x1fd6
      sp3 ip3 (by decide) (by decide) (by decide) (by decide +kernel)
  obtain ⟨t, run, regs, ip, sp, mem⟩ :=
    pushRegister hCall.stack avoid outer run4 regs4 .rbx (by decide) 32 0x1fd8
      sp4 ip4 (by decide) (by decide) (by decide) (by decide +kernel)
  refine ⟨t, run, ip, sp, ⟨regs .rbp (by decide), ?_, ?_, ?_, ?_, ?_, ?_⟩, regs⟩
  all_goals
    rw [mem, mem4, mem3, mem2, mem1]
    simp only [BitVec.sub_eq_add_neg, Nat.reduceAdd]
  case refine_6 =>
    change memLoad _ _ 64 = memLoad initial.external (stackPtr initial) 64
    repeat rw [memLoad_memStore_apart_right _ _ _ _ 64
      (by unfold OffsetsApart; decide +kernel) (by decide) (by decide)]
  all_goals
    repeat rw [memLoad_memStore_apart _ _ _ _ _ 64
      (by unfold OffsetsApart; decide +kernel) (by decide) (by decide)]
    exact memLoad_memStore _ _ (by decide) (by decide) _

end Hkdf.Proofs.NewExpand.Wrapper
