import P256.Proofs.Nonce.Initialize.Conversions.Int2Octets.State
import P256.Proofs.Program.Pop
import X86Proofs.Instructions.Call.Triple

set_option autoImplicit false


namespace P256.Proofs.Nonce.Initialize.Conversions.Int2Octets

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure RestoreState [bindings : Bindings] (s t : RamState) : Prop where
  bindingsSupported : MachineRamUnitStrideDecodable bindings t
  machine : SupportedIntegerMachineState bindings.processor t
  loaded : ProgramLoaded t
  allocated : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome
  rsp : stackPtr t = stackPtr s - 48
  saved : ∀ entry ∈ savedRegisters,
    memLoad t.external (stackPtr s - BitVec.ofNat 64 entry.2) 64 = s.regValue entry.1
  returnAddress : memLoad t.external (stackPtr s) 64 = memLoad s.external (stackPtr s) 64

structure RestoreCode (offset : Nat) : Prop where
  bounded : offset + 11 ≤ 118431
  rbx : Extracted.textBytes.toListFrom offset 1 = encodePopR64 3
  r12 : Extracted.textBytes.toListFrom (offset + 1) 2 = encodePopR64 12
  r13 : Extracted.textBytes.toListFrom (offset + 3) 2 = encodePopR64 13
  r14 : Extracted.textBytes.toListFrom (offset + 5) 2 = encodePopR64 14
  r15 : Extracted.textBytes.toListFrom (offset + 7) 2 = encodePopR64 15
  rbp : Extracted.textBytes.toListFrom (offset + 9) 1 = encodePopR64 5
  ret : Extracted.textBytes.toListFrom (offset + 10) 1 = [0xc3]

def restoreComponents : List Component :=
  [.reg 3, .reg 4, .reg 5, .reg 12, .reg 13, .reg 14, .reg 15, .rip]

theorem restore_registers [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {entry : BitVec 64} {inputBytes outputBytes reserve codeOffset : Nat}
    {inputRegister : Syntax.Reg}
    (pre : CalleePre s boundary entry inputBytes outputBytes reserve inputRegister)
    (hreserve : 48 ≤ reserve) (state : RestoreState s t) (code : RestoreCode codeOffset)
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 codeOffset) :
    ∃ u, Advances boundary 7 t u ∧ ReadyToStep u ∧
      AgreesExcept restoreComponents t u ∧
      u.RIP = (returnBoundary s).rip ∧ stackPtr u = (returnBoundary s).rsp ∧
      (∀ r ∈ [Syntax.Reg.rbx, .rbp, .r12, .r13, .r14, .r15],
        u.regValue r = s.regValue r) := by
  have loaded := programLoaded_codeIn state.loaded
  have read (offset : Nat) (ho : offset ≤ 48) :
      MemReadable t (stackPtr s - BitVec.ofNat 64 offset) 8 :=
    readable_of_grow
      (stack_sub_readable pre.stack (by omega) (by omega)) state.allocated
  have read1 : MemReadable t (stackPtr t) 8 := by
    rw [state.rsp]
    exact (read 48 (by decide))
  obtain ⟨t1, run1, ready1, effect1⟩ :=
    (pop_register_effect_step
      (Extracted.textAddress + BitVec.ofNat 64 codeOffset) 3 (by decide)).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (loaded) codeOffset (encodePopR64 3)
        (by have h := code.bounded; change codeOffset + 1 ≤ 118431; omega) code.rbx)
      ⟨rip, read1⟩ (by
        change (Extracted.textAddress + BitVec.ofNat 64 codeOffset) + BitVec.ofNat 64 1 ≠ boundary.rip
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]
        exact boundary_ne_program pre.outerBoundary
          (inProgram_of_textOffset (codeOffset + 1) (by have h := code.bounded; omega)))
  have frame1 : AgreesExcept [.reg 3, .reg 4, .rip] t t1 := effect1.agrees
  have memory1 : t1.external = t.external :=
    (frame1.external (by simp [Component.Covers]))
  have rip1 : t1.RIP = Extracted.textAddress + BitVec.ofNat 64 (codeOffset + 1) := by
    have h : t1.RIP = (Extracted.textAddress + BitVec.ofNat 64 codeOffset) + BitVec.ofNat 64 1 := effect1.rip
    rw [BitVec.add_assoc, ← BitVec.ofNat_add] at h
    simpa only [Nat.add_assoc] using h
  have rsp1 : stackPtr t1 = stackPtr s - 40 := by
    have hw : stackPtr t1 = stackPtr t + 8 := effect1.writes.2
    rw [hw, state.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have value1 : (Operand.reg 3 : Operand 64).read t1 = s.regValue .rbx := by
    have hw : (Operand.reg 3 : Operand 64).read t1 =
        memLoad t.external (stackPtr t) 64 := effect1.writes.1
    rw [hw, state.rsp]
    exact state.saved (.rbx, 48) (by simp [savedRegisters])
  have read2 : MemReadable t1 (stackPtr t1) 8 := by
    rw [rsp1]
    exact (read 40 (by decide)).of_external_eq memory1
  obtain ⟨t2, run2, ready2, effect2⟩ :=
    (pop_register_effect_step
      (Extracted.textAddress + BitVec.ofNat 64 (codeOffset + 1)) 12 (by decide)).advances
      ready1
      (programText_slice (loaded.of_external_eq memory1) (codeOffset + 1) (encodePopR64 12)
        (by have h := code.bounded; change (codeOffset + 1) + 2 ≤ 118431; omega) code.r12)
      ⟨rip1, read2⟩ (by
        change (Extracted.textAddress + BitVec.ofNat 64 (codeOffset + 1)) + BitVec.ofNat 64 2 ≠ boundary.rip
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]
        exact boundary_ne_program pre.outerBoundary
          (inProgram_of_textOffset ((codeOffset + 1) + 2) (by have h := code.bounded; omega)))
  have frame2 : AgreesExcept [.reg 12, .reg 4, .rip] t1 t2 := effect2.agrees
  have memory2 : t2.external = t.external :=
    (frame2.external (by simp [Component.Covers])).trans memory1
  have rip2 : t2.RIP = Extracted.textAddress + BitVec.ofNat 64 (codeOffset + 3) := by
    have h : t2.RIP = (Extracted.textAddress + BitVec.ofNat 64 (codeOffset + 1)) + BitVec.ofNat 64 2 := effect2.rip
    rw [BitVec.add_assoc, ← BitVec.ofNat_add] at h
    simpa only [Nat.add_assoc] using h
  have rsp2 : stackPtr t2 = stackPtr s - 32 := by
    have hw : stackPtr t2 = stackPtr t1 + 8 := effect2.writes.2
    rw [hw, rsp1]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have value2 : (Operand.reg 12 : Operand 64).read t2 = s.regValue .r12 := by
    have hw : (Operand.reg 12 : Operand 64).read t2 =
        memLoad t1.external (stackPtr t1) 64 := effect2.writes.1
    rw [hw, rsp1, memory1]
    exact state.saved (.r12, 40) (by simp [savedRegisters])
  have read3 : MemReadable t2 (stackPtr t2) 8 := by
    rw [rsp2]
    exact (read 32 (by decide)).of_external_eq memory2
  obtain ⟨t3, run3, ready3, effect3⟩ :=
    (pop_register_effect_step
      (Extracted.textAddress + BitVec.ofNat 64 (codeOffset + 3)) 13 (by decide)).advances
      ready2
      (programText_slice (loaded.of_external_eq memory2) (codeOffset + 3) (encodePopR64 13)
        (by have h := code.bounded; change (codeOffset + 3) + 2 ≤ 118431; omega) code.r13)
      ⟨rip2, read3⟩ (by
        change (Extracted.textAddress + BitVec.ofNat 64 (codeOffset + 3)) + BitVec.ofNat 64 2 ≠ boundary.rip
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]
        exact boundary_ne_program pre.outerBoundary
          (inProgram_of_textOffset ((codeOffset + 3) + 2) (by have h := code.bounded; omega)))
  have frame3 : AgreesExcept [.reg 13, .reg 4, .rip] t2 t3 := effect3.agrees
  have memory3 : t3.external = t.external :=
    (frame3.external (by simp [Component.Covers])).trans memory2
  have rip3 : t3.RIP = Extracted.textAddress + BitVec.ofNat 64 (codeOffset + 5) := by
    have h : t3.RIP = (Extracted.textAddress + BitVec.ofNat 64 (codeOffset + 3)) + BitVec.ofNat 64 2 := effect3.rip
    rw [BitVec.add_assoc, ← BitVec.ofNat_add] at h
    simpa only [Nat.add_assoc] using h
  have rsp3 : stackPtr t3 = stackPtr s - 24 := by
    have hw : stackPtr t3 = stackPtr t2 + 8 := effect3.writes.2
    rw [hw, rsp2]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have value3 : (Operand.reg 13 : Operand 64).read t3 = s.regValue .r13 := by
    have hw : (Operand.reg 13 : Operand 64).read t3 =
        memLoad t2.external (stackPtr t2) 64 := effect3.writes.1
    rw [hw, rsp2, memory2]
    exact state.saved (.r13, 32) (by simp [savedRegisters])
  have read4 : MemReadable t3 (stackPtr t3) 8 := by
    rw [rsp3]
    exact (read 24 (by decide)).of_external_eq memory3
  obtain ⟨t4, run4, ready4, effect4⟩ :=
    (pop_register_effect_step
      (Extracted.textAddress + BitVec.ofNat 64 (codeOffset + 5)) 14 (by decide)).advances
      ready3
      (programText_slice (loaded.of_external_eq memory3) (codeOffset + 5) (encodePopR64 14)
        (by have h := code.bounded; change (codeOffset + 5) + 2 ≤ 118431; omega) code.r14)
      ⟨rip3, read4⟩ (by
        change (Extracted.textAddress + BitVec.ofNat 64 (codeOffset + 5)) + BitVec.ofNat 64 2 ≠ boundary.rip
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]
        exact boundary_ne_program pre.outerBoundary
          (inProgram_of_textOffset ((codeOffset + 5) + 2) (by have h := code.bounded; omega)))
  have frame4 : AgreesExcept [.reg 14, .reg 4, .rip] t3 t4 := effect4.agrees
  have memory4 : t4.external = t.external :=
    (frame4.external (by simp [Component.Covers])).trans memory3
  have rip4 : t4.RIP = Extracted.textAddress + BitVec.ofNat 64 (codeOffset + 7) := by
    have h : t4.RIP = (Extracted.textAddress + BitVec.ofNat 64 (codeOffset + 5)) + BitVec.ofNat 64 2 := effect4.rip
    rw [BitVec.add_assoc, ← BitVec.ofNat_add] at h
    simpa only [Nat.add_assoc] using h
  have rsp4 : stackPtr t4 = stackPtr s - 16 := by
    have hw : stackPtr t4 = stackPtr t3 + 8 := effect4.writes.2
    rw [hw, rsp3]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have value4 : (Operand.reg 14 : Operand 64).read t4 = s.regValue .r14 := by
    have hw : (Operand.reg 14 : Operand 64).read t4 =
        memLoad t3.external (stackPtr t3) 64 := effect4.writes.1
    rw [hw, rsp3, memory3]
    exact state.saved (.r14, 24) (by simp [savedRegisters])
  have read5 : MemReadable t4 (stackPtr t4) 8 := by
    rw [rsp4]
    exact (read 16 (by decide)).of_external_eq memory4
  obtain ⟨t5, run5, ready5, effect5⟩ :=
    (pop_register_effect_step
      (Extracted.textAddress + BitVec.ofNat 64 (codeOffset + 7)) 15 (by decide)).advances
      ready4
      (programText_slice (loaded.of_external_eq memory4) (codeOffset + 7) (encodePopR64 15)
        (by have h := code.bounded; change (codeOffset + 7) + 2 ≤ 118431; omega) code.r15)
      ⟨rip4, read5⟩ (by
        change (Extracted.textAddress + BitVec.ofNat 64 (codeOffset + 7)) + BitVec.ofNat 64 2 ≠ boundary.rip
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]
        exact boundary_ne_program pre.outerBoundary
          (inProgram_of_textOffset ((codeOffset + 7) + 2) (by have h := code.bounded; omega)))
  have frame5 : AgreesExcept [.reg 15, .reg 4, .rip] t4 t5 := effect5.agrees
  have memory5 : t5.external = t.external :=
    (frame5.external (by simp [Component.Covers])).trans memory4
  have rip5 : t5.RIP = Extracted.textAddress + BitVec.ofNat 64 (codeOffset + 9) := by
    have h : t5.RIP = (Extracted.textAddress + BitVec.ofNat 64 (codeOffset + 7)) + BitVec.ofNat 64 2 := effect5.rip
    rw [BitVec.add_assoc, ← BitVec.ofNat_add] at h
    simpa only [Nat.add_assoc] using h
  have rsp5 : stackPtr t5 = stackPtr s - 8 := by
    have hw : stackPtr t5 = stackPtr t4 + 8 := effect5.writes.2
    rw [hw, rsp4]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have value5 : (Operand.reg 15 : Operand 64).read t5 = s.regValue .r15 := by
    have hw : (Operand.reg 15 : Operand 64).read t5 =
        memLoad t4.external (stackPtr t4) 64 := effect5.writes.1
    rw [hw, rsp4, memory4]
    exact state.saved (.r15, 16) (by simp [savedRegisters])
  have read6 : MemReadable t5 (stackPtr t5) 8 := by
    rw [rsp5]
    exact (read 8 (by decide)).of_external_eq memory5
  obtain ⟨t6, run6, ready6, effect6⟩ :=
    (pop_register_effect_step
      (Extracted.textAddress + BitVec.ofNat 64 (codeOffset + 9)) 5 (by decide)).advances
      ready5
      (programText_slice (loaded.of_external_eq memory5) (codeOffset + 9) (encodePopR64 5)
        (by have h := code.bounded; change (codeOffset + 9) + 1 ≤ 118431; omega) code.rbp)
      ⟨rip5, read6⟩ (by
        change (Extracted.textAddress + BitVec.ofNat 64 (codeOffset + 9)) + BitVec.ofNat 64 1 ≠ boundary.rip
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]
        exact boundary_ne_program pre.outerBoundary
          (inProgram_of_textOffset ((codeOffset + 9) + 1) (by have h := code.bounded; omega)))
  have frame6 : AgreesExcept [.reg 5, .reg 4, .rip] t5 t6 := effect6.agrees
  have memory6 : t6.external = t.external :=
    (frame6.external (by simp [Component.Covers])).trans memory5
  have rip6 : t6.RIP = Extracted.textAddress + BitVec.ofNat 64 (codeOffset + 10) := by
    have h : t6.RIP = (Extracted.textAddress + BitVec.ofNat 64 (codeOffset + 9)) + BitVec.ofNat 64 1 := effect6.rip
    rw [BitVec.add_assoc, ← BitVec.ofNat_add] at h
    simpa only [Nat.add_assoc] using h
  have rsp6 : stackPtr t6 = stackPtr s - 0 := by
    have hw : stackPtr t6 = stackPtr t5 + 8 := effect6.writes.2
    rw [hw, rsp5]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have value6 : (Operand.reg 5 : Operand 64).read t6 = s.regValue .rbp := by
    have hw : (Operand.reg 5 : Operand 64).read t6 =
        memLoad t5.external (stackPtr t5) 64 := effect6.writes.1
    rw [hw, rsp5, memory5]
    exact state.saved (.rbp, 8) (by simp [savedRegisters])
  have rsp6' : stackPtr t6 = stackPtr s := by simpa using rsp6
  have read6' : MemReadable t6 (stackPtr t6) 8 := by
    rw [rsp6']
    simpa only [BitVec.sub_zero] using (read 0 (by decide)).of_external_eq memory6
  have top : stackTop t6 = (returnBoundary s).rip := by
    change memLoad t6.external (stackPtr t6) 64 = memLoad s.external (stackPtr s) 64
    rw [rsp6', memory6]
    exact state.returnAddress
  obtain ⟨u, run7, ready7, effect7⟩ :=
    (ret_effect_step (Extracted.textAddress + BitVec.ofNat 64 (codeOffset + 10))).advances
      ready6
      (programText_slice (loaded.of_external_eq memory6) (codeOffset + 10) [0xc3]
        (by have h := code.bounded; change codeOffset + 10 + 1 ≤ 118431; omega) code.ret)
      ⟨⟨rip6, read6'⟩, top ▸ inProgram_low pre.returnInProgram⟩
      (by change stackTop t6 ≠ boundary.rip
          rw [top]
          exact boundary_ne_program pre.outerBoundary pre.returnInProgram)
  refine ⟨u, (((((run1.trans run2).trans run3).trans run4).trans run5).trans run6).trans run7,
    ready7, ?_, effect7.rip.trans top, ?_, ?_⟩
  · apply (((((frame1.trans frame2).trans frame3).trans frame4).trans frame5).trans frame6 |>.trans effect7.agrees).mono
    simp [restoreComponents, retEffect, Effect.components, Write.component, Operand.component]
  · have hw : stackPtr u = stackPtr t6 + 8 := effect7.writes
    rw [hw, rsp6']
    rfl
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · change (Operand.reg 3 : Operand 64).read u = _
      rw [effect7.agrees.read (by simp), frame6.read (by simp), frame5.read (by simp), frame4.read (by simp), frame3.read (by simp), frame2.read (by simp)]
      exact value1
    · change (Operand.reg 5 : Operand 64).read u = _
      rw [effect7.agrees.read (by simp)]
      exact value6
    · change (Operand.reg 12 : Operand 64).read u = _
      rw [effect7.agrees.read (by simp), frame6.read (by simp), frame5.read (by simp), frame4.read (by simp), frame3.read (by simp)]
      exact value2
    · change (Operand.reg 13 : Operand 64).read u = _
      rw [effect7.agrees.read (by simp), frame6.read (by simp), frame5.read (by simp), frame4.read (by simp)]
      exact value3
    · change (Operand.reg 14 : Operand 64).read u = _
      rw [effect7.agrees.read (by simp), frame6.read (by simp), frame5.read (by simp)]
      exact value4
    · change (Operand.reg 15 : Operand 64).read u = _
      rw [effect7.agrees.read (by simp), frame6.read (by simp)]
      exact value5

end P256.Proofs.Nonce.Initialize.Conversions.Int2Octets
