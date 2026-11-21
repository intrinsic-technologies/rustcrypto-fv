import P256.Proofs.SignatureFromSlice.Wrapper.Epilogue.State
import P256.Proofs.Program.Pop
import X86Proofs.Instructions.Add.Generated.Imm8.Triple
import X86Proofs.Instructions.Call.Triple

set_option autoImplicit false

namespace P256.Proofs.SignatureFromSlice.Wrapper.Return

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure RestoreCode (offset stackOffset : Nat) (locals : BitVec 8) : Prop where
  size : offset + 8 ≤ 118431
  amount : BitVec.ofNat 64 stackOffset = 16 + locals.signExtend 64
  add : Extracted.textBytes.toListFrom offset 4 = [0x48, 0x83, 0xc4] ++ immBytes 8 locals
  rbx : Extracted.textBytes.toListFrom (offset + 4) (encodePopR64 3).length = encodePopR64 3
  r14 : Extracted.textBytes.toListFrom (offset + 5) (encodePopR64 14).length = encodePopR64 14
  ret : Extracted.textBytes.toListFrom (offset + 7) 1 = [0xc3]

set_option maxRecDepth 2048 in
set_option maxHeartbeats 800000 in
theorem restore [bindings : Bindings] {initial t : RamState} {stackOffset reserve : Nat}
    {locals : BitVec 8} (state : State initial t stackOffset)
    (stack : Stack.Valid initial reserve) (space : 16 ≤ reserve)
    (outside : ¬ InProgram (returnBoundary initial).rip)
    (low : (returnBoundary initial).rip.toNat < 2^32)
    (offset : Nat) (bytes : RestoreCode offset stackOffset locals)
    (rip : t.RIP = (0x100000 : BitVec 64) + BitVec.ofNat 64 offset) :
    ∃ u, Returns (returnBoundary initial) 4 t u ∧
      SupportedIntegerMachineState bindings.processor u ∧
      MachineRamUnitStrideDecodable bindings u ∧
      CalleeSavedRegistersUnchanged initial u ∧ DirectionFlagUnset u ∧
      u.external = t.external ∧ u.regValue .rax = t.regValue .rax := by
  let p : BitVec 64 := 0x100000 + BitVec.ofNat 64 offset
  have next (i : Nat) (hi : i ≤ 7) : p + BitVec.ofNat 64 i ≠ (returnBoundary initial).rip := by
    apply boundary_ne_program outside
    change InProgram (0x100000 + BitVec.ofNat 64 offset + BitVec.ofNat 64 i)
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact inProgram_of_textOffset (offset + i) (by have := bytes.size; omega)
  have code := programLoaded_codeIn state.loaded
  have hc1 : CodeIn (codeRange p ([0x48, 0x83, 0xc4] ++ immBytes 8 locals)) t :=
    programText_slice code offset _ (by simpa using Nat.le_trans (Nat.add_le_add_left (by decide : 4 ≤ 8) offset) bytes.size) bytes.add
  obtain ⟨a, ha, ra, ea⟩ :=
    (add_r64_imm8_effect_step p 0x48 0xc4 locals
      (by simp [RexWPrefix]) (by decide) (by decide)).advances
      (readyToStep state.machine state.bindingsSupported) hc1 rip (next 4 (by decide))
  change (addR64Imm8Effect p 4 locals t).Holds t a at ea
  have ma : a.external = t.external := ea.agrees.external (by simp [Component.Covers])
  have spa : stackPtr a = stackPtr initial - 16 := by
    have hw : stackPtr a = stackPtr t + locals.signExtend 64 := ea.writes
    rw [hw, state.rsp, bytes.amount, ← BitVec.sub_sub, BitVec.sub_add_cancel]
  have readable (u : RamState) (hm : u.external = t.external) (off : Nat) (ho : off ≤ reserve) :
      MemReadable u (stackPtr initial - BitVec.ofNat 64 off) 8 :=
    (readable_of_grow (stack_sub_readable stack ho (by omega)) state.allocated).of_external_eq hm
  have hca : CodeIn (codeRange (p+4) (encodePopR64 3)) a := by
    have h := programText_slice (code.of_external_eq ma) (offset+4) (encodePopR64 3)
      (by have := bytes.size; change offset + 4 + 1 ≤ 118431; omega)
      bytes.rbx
    simpa only [p, Extracted.textAddress, BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using h
  obtain ⟨b, hb, rb, eb⟩ := (pop_register_effect_step (p+4) 3 (by decide)).advances ra hca
    ⟨ea.rip, by rw [spa]; exact readable a ma 16 (by omega)⟩
    (by change p + 4 + 1 ≠ _; simpa only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using next 5 (by decide))
  change (popR64Effect (p+4) 1 3 a).Holds a b at eb
  have mb : b.external = t.external :=
    (eb.agrees.external (by simp [Component.Covers])).trans ma
  have spb : stackPtr b = stackPtr initial - 8 := by
    have hw : stackPtr b = stackPtr a + 8 := eb.writes.2
    rw [hw, spa]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have bx : b.regValue .rbx = initial.regValue .rbx := by
    have hw : b.regValue .rbx = memLoad a.external (stackPtr a) 64 := eb.writes.1
    rw [hw, spa, ma]
    exact state.savedRbx
  have hcb : CodeIn (codeRange (p+5) (encodePopR64 14)) b := by
    have h := programText_slice (code.of_external_eq mb) (offset+5) (encodePopR64 14)
      (by have := bytes.size; change offset + 5 + 2 ≤ 118431; omega)
      bytes.r14
    simpa only [p, Extracted.textAddress, BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using h
  obtain ⟨c, hc, rc, ec⟩ := (pop_register_effect_step (p+5) 14 (by decide)).advances rb hcb
    ⟨by simpa only [popR64Effect, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using eb.rip,
      by rw [spb]; exact readable b mb 8 (by omega)⟩
    (by change p + 5 + 2 ≠ _; simpa only [BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using next 7 (by decide))
  change (popR64Effect (p+5) 2 14 b).Holds b c at ec
  have mc : c.external = t.external :=
    (ec.agrees.external (by simp [Component.Covers])).trans mb
  have spc : stackPtr c = stackPtr initial := by
    have hw : stackPtr c = stackPtr b + 8 := ec.writes.2
    rw [hw, spb]
    exact BitVec.sub_add_cancel _ _
  have r14 : c.regValue .r14 = initial.regValue .r14 := by
    have hw : c.regValue .r14 = memLoad b.external (stackPtr b) 64 := ec.writes.1
    rw [hw, spb, mb]
    exact state.savedR14
  have top : stackTop c = (returnBoundary initial).rip := by
    rw [stackTop, spc]
    change memLoad c.external (stackPtr initial) 64 = _
    rw [mc]
    exact state.returnAddress
  have hcc : CodeIn (codeRange (p+7) [0xc3]) c := by
    have h := programText_slice (code.of_external_eq mc) (offset+7) [0xc3]
      (by have := bytes.size; change offset + 7 + 1 ≤ 118431; omega)
      bytes.ret
    simpa only [p, Extracted.textAddress, BitVec.ofNat_add, ← BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using h
  obtain ⟨u, step, ready, effect⟩ := (ret_effect_step (p+7)) c rc hcc
    ⟨⟨by simpa only [popR64Effect, BitVec.add_assoc, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using ec.rip,
       by rw [spc]; simpa only [BitVec.sub_zero] using readable c mc 0 (by omega)⟩,
     by rw [top]; exact low⟩
  have ret : Returns (returnBoundary initial) 1 c u := Returns.of_step step
    (effect.rip.trans top) (by
      change stackPtr u = stackPtr initial + 8
      have hw : stackPtr u = stackPtr c + 8 := effect.writes
      rw [hw, spc])
  have frame := ((ea.agrees.trans eb.agrees).trans ec.agrees).trans effect.agrees
  refine ⟨u, ((ha.trans hb).trans hc).returns ret,
    supportedMachine_of_ready_agrees state.machine ready frame,
    bindingsSupported_of_ready_agrees state.bindingsSupported ready frame,
    ?_, frame.directionFlagClear (by simp) state.directionFlag,
    frame.external (by simp [Component.Covers]), frame.read (n := 64) (r := 0) (by simp)⟩
  intro r hr
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
  · exact (effect.agrees.read (n := 64) (r := 3) (by simp)).trans
      ((ec.agrees.read (n := 64) (r := 3) (by simp)).trans bx)
  · exact (frame.read (n := 64) (r := 5) (by simp)).trans (state.otherRegisters .rbp (by simp))
  · exact (frame.read (n := 64) (r := 12) (by simp)).trans (state.otherRegisters .r12 (by simp))
  · exact (frame.read (n := 64) (r := 13) (by simp)).trans (state.otherRegisters .r13 (by simp))
  · exact (effect.agrees.read (n := 64) (r := 14) (by simp)).trans r14
  · exact (frame.read (n := 64) (r := 15) (by simp)).trans (state.otherRegisters .r15 (by simp))

end P256.Proofs.SignatureFromSlice.Wrapper.Return
