import P256.Proofs.Program.ScalarFrame.Memory
import X86Proofs.Instructions.Call.Triple

set_option autoImplicit false

namespace P256.Proofs.Program.ScalarFrame

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open P256.Proofs.Program
open X86 X86.Machine X86.UserProcess X86Proofs

variable {entry : BitVec 64} {inputBytes outputBytes stackReserve frameOffset : Nat}

variable {inputRegister : Syntax.Reg}

theorem call_step [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary entry inputBytes outputBytes stackReserve inputRegister)
    (hframe : frameOffset + 8 ≤ stackReserve) (halign : (frameOffset + 8) % 8 = 0)
    (ready : ReadyToStep t) (loaded : ProgramLoaded t)
    (allocated : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome)
    (rsp : stackPtr t = stackPtr s - BitVec.ofNat 64 frameOffset)
    (offset : Nat) (disp : BitVec 32)
    (hsize : offset + 5 ≤ 118431)
    (hbytes : Extracted.textBytes.toListFrom offset 5 = encodeCallRel32 disp)
    (hlow : (branchTarget (Extracted.textAddress + BitVec.ofNat 64 offset) 5
      (disp.signExtend 64)).toNat < 2^32)
    (htarget : InProgram (branchTarget (Extracted.textAddress + BitVec.ofNat 64 offset) 5
      (disp.signExtend 64)))
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 offset) :
    ∃ u, Advances boundary 1 t u ∧ ReadyToStep u ∧
      (callEffect (fun _ => branchTarget (Extracted.textAddress + BitVec.ofNat 64 offset) 5
        (disp.signExtend 64)) (Extracted.textAddress + BitVec.ofNat 64 offset + 5) t).Holds t u := by
  have hpushAddr : pushAddr t = stackPtr s - BitVec.ofNat 64 (frameOffset + 8) := by
    simp only [pushAddr, rsp, BitVec.sub_sub, BitVec.ofNat_add]
    rfl
  have hpush : PushPre (Extracted.textAddress + BitVec.ofNat 64 offset) 5 t := by
    refine ⟨rip, ?_, ?_⟩
    · rw [hpushAddr]
      exact P256.Proofs.Program.writable_of_grow (P256.Proofs.Program.stack_sub_writable8 pre.stack
        (fun a ha hp => pre.avoids (Stack.region s stackReserve) (by simp) a ha (.inr hp))
        (offset := frameOffset + 8) hframe halign) allocated
    · rw [hpushAddr]
      intro i hi j hj he
      apply pre.avoids (Stack.region s stackReserve) (by simp)
        (stackPtr s - BitVec.ofNat 64 (frameOffset + 8) + BitVec.ofNat 64 i)
      · exact stack_contains pre (offset := frameOffset + 8) hframe (by omega) ⟨i, hi, rfl⟩
      · apply Or.inl
        rw [he, BitVec.add_assoc, ← BitVec.ofNat_add]
        exact inProgram_of_textOffset (offset + j) (by omega)
  exact (call_rel32_effect_step _ disp hlow).advances ready
    (programText_slice (programLoaded_codeIn loaded) offset (encodeCallRel32 disp) hsize hbytes)
    hpush (boundary_ne_program pre.outerBoundary htarget)

theorem call_byte {s t u : RamState} {target : RamState → BitVec 64}
    {ret : BitVec 64}
    (hlow : frameOffset + 16 ≤ 2^64)
    (rsp : stackPtr t = stackPtr s - BitVec.ofNat 64 frameOffset)
    (effect : (callEffect target ret t).Holds t u)
    {offset len : Nat} (ho : offset ≤ frameOffset) (hl : len ≤ offset + 8) {i : Nat} (hi : i < len) :
    u.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      t.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  have hpushAddr : pushAddr t = stackPtr s - BitVec.ofNat 64 (frameOffset + 8) := by
    simp only [pushAddr, rsp, BitVec.sub_sub, BitVec.ofNat_add]
    rfl
  apply effect.agrees.byte
  intro c hc hv
  simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact hv.elim
  · obtain ⟨j, hj, he⟩ := hv
    rw [hpushAddr] at he
    have ha : stackPtr s - BitVec.ofNat 64 offset =
        (stackPtr s - BitVec.ofNat 64 (frameOffset + 8)) + BitVec.ofNat 64 ((frameOffset + 8)-offset) := by
      rw [← BitVec.ofNat_sub_ofNat_of_le (frameOffset + 8) offset (by omega) (by omega)]
      simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
      rw [← BitVec.add_assoc (-(BitVec.ofNat 64 (frameOffset + 8))),
        show -(BitVec.ofNat 64 (frameOffset + 8)) + BitVec.ofNat 64 (frameOffset + 8) = 0#64 by
          rw [BitVec.add_comm, ← BitVec.sub_eq_add_neg, BitVec.sub_self], BitVec.zero_add]
    apply RangeApart.offsets (stackPtr s - BitVec.ofNat 64 (frameOffset + 8)) (a := 0) (b := (frameOffset + 8)-offset)
      (len := 8) (count := len) (by decide) (by omega) (.inl (by omega)) j hj i hi
    rw [show BitVec.ofNat 64 0 = 0#64 by rfl, BitVec.add_zero, ← ha]
    exact he.symm
  · exact hv.elim

end P256.Proofs.Program.ScalarFrame
