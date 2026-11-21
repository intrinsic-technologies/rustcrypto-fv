import P256.Proofs.Program.Push
import X86Proofs.Instructions.Call.Triple

set_option autoImplicit false

namespace P256.Proofs.Program

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [Bindings] {s t : RamState} {boundary : ReturnBoundary} {reserve : Nat}
variable (hStack : Stack.Valid s reserve)
  (hAvoid : (Stack.region s reserve).Avoids (fun a => InProgram a ∨ InPageTables a))
  (hOuter : ¬ InProgram boundary.rip) (ready : ReadyToStep t) (loaded : ProgramLoaded t)
  (grow : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome)

include hStack hAvoid hOuter ready loaded grow in
theorem call_rel32_exists (offset codeOffset : Nat) (disp : BitVec 32)
    (hsp : stackPtr t = stackPtr s - BitVec.ofNat 64 offset)
    (hip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 codeOffset)
    (hoffset : offset + 8 ≤ reserve) (halign : (offset + 8) % 8 = 0)
    (hsize : codeOffset + 5 ≤ 118431)
    (hbytes : Extracted.textBytes.toListFrom codeOffset 5 = encodeCallRel32 disp)
    (htarget : InProgram (branchTarget (Extracted.textAddress + BitVec.ofNat 64 codeOffset)
      5 (disp.signExtend 64))) :
    ∃ u, Advances boundary 1 t u ∧ ReadyToStep u ∧ ProgramLoaded u ∧
      (callEffect (fun _ => branchTarget (Extracted.textAddress + BitVec.ofNat 64 codeOffset)
        5 (disp.signExtend 64)) (Extracted.textAddress + BitVec.ofNat 64 codeOffset + 5) t).Holds t u ∧
      u.external = memStore t.external (stackPtr s - BitVec.ofNat 64 (offset + 8))
        (Extracted.textAddress + BitVec.ofNat 64 codeOffset + 5) := by
  have haddr : pushAddr t = stackPtr s - BitVec.ofNat 64 (offset + 8) := by
    rw [pushAddr, hsp, BitVec.sub_sub, BitVec.ofNat_add]
    rfl
  have hcontains (i : Nat) (hi : i < 8) :
      (Stack.region s reserve).Contains (pushAddr t + BitVec.ofNat 64 i).toNat := by
    rw [haddr]
    apply memoryRegion_contains_add hStack.1 (len := 8) _ _ hi
    · rw [stack_sub_toNat hStack hoffset]
      change (stackPtr s).toNat - reserve ≤ (stackPtr s).toNat - (offset + 8)
      omega
    · rw [stack_region_end, stack_sub_toNat hStack hoffset]
      omega
  have hp : PushPre (Extracted.textAddress + BitVec.ofNat 64 codeOffset) 5 t := by
    refine ⟨hip, ?_, ?_⟩
    · rw [haddr]
      exact writable_of_grow (stack_sub_writable8 hStack
        (fun a ha hpage => hAvoid a ha (.inr hpage)) hoffset halign) grow
    · intro i hi j hj he
      apply hAvoid _ (hcontains i hi) (.inl ?_)
      rw [he, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact inProgram_of_textOffset (codeOffset + j) (by omega)
  have code := programText_slice (programLoaded_codeIn loaded) codeOffset
    (encodeCallRel32 disp) hsize hbytes
  have hlow := inProgram_low htarget
  obtain ⟨u, step, ru, effect⟩ := call_rel32_effect_step _ disp hlow t ready code hp
  have run : Advances boundary 1 t u :=
    Advances.of_step step (.inl (by
      rw [effect.rip]
      exact boundary_ne_program hOuter htarget))
  have loadedu : ProgramLoaded u := by
    intro a b hf
    rw [effect.agrees.byte]
    · exact loaded a b hf
    · intro c hc hv
      simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact hv.elim
      · obtain ⟨i, hi, rfl⟩ := hv
        exact hAvoid _ (hcontains i hi) (.inl ⟨b, hf⟩)
      · exact hv.elim
  refine ⟨u, run, ru, loadedu, effect, ?_⟩
  have direct := call_rel32_step t ready disp (by rw [hip]; exact code.bytesAt)
    (by rw [hip]; exact code.low (by simp [encodeCallRel32]) (by simp [encodeCallRel32]))
    (by rw [hip]; exact hlow) hp.write
  rw [step] at direct
  cases direct
  rw [afterStep_call_external, haddr, hip]
  rfl

end P256.Proofs.Program
