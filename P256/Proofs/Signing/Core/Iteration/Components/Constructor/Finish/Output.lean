import P256.Proofs.Signing.Core.Iteration.Components.Constructor.Finish.Output.Copy
import P256.Proofs.Signing.Core.Iteration.Components.Constructor.Finish.Output.Tag
import X86Proofs.Instructions.Branch.Triple
import P256.Proofs.Signing.Core.Iteration.Components.Constructor.Finish.Output.Epilogue

set_option autoImplicit false

open P256.Proofs.Program

namespace P256.Proofs.Signing.Core.Iteration.Components.Constructor.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)

theorem reject [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x109890 32 72 512) (state : Stage s t boundary)
    (rip : t.RIP = 0x109a0d) :
    ∃ u, CalleeResult s u boundary 72 512 ∧
      memLoad u.external (s.regValue .rdi) 64 = 1 ∧
      memLoad u.external (s.regValue .rdi + 8) 64 = 0 := by
  obtain ⟨v, run, ready, effect⟩ :=
    (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any
      0x109a0d 0x48 (by simp [RexWPrefix]) (.base 3 (.d8 8)) (by decide) rfl rfl 0).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0x9a0d _
        (by decide) (by decide +kernel))
      ⟨rip, by
        change P256.Proofs.Common.Instructions.CrossPageStore.Writable t (t.regValue .rbx + 8) 8
        rw [state.output]
        exact (output_writable pre state.toFrame).add 8 (by decide), by
        change RangeApart (t.regValue .rbx + 8) 8 0x109a0d 8
        rw [state.output]
        exact P256.Proofs.Common.Instructions.RangeApart.add_left
          (output_code pre (offset := 0x9a0d) (len := 8) (by decide)) 8 (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x9a15 (by decide)))
  change (storeEffect (n := 64) 0x109a0d 8
    (storeAddrAt 0x109a0d (.base 3 (.d8 8)) 8) (fun _ => 0) t).Holds t v at effect
  have frame : AgreesExcept [.mem (s.regValue .rdi + 8) 8, .rip] t v := by
    have h := effect.agrees
    have address : storeAddrAt 0x109a0d (.base 3 (.d8 8)) 8 t = t.regValue .rbx + 8 := by
      x86_norm
      rfl
    simp only [storeEffect_components, Nat.reduceDiv, address] at h
    rw [state.output] at h
    exact h
  have vst := after_output_store pre state run ready frame (off := 8) (by decide)
  have zero : memLoad v.external (s.regValue .rdi + 8) 64 = 0 := by
    have h := effect.writes
    change memLoad v.external (t.regValue .rbx + 8) 64 = 0 at h
    rw [state.output] at h
    exact h
  have apart : RangeApart (s.regValue .rdi) 8 0x109a15 7 := by
    have h := P256.Proofs.Common.Instructions.RangeApart.add_left
      (h := output_code pre (offset := 0x9a15) (len := 7) (by decide)) 0 (len := 8) (by decide)
    change RangeApart (s.regValue .rdi + 0#64) 8 _ 7 at h
    simpa only [BitVec.add_zero, Extracted.textAddress, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using h
  obtain ⟨a, sa, ipa, tag, ag⟩ := store_tag pre vst 0x109a15 1
    (programText_slice (programLoaded_codeIn vst.loaded) 0x9a15 _
      (by decide) (by decide +kernel)) effect.rip
    (inProgram_of_textOffset 0x9a1c (by decide)) apart
  have payload : memLoad a.external (s.regValue .rdi + 8) 64 = 0 := by
    have ag' : AgreesExcept [.mem (s.regValue .rdi + BitVec.ofNat 64 0) 8, .rip] v a := by
      simpa only [BitVec.add_zero] using ag
    exact (output_word_preserved ag' (target := 8) (by unfold OffsetsApart; decide +kernel)).trans zero
  obtain ⟨u, result, memory⟩ := epilogue pre sa ipa
  refine ⟨u, result, ?_, ?_⟩
  · rw [memory]; exact tag
  · rw [memory]; exact payload

theorem accept [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x y : Nat}
    (pre : CalleePre s boundary 0x109890 32 72 512) (state : Stage s t boundary)
    (rip : t.RIP = 0x109a2c)
    (first : Nat256At t (stackPtr t + 64) x)
    (second : Nat256At t (stackPtr t + 96) y) :
    ∃ u, CalleeResult s u boundary 72 512 ∧
      memLoad u.external (s.regValue .rdi) 64 = 0 ∧
      Nat256At u (s.regValue .rdi + 8) x ∧ Nat256At u (s.regValue .rdi + 40) y := by
  obtain ⟨a, sa, ipa, xa, ya⟩ := copy_scalars pre state rip first second
  have apart : RangeApart (s.regValue .rdi) 8 0x109a9b 7 := by
    have h := P256.Proofs.Common.Instructions.RangeApart.add_left
      (h := output_code pre (offset := 0x9a9b) (len := 7) (by decide)) 0 (len := 8) (by decide)
    change RangeApart (s.regValue .rdi + 0#64) 8 0x109a9b 7 at h
    simpa only [BitVec.add_zero, Extracted.textAddress, BitVec.reduceAdd] using h
  obtain ⟨b, sb, ipb, tag, frame⟩ := store_tag pre sa 0x109a9b 0
    (programText_slice (programLoaded_codeIn sa.loaded) 0x9a9b _
      (by decide) (by decide +kernel)) ipa
    (inProgram_of_textOffset 0x9aa2 (by decide)) apart
  have keep {value off : Nat}
      (apart : OffsetsApart 0#64 8 (BitVec.ofNat 64 off) 32)
      (scalar : Nat256At a (s.regValue .rdi + BitVec.ofNat 64 off) value) :
      Nat256At b (s.regValue .rdi + BitVec.ofNat 64 off) value := by
    refine ⟨scalar.1, ?_⟩
    intro i hi
    refine (frame.byte ?_).trans (scalar.2 i hi)
    intro c hc hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · obtain ⟨j, hj, he⟩ := hv
      apply apart.ne (s.regValue .rdi) hj hi (by decide)
      simpa only [BitVec.add_zero, Extracted.textAddress, BitVec.reduceAdd] using he.symm
    · exact hv.elim
  have xb := keep (off := 8) (by unfold OffsetsApart; decide +kernel) xa
  have yb := keep (off := 40) (by unfold OffsetsApart; decide +kernel) ya
  obtain ⟨c, run, ready, effect⟩ :=
    (jmp_rel32_effect_step 0x109aa2 0xffffff75 (by decide)).advances
      (readyToStep sb.machine sb.bindingsSupported)
      (programText_slice (programLoaded_codeIn sb.loaded) 0x9aa2 _
        (by decide) (by decide +kernel)) ipb
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x9a1c (by decide)))
  have jump : AgreesExcept [.rip] b c := effect.agrees
  have sc := sb.after_registers run ready jump (by simp [Component.Covers]) (by simp)
  have memoryC : c.external = b.external := jump.external (by simp [Component.Covers])
  obtain ⟨u, result, memoryU⟩ := epilogue pre sc effect.rip
  have memory : u.external = b.external := memoryU.trans memoryC
  refine ⟨u, result, ?_, ?_, ?_⟩
  · rw [memory]
    exact tag
  · simpa only [Nat256At, memory, BitVec.ofNat_eq_ofNat] using xb
  · simpa only [Nat256At, memory, BitVec.ofNat_eq_ofNat] using yb

end P256.Proofs.Signing.Core.Iteration.Components.Constructor.Finish
