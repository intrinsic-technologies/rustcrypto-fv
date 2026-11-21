import P256.Proofs.SignatureFromDer.Fixed.Finish.Output.Copy
import P256.Proofs.SignatureFromDer.Fixed.Finish.Output.Tag
import X86Proofs.Instructions.Branch.Triple
import P256.Proofs.SignatureFromDer.Fixed.Finish.Output.Epilogue

set_option autoImplicit false

open P256.Proofs.Program (CalleePre CalleeResult boundary_ne_program readyToStep inProgram_of_textOffset programLoaded_codeIn programText_slice)

namespace P256.Proofs.SignatureFromDer.Fixed.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)

theorem reject [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {inputBytes : Nat} (pre : CalleePre s boundary 0x109ac0 inputBytes 72 560) (state : Stage s t boundary)
    (rip : t.RIP = 0x109c57) :
    ∃ u, CalleeResult s u boundary 72 560 ∧
      loadBytes u.external (s.regValue .rdi) 8 = .ok (1 : BitVec 64) ∧
      memLoad u.external (s.regValue .rdi + 8) 64 = 0 := by
  obtain ⟨v, run, ready, effect⟩ :=
    (P256.Proofs.Common.Instructions.CrossPageStore.mov_m64_imm32_effect_step_any
      0x109c57 0x48 (by simp [RexWPrefix]) (.base 3 (.d8 8)) (by decide) rfl rfl 0).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0x9c57 _
        (by decide) (by decide +kernel))
      ⟨rip, by
        change P256.Proofs.Common.Instructions.CrossPageStore.Writable t (t.regValue .rbx + 8) 8
        rw [state.output]
        exact (output_writable pre state.toFrame).add 8 (by decide), by
        change RangeApart (t.regValue .rbx + 8) 8 0x109c57 8
        rw [state.output]
        exact P256.Proofs.Common.Instructions.RangeApart.add_left
          (h := output_code pre (offset := 0x9c57) (len := 8) (by decide)) 8 (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x9c5f (by decide)))
  have frame : AgreesExcept [.mem (s.regValue .rdi + 8) 8, .rip] t v := by
    have addr (q : RamState) : storeAddrAt 0x109c57 (.base 3 (.d8 8)) 8 q = q.regValue .rbx + 8 := rfl
    simpa only [movM64Imm32Effect, storeEffect_components, Nat.reduceDiv,
      AddrMode.tail, Disp.bytes, immBytes_length, List.length_cons, List.length_nil,
      Nat.reduceAdd, addr, state.output] using effect.agrees
  have sv := after_output_store pre state run ready frame (by decide)
  have value : memLoad v.external (s.regValue .rdi + 8) 64 = 0 := by
    have h : memLoad v.external (t.regValue .rbx + 8) 64 = 0 := effect.writes
    simpa only [state.output] using h
  have apart : RangeApart (s.regValue .rdi) 8 0x109c5f 7 := by
    have h := P256.Proofs.Common.Instructions.RangeApart.add_left
      (h := output_code pre (offset := 0x9c5f) (len := 7) (by decide)) 0 (len := 8) (by decide)
    change RangeApart (s.regValue .rdi + 0#64) 8 0x109c5f 7 at h
    simpa only [BitVec.add_zero] using h
  obtain ⟨a, sa, ipa, tag, tagframe⟩ := store_tag pre sv 0x109c5f 1
    (programText_slice (programLoaded_codeIn sv.loaded) 0x9c5f _
      (by decide) (by decide +kernel)) effect.rip
    (inProgram_of_textOffset 0x9c66 (by decide)) apart
  have null : memLoad a.external (s.regValue .rdi + 8) 64 = 0 := by
    have tf : AgreesExcept [.mem (s.regValue .rdi + 0#64) 8, .rip] v a := by
      simpa only [BitVec.add_zero] using tagframe
    exact (output_word_preserved tf (target := 8) (by unfold OffsetsApart; decide +kernel)).trans value
  obtain ⟨u, result, memory⟩ := epilogue pre sa ipa
  change loadBytes a.external (s.regValue .rdi) 8 = .ok (1 : BitVec 64) at tag
  exact ⟨u, result, by simpa only [memory] using tag, by simpa only [memory] using null⟩

theorem accept [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x y : Nat}
    (pre : CalleePre s boundary 0x109ac0 64 72 560) (state : Stage s t boundary)
    (rip : t.RIP = 0x109c74)
    (first : Nat256At t (stackPtr t + 104) x)
    (second : Nat256At t (stackPtr t + 136) y) :
    ∃ u, CalleeResult s u boundary 72 560 ∧
      loadBytes u.external (s.regValue .rdi) 8 = .ok (0 : BitVec 64) ∧
      Nat256At u (s.regValue .rdi + 8) x ∧ Nat256At u (s.regValue .rdi + 40) y := by
  obtain ⟨a, sa, ipa, xa, ya⟩ := copy_scalars pre state rip first second
  have apart : RangeApart (s.regValue .rdi) 8 0x109cf3 7 := by
    have h := P256.Proofs.Common.Instructions.RangeApart.add_left
      (h := output_code pre (offset := 0x9cf3) (len := 7) (by decide)) 0 (len := 8) (by decide)
    change RangeApart (s.regValue .rdi + 0#64) 8 0x109cf3 7 at h
    simpa only [BitVec.add_zero] using h
  obtain ⟨b, sb, ipb, tag, frame⟩ := store_tag pre sa 0x109cf3 0
    (programText_slice (programLoaded_codeIn sa.loaded) 0x9cf3 _
      (by decide) (by decide +kernel)) ipa
    (inProgram_of_textOffset 0x9cfa (by decide)) apart
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
      simpa only [BitVec.add_zero] using he.symm
    · exact hv.elim
  have xb := keep (off := 8) (by unfold OffsetsApart; decide +kernel) xa
  have yb := keep (off := 40) (by unfold OffsetsApart; decide +kernel) ya
  obtain ⟨c, run, ready, effect⟩ :=
    (jmp_rel32_effect_step 0x109cfa 0xffffff67 (by decide)).advances
      (readyToStep sb.machine sb.bindingsSupported)
      (programText_slice (programLoaded_codeIn sb.loaded) 0x9cfa _
        (by decide) (by decide +kernel)) ipb
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x9c66 (by decide)))
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

end P256.Proofs.SignatureFromDer.Fixed.Finish
