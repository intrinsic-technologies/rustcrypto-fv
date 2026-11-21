import P256.Proofs.Sec1.Wrapper.Success.Tail.CopyPre
import P256.Proofs.Program.CopyBytes
import X86Proofs.Instructions.Call.Triple

set_option autoImplicit false

namespace P256.Proofs.Sec1.Wrapper.Success.Tail

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Standards.SECG.ECC Prelude X86 X86.Machine X86.UserProcess X86Proofs

def copyChanges (initial : RamState) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 4, .reg 6, .reg 7, .reg 8, .flags, .rip,
    .mem (initial.regValue .rcx + 8) 65, .mem (stackPtr initial - 240) 8]

theorem copy [Bindings] {initial s : RamState} {input : ByteArray}
    {slices : Array Input} {x y : Nat}
    (valid : ValidCallWithSlices publicKeyFromSec1Bytes initial [input] slices)
    (model : Points.decodePublicKey input = some (.affine x y))
    (state : ReturnState initial s) (outside : ¬ InProgram (returnBoundary initial).rip)
    (rip : s.RIP = 0x1018cd) (source : s.regValue .rsi = stackPtr initial - 232)
    (destination : s.regValue .rdi = initial.regValue .rcx + 8)
    (count : s.regValue .rdx = BitVec.ofNat 64 65)
    (bytes : (MemoryRegion.mk (stackPtr initial - 232).toNat 65).HasBytes s.external
      (Points.encode (.affine x y))) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ ReadyToStep t ∧
      ProgramLoaded t ∧ t.RIP = 0x1018d3 ∧ stackPtr t = stackPtr initial - 232 ∧
      AgreesExcept (copyChanges initial) s t ∧
      Bytes t.external (initial.regValue .rcx + 8) 65
        (fun i => (Points.encode (.affine x y)).data[i]!) := by
  have stack_contains {off len : Nat} {a : BitVec 64} (bound : off ≤ 4048)
      (endBound : len ≤ off + 8)
      (covered : (Component.mem (stackPtr initial - BitVec.ofNat 64 off) len).Covers a) :
      (Stack.region initial 4048).Contains a.toNat := by
    obtain ⟨i, hi, rfl⟩ := covered
    exact stack_buffer_contains valid.stackAvailable.1 bound endBound
      (memoryRegion_contains_add (stack_buffer_bounded valid.stackAvailable.1 bound endBound)
        (Nat.le_refl _) (Nat.le_refl _) hi)
  have push : pushAddr s = stackPtr initial - 240 := by
    rw [pushAddr, state.rsp, BitVec.sub_sub]
    rfl
  have writable : MemWritable s (pushAddr s) 8 := by
    rw [push]
    exact writable_of_grow (stack_sub_writable8 valid.stackAvailable.1
      (fun a ha hp => call_stack_avoids valid a ha (.inr hp)) (by decide) (by decide))
      state.allocated
  have apart : RangeApart (pushAddr s) 8 0x1018cd 6 := by
    rw [push]
    intro i hi j hj eq
    apply call_stack_avoids valid _
      (stack_contains (off := 240) (by decide) (by decide) ⟨i, hi, rfl⟩)
    apply Or.inl
    change InProgram (stackPtr initial - 240 + BitVec.ofNat 64 i)
    rw [eq]
    have h := inProgram_of_textOffset (0x18cd + j) (by omega)
    simpa only [BitVec.ofNat_add, ← BitVec.add_assoc, Extracted.textAddress,
      BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using h
  have pointer := memcpy_pointer state.loaded
  have target : callMemPtr 0x1018cd (.rip 0x102c25) s = 0x11c930 := pointer.2
  obtain ⟨a, step, ready, effect⟩ := call_m64_effect_step 0x1018cd (.rip 0x102c25)
    trivial rfl rfl s (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x18cd _
      (by decide) (by decide +kernel))
    ⟨⟨⟨rip, writable, apart⟩, by rw [target]; decide⟩, pointer.1⟩
  have effect' : (callEffect (fun _ => 0x11c930) 0x1018d3 s).Holds s a := by
    change (callEffect (callMemPtr 0x1018cd (.rip 0x102c25)) 0x1018d3 s).Holds s a at effect
    simpa only [callEffect, pushEffect, target] using effect
  have run : Advances (returnBoundary initial) 1 s a := Advances.of_step step (.inl (by
    rw [effect'.rip]
    exact boundary_ne_program outside (inProgram_of_textOffset 0x1c930 (by decide))))
  have loaded : ProgramLoaded a := by
    intro address byte fetched
    rw [effect'.agrees.byte (x := address) ?_]
    · exact state.loaded address byte fetched
    · intro c hc covers
      simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · exact covers.elim
      · rw [push] at covers
        exact call_stack_avoids valid address
          (stack_contains (off := 240) (by decide) (by decide) covers) (.inl ⟨byte, fetched⟩)
      · exact covers.elim
  have agA : AgreesExcept [.reg 4, .mem (stackPtr initial - 240) 8, .rip] s a := by
    simpa only [pushEffect_components, push] using effect'.agrees
  have srcA : a.regValue .rsi = stackPtr initial - 232 :=
    (agA.read (n := 64) (r := 6) (by simp)).trans source
  have dstA : a.regValue .rdi = initial.regValue .rcx + 8 :=
    (agA.read (n := 64) (r := 7) (by simp)).trans destination
  have child := copy_pre valid model state ready loaded effect' outside srcA dstA (by
    change InProgram (stackTop a)
    rw [(callEffect_stack effect').1]
    exact inProgram_of_textOffset 0x18d3 (by decide))
  have countA := (agA.read (n := 64) (r := 2) (by simp)).trans count
  obtain ⟨t, result, copied, agCopy⟩ := memcpy_correct child countA (by omega)
  have ag : AgreesExcept (copyChanges initial) s t :=
    (agA.trans agCopy).mono (by simp [copyChanges, Copy.copyComponents, Copy.registerComponents, dstA])
  obtain ⟨fuel, childRun⟩ := result.execution
  refine ⟨1 + fuel, t, run.trans childRun,
    readyToStep result.machine result.bindingsSupported, result.loaded,
    result.rip.trans (callEffect_stack effect').1,
    (result.rsp.trans (callEffect_stack effect').2).trans state.rsp, ag, ?_⟩
  intro i hi
  rw [← dstA, copied i hi, srcA]
  have saved := ScalarFrame.call_byte (by decide) state.rsp effect'
    (offset := 232) (len := 65) (by decide) (by decide) (i := i) (by omega)
  apply saved.trans
  have size : (Points.encode (.affine x y)).size = 65 := bytes.1
  have isize : i < (Points.encode (.affine x y)).data.size := by
    rw [ByteArray.size_data, size]
    exact hi
  have value := bytes.2 ⟨i, by rw [size]; exact hi⟩
  change s.external[BitVec.ofNat 64 ((stackPtr initial - 232).toNat + i)]? =
    some (Points.encode (.affine x y)).data[i] at value
  simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at value
  exact value.trans (congrArg some (getElem!_pos (Points.encode (.affine x y)).data i isize).symm)

end P256.Proofs.Sec1.Wrapper.Success.Tail
