import P256.Proofs.Sec1.Wrapper.Success.Tail.Memory
import P256.Proofs.Common.Instructions.CrossPageStore
import X86Proofs.Instructions.Xor.Generated.RR.Triple
import X86Proofs.Program.ReadWrite.Bytes

set_option autoImplicit false

namespace P256.Proofs.Sec1.Wrapper.Success.Tail

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

theorem store [Bindings] {initial s : RamState} {input : ByteArray}
    {slices : Array Input} {x y : Nat}
    (valid : ValidCallWithSlices publicKeyFromSec1Bytes initial [input] slices)
    (model : Points.decodePublicKey input = some (.affine x y))
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (grown : ∀ a : BitVec 64, (initial.external[a]?).isSome → (s.external[a]?).isSome)
    (outside : ¬ InProgram (returnBoundary initial).rip) (rip : s.RIP = 0x1018d3)
    (output : s.regValue .rbx = initial.regValue .rcx)
    (count : s.regValue .r15 = BitVec.ofNat 64 65) :
    ∃ t, Advances (returnBoundary initial) 2 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP = 0x1018d8 ∧ t.regValue .rax = 0 ∧
      Bytes t.external (initial.regValue .rcx) 8 (storedByte (BitVec.ofNat 64 65)) ∧
      AgreesExcept [.reg 0, .flags, .mem (initial.regValue .rcx) 8, .rip] s t := by
  have address : storeAddrAt 0x1018d3 (.base 3 .none) 3 s = initial.regValue .rcx := by
    change s.regValue .rbx + 0 = initial.regValue .rcx
    exact (BitVec.add_zero _).trans output
  have writable : CrossPageStore.Writable s (initial.regValue .rcx) 8 := by
    simpa only [BitVec.add_zero] using (output_writable valid model grown).add 0 (len := 8) (by omega)
  have avoids := ((valid.outputSeparationIfAccepted (accepted_of_model model)).2
    (outputRegion publicKeyFromSec1Bytes initial [input]) (by simp)).2
  have contains {a : BitVec 64} (h : (Component.mem (initial.regValue .rcx) 8).Covers a) :
      (outputRegion publicKeyFromSec1Bytes initial [input]).Contains a.toNat :=
    output_contains valid model (off := 0) (len := 8) (by omega)
      (by simpa only [BitVec.add_zero] using h)
  have apart : RangeApart (initial.regValue .rcx) 8 0x1018d3 3 := by
    intro i hi j hj eq
    apply avoids _ (contains ⟨i, hi, rfl⟩) (.inl ?_)
    rw [eq]
    have h := inProgram_of_textOffset (0x18d3 + j) (by omega)
    simpa only [BitVec.ofNat_add, ← BitVec.add_assoc, Extracted.textAddress,
      BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using h
  obtain ⟨a, runA, readyA, effectA⟩ :=
    (CrossPageStore.mov_m64_r64_effect_step_any 0x1018d3 0x4c
      (by simp [RexWPrefix]) 7 (.base 3 .none) (by decide) rfl rfl).advances ready
      (programText_slice (programLoaded_codeIn loaded) 0x18d3 _
        (by decide) (by decide +kernel))
      ⟨rip, by change CrossPageStore.Writable s (storeAddrAt _ _ 3 s) 8
               rw [address]; exact writable,
        by change RangeApart (storeAddrAt _ _ 3 s) 8 0x1018d3 3
           rw [address]; exact apart⟩
      (boundary_ne_program outside (inProgram_of_textOffset 0x18d6 (by decide)))
  change (storeEffect (n := 64) 0x1018d3 3 (storeAddrAt 0x1018d3 (.base 3 .none) 3)
    (fun v => (Operand.reg 15 : Operand 64).read v) s).Holds s a at effectA
  have agreesA : AgreesExcept [.mem (initial.regValue .rcx) 8, .rip] s a := by
    have ag : AgreesExcept [.mem (storeAddrAt 0x1018d3 (.base 3 .none) 3 s) 8, .rip] s a := by
      simpa only [storeEffect_components, Nat.reduceDiv] using effectA.agrees
    simpa only [address] using ag
  have loadedA : ProgramLoaded a := by
    intro addr byte fetched
    apply (agreesA.byte ?_).trans (loaded addr byte fetched)
    intro c hc hv
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · exact avoids addr (contains hv) (.inl ⟨byte, fetched⟩)
    · exact hv.elim
  have value : memLoad a.external (initial.regValue .rcx) 64 = BitVec.ofNat 64 65 := by
    have h := effectA.writes
    change memLoad a.external (storeAddrAt 0x1018d3 (.base 3 .none) 3 s) 64 = s.regValue .r15 at h
    simpa only [address, count] using h
  have length : Bytes a.external (initial.regValue .rcx) 8
      (storedByte (BitVec.ofNat 64 65)) := by
    have h := Bytes.of_memLoad (n := 64) (fun i hi => agreesA.grow _ (writable.1.mem i hi))
    rw [value] at h
    exact h
  obtain ⟨t, runT, readyT, effectT⟩ := (xor_r32_r32_effect_step 0x1018d6 0xc0 (by decide)).advances
    readyA (programText_slice (programLoaded_codeIn loadedA) 0x18d6 _
      (by decide) (by decide +kernel)) effectA.rip
    (boundary_ne_program outside (inProgram_of_textOffset 0x18d8 (by decide)))
  have agreesT : AgreesExcept [.reg 0, .flags, .rip] a t := effectT.agrees
  have memory := agreesT.external (by simp [Component.Covers])
  refine ⟨t, runA.trans runT, readyT, ?_, effectT.rip, ?_, ?_,
    (agreesA.trans agreesT).mono (by simp)⟩
  · simpa only [ProgramLoaded, memory] using loadedA
  · have h := effectT.writes
    change t.regValue .rax = (((Operand.reg 0 : Operand 32).read a) ^^^
      ((Operand.reg 0 : Operand 32).read a)).setWidth 64 at h
    simpa only [BitVec.xor_self, BitVec.setWidth_zero, BitVec.ofNat_eq_ofNat] using h
  · simpa only [memory] using length

end P256.Proofs.Sec1.Wrapper.Success.Tail
