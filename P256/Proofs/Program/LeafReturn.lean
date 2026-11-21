import P256.Proofs.Program.ScalarFrame.Output
import P256.Proofs.Program.State
import P256.Proofs.Program.Copy.Return

set_option autoImplicit false

namespace P256.Proofs.Program

open Prelude X86 X86.Machine X86.UserProcess X86Proofs P256.Spec.Program P256.Spec.Program.Routines

def leafComponents (dst : BitVec 64) (size : Nat) (clobbered : List (BitVec 5)) : List Component :=
  clobbered.map Component.reg ++ [.flags, .rip, .mem dst size]

theorem leaf_covers {dst a : BitVec 64} {size : Nat} {clobbered : List (BitVec 5)}
    {c : Component} (member : c ∈ leafComponents dst size clobbered) (covers : c.Covers a) :
    ∃ i : Nat, i < size ∧ a = dst + BitVec.ofNat 64 i := by
  simp only [leafComponents, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with member | rfl | rfl | rfl
  · obtain ⟨r, _, rfl⟩ := List.mem_map.mp member
    exact covers.elim
  · exact covers.elim
  · exact covers.elim
  · exact covers

theorem leaf_return [Bindings] {s t : RamState} {boundary : ReturnBoundary} {entry : BitVec 64} {inputBytes outputBytes reserve fuel codeOffset : Nat}
    {inputRegister : Syntax.Reg}
    (clobbered : List (BitVec 5)) (noStack : (4 : BitVec 5) ∉ clobbered)
    (noSaved : ∀ r ∈ ([3,5,12,13,14,15] : List (BitVec 5)), r ∉ clobbered)
    (pre : CalleePre s boundary entry inputBytes outputBytes reserve inputRegister)
    (run : Advances boundary fuel s t) (ready : ReadyToStep t)
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 codeOffset)
    (codeBound : codeOffset + 1 < 118431)
    (code : Extracted.textBytes.toListFrom codeOffset 1 = [0xc3]) (ag : AgreesExcept (leafComponents (s.regValue .rdi) outputBytes clobbered) s t) :
    ∃ u, CalleeResult s u boundary outputBytes reserve ∧ u.external = t.external ∧
      u.regValue .rax = t.regValue .rax ∧
      AgreesExcept (leafComponents (s.regValue .rdi) outputBytes clobbered ++ [.reg 4, .rip]) s u := by
  have sp : stackPtr t = stackPtr s := ag.read (n := 64) (r := 4) (by simpa [leafComponents] using noStack)
  have stack_contains (i : Nat) (hi : i < 8) :
      (Stack.region s reserve).Contains (stackPtr s + BitVec.ofNat 64 i).toNat := by
    apply memoryRegion_contains_add pre.stack.1 (Nat.sub_le _ _) _ hi
    rw [stack_region_end]
    exact Nat.le_refl _
  have loaded : ProgramLoaded t := by
    intro address byte hb
    refine (ag.byte ?_).trans (pre.loaded address byte hb)
    intro c hm hv
    obtain ⟨i, hi, rfl⟩ := leaf_covers hm hv
    exact pre.avoids _ (by simp) _
      (memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) hi)
      (.inl ⟨byte, hb⟩)
  have top : stackTop t = (returnBoundary s).rip := by
    change memLoad t.external (stackPtr t) 64 = memLoad s.external (stackPtr s) 64
    rw [sp]
    apply memLoad_congr
    intro i hi
    apply memByte_congr
    apply ag.byte
    intro c hm hv
    obtain ⟨j, hj, he⟩ := leaf_covers hm hv
    have hd := pre.separation (1 : Fin 3) (2 : Fin 3) (by decide)
    apply hd _ (memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) hj)
    rw [← he]
    exact stack_contains i hi
  have readable : MemReadable t (stackPtr t) 8 := by
    rw [sp]
    refine ⟨?_, fun i hi ↦ ag.grow _
      (Option.isSome_iff_exists.mpr (pre.stack.2.1 _ (stack_contains i hi)))⟩
    have hb := pre.stack.1
    change (Stack.region s reserve).start + (Stack.region s reserve).size < 2^32 at hb
    rw [stack_region_end] at hb
    omega
  obtain ⟨u, runu, ru, eu⟩ := (ret_effect_step (Extracted.textAddress + BitVec.ofNat 64 codeOffset)).advances ready
    (programText_slice (programLoaded_codeIn loaded) codeOffset [0xc3] (by simpa using Nat.le_of_lt codeBound) code)
    ⟨⟨rip, readable⟩, top ▸ inProgram_low pre.returnInProgram⟩
    (by change stackTop t ≠ boundary.rip
        rw [top]
        exact boundary_ne_program pre.outerBoundary pre.returnInProgram)
  have final : AgreesExcept (leafComponents (s.regValue .rdi) outputBytes clobbered ++ [.reg 4, .rip]) s u :=
    ag.trans eu.agrees
  have mem : u.external = t.external := eu.agrees.external (by simp [Component.Covers])
  refine ⟨u, ?_, mem, eu.agrees.read (n := 64) (r := 0) (by simp), final⟩
  refine ⟨⟨fuel + 1, run.trans runu⟩, eu.rip.trans top, ?_,
    bindingsSupported_of_ready_agrees pre.bindingsSupported ru final,
    supportedMachine_of_ready_agrees pre.machine ru final, ?_,
    final.directionFlagClear (by simp [leafComponents]) pre.directionFlag,
    final.mxcsr (by simp [leafComponents]), final.fcw (by simp [leafComponents]),
    ?_, ?_, final.grow⟩
  · have hw := eu.writes
    change u.regValue .rsp = stackPtr t + 8 at hw
    rw [hw, sp]
    rfl
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact final.read (n := 64) (r := 3) (by simpa [leafComponents] using noSaved 3 (by simp))
    · exact final.read (n := 64) (r := 5) (by simpa [leafComponents] using noSaved 5 (by simp))
    · exact final.read (n := 64) (r := 12) (by simpa [leafComponents] using noSaved 12 (by simp))
    · exact final.read (n := 64) (r := 13) (by simpa [leafComponents] using noSaved 13 (by simp))
    · exact final.read (n := 64) (r := 14) (by simpa [leafComponents] using noSaved 14 (by simp))
    · exact final.read (n := 64) (r := 15) (by simpa [leafComponents] using noSaved 15 (by simp))
  · apply final.memoryWriteFrame
    intro c hc a ha
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with hc | rfl | rfl
    · obtain ⟨i, hi, rfl⟩ := leaf_covers hc ha
      exact ⟨registerRegion s .rdi outputBytes, by simp,
      memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) hi⟩
    · exact ha.elim
    · exact ha.elim
  · intro a b hb
    rw [mem]
    exact loaded a b hb

end P256.Proofs.Program
