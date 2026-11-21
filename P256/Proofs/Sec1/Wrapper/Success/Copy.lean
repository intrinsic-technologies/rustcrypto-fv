import P256.Spec
import P256.Proofs.Sec1.Wrapper.ReturnState
import P256.Proofs.Program.WrapperMemory
import P256.Proofs.Common.Instructions.RepMovsqAny

set_option autoImplicit false

namespace P256.Proofs.Sec1.Wrapper.Success

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions.CrossPageStore

def copyComponents (initial : RamState) (destination count : Nat) : List Component :=
  [.reg 6, .reg 7, .reg 1, .mem (stackPtr initial - BitVec.ofNat 64 destination) (8 * count), .rip]

theorem stack_copy [Bindings] {initial t : RamState} {count source destination codeOffset : Nat}
    (state : ReturnState initial t) (stack : Stack.Valid initial 4048)
    (avoids : (callStack publicKeyFromSec1Bytes initial).Avoids (fun a => InProgram a ∨ InPageTables a))
    (outside : ¬ InProgram (returnBoundary initial).rip)
    (positive : 0 < count) (sourceBound : source ≤ 4048) (sourceEnd : 8 * count ≤ source + 8)
    (destinationBound : destination ≤ 4048) (saved : 8 * count + 24 ≤ destination)
    (apart : source + 8 * count ≤ destination ∨ destination + 8 * count ≤ source)
    (codeBound : codeOffset + 3 < 118431)
    (code : Extracted.textBytes.toListFrom codeOffset 3 = [0xf3, 0x48, 0xa5])
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 codeOffset)
    (src : t.regValue .rsi = stackPtr initial - BitVec.ofNat 64 source)
    (dst : t.regValue .rdi = stackPtr initial - BitVec.ofNat 64 destination)
    (length : t.regValue .rcx = BitVec.ofNat 64 count) :
    ∃ u, Advances (returnBoundary initial) count t u ∧ ReturnState initial u ∧
      u.RIP = Extracted.textAddress + BitVec.ofNat 64 codeOffset + (3 : BitVec 64) ∧
      AgreesExcept (copyComponents initial destination count) t u ∧
      ∀ i < 8 * count,
        u.external[stackPtr initial - BitVec.ofNat 64 destination + BitVec.ofNat 64 i]? =
          t.external[stackPtr initial - BitVec.ofNat 64 source + BitVec.ofNat 64 i]? := by
  have hn : (rcx.read t).toNat = count := by
    change (t.regValue .rcx).toNat = count
    rw [length, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
  have hr : MemReadable t (rsi.read t) (8 * count) := by
    change MemReadable t (t.regValue .rsi) (8 * count)
    rw [src]
    exact readable_of_grow (stack_sub_readable stack sourceBound sourceEnd) state.allocated
  have hw : Writable t (rdi.read t) (8 * count) := by
    change Writable t (t.regValue .rdi) (8 * count)
    rw [dst]
    have readable := readable_of_grow
      (stack_sub_readable stack destinationBound (by omega : 8 * count ≤ destination + 8)) state.allocated
    refine ⟨readable, tables_of_not_reserved (by omega) readable.low ?_⟩
    intro i hi reserved
    exact avoids _ (stack_component_within (routine := publicKeyFromSec1Bytes) stack
      destinationBound (by omega) ⟨i, hi, rfl⟩) (.inr reserved)
  have disjoint : (rsi.read t).toNat + 8 * count ≤ (rdi.read t).toNat ∨
      (rdi.read t).toNat + 8 * count ≤ (rsi.read t).toNat := by
    change (t.regValue .rsi).toNat + 8 * count ≤ (t.regValue .rdi).toNat ∨
      (t.regValue .rdi).toNat + 8 * count ≤ (t.regValue .rsi).toNat
    rw [src, dst, stack_sub_toNat stack sourceBound, stack_sub_toNat stack destinationBound]
    have bounds := stack_bounds stack
    omega
  have noCode : RangeApart (rdi.read t) (8 * count)
      (Extracted.textAddress + BitVec.ofNat 64 codeOffset) 3 := by
    change RangeApart (t.regValue .rdi) _ _ _
    rw [dst]
    intro i hi j hj eq
    apply avoids _ (stack_component_within (routine := publicKeyFromSec1Bytes) stack
      destinationBound (by omega) ⟨i, hi, rfl⟩)
    apply Or.inl
    rw [eq, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact inProgram_of_textOffset (codeOffset + j) (by omega)
  have pc := P256.Proofs.Common.Instructions.RepMovsqAny.pre_of_memory
    rip state.directionFlag.df hn hr hw disjoint noCode
  obtain ⟨run, ready, effect, bytes⟩ :=
    P256.Proofs.Common.Instructions.RepMovsqAny.rep_movsq_execution
      state.bindingsSupported.stringStride (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) codeOffset _ (by change codeOffset + 3 ≤ 118431; omega) code) pc hn
      (boundary_ne_program outside (inProgram_of_textOffset _ (by omega)))
      (by
        change Extracted.textAddress + BitVec.ofNat 64 codeOffset + BitVec.ofNat 64 3 ≠ _
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]
        exact boundary_ne_program outside (inProgram_of_textOffset (codeOffset + 3) codeBound))
  simp only [Nat.max_eq_left (by omega : 1 ≤ count)] at run ready effect bytes
  generalize hu : nextStates count t = u at run ready effect bytes
  have frame : AgreesExcept (copyComponents initial destination count) t u := by
    simpa only [repMovsqEffect_components, hn, show rdi.read t = _ from dst, copyComponents]
      using effect.agrees
  have word (off : Nat) (bound : off ≤ 24) :
      memLoad u.external (stackPtr initial - BitVec.ofNat 64 off) 64 =
        memLoad t.external (stackPtr initial - BitVec.ofNat 64 off) 64 := by
    apply memLoad_agrees_apart frame
    intro a n member
    have eq : a = stackPtr initial - BitVec.ofNat 64 destination ∧ n = 8 * count := by
      simpa only [copyComponents, List.mem_cons, List.not_mem_nil, or_false,
        Component.mem.injEq, reduceCtorEq, false_or, or_false] using member
    obtain ⟨rfl, rfl⟩ := eq
    exact stack_sub_apart stack destinationBound (by omega) (by omega) (by omega) (.inl (by omega))
  have loaded : ProgramLoaded u := by
    intro a b fetched
    rw [frame.byte (x := a) ?_]
    · exact state.loaded a b fetched
    · intro c member covered
      simp only [copyComponents, List.mem_cons, List.not_mem_nil, or_false] at member
      rcases member with rfl | rfl | rfl | rfl | rfl
      all_goals try exact covered.elim
      exact avoids _ (stack_component_within (routine := publicKeyFromSec1Bytes) stack
        destinationBound (by omega) covered) (.inl ⟨b, fetched⟩)
  refine ⟨u, run, ⟨bindingsSupported_of_ready_agrees state.bindingsSupported ready frame,
    supportedMachine_of_ready_agrees state.machine ready frame, loaded,
    frame.directionFlagClear (by simp [copyComponents]) state.directionFlag,
    (frame.read (n := 64) (r := 4) (by simp [copyComponents])).trans state.rsp,
    (word 24 (by decide)).trans state.savedRbx,
    (word 16 (by decide)).trans state.savedR14,
    (word 8 (by decide)).trans state.savedR15,
    ?_, ?_, fun a ha => frame.grow a (state.allocated a ha)⟩, effect.rip, frame, ?_⟩
  · have memory := word 0 (by decide)
    simp only [BitVec.sub_zero] at memory
    exact memory.trans state.returnAddress
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (frame.read (n := 64) (r := 5) (by simp [copyComponents])).trans (state.otherRegisters .rbp (by simp))
    · exact (frame.read (n := 64) (r := 12) (by simp [copyComponents])).trans (state.otherRegisters .r12 (by simp))
    · exact (frame.read (n := 64) (r := 13) (by simp [copyComponents])).trans (state.otherRegisters .r13 (by simp))
  · simpa only [show rdi.read t = _ from dst, show rsi.read t = _ from src] using bytes

end P256.Proofs.Sec1.Wrapper.Success
