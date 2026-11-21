import P256.Proofs.Projective.Multiply.Machine.Basepoint.Constants
import P256.Proofs.Projective.Preserve
import P256.Proofs.Common.Instructions.RepMovsqAny
import P256.Proofs.Program.WrapperMemory

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Basepoint.TableSteps

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

variable {entry : BitVec 64} {inputBytes outputBytes reserve frameOffset : Nat}

def copyComponents (s : RamState) (destination : Nat) : List Component :=
  [.reg 6, .reg 7, .reg 1, .mem (stackPtr s - BitVec.ofNat 64 destination) 96, .rip]

theorem copy_to_stack [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {point : Projective}
    (pre : CalleePre s boundary entry inputBytes outputBytes reserve) (state : FrameState s t outputBytes reserve (BitVec.ofNat 64 frameOffset))
    (codeOffset : Nat) (codeBound : codeOffset + 3 < 118431)
    (codeBytes : Extracted.textBytes.toListFrom codeOffset 3 = [0xf3, 0x48, 0xa5])
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 codeOffset)
    (destination : Nat) (destBound : destination ≤ frameOffset) (destSaved : 144 ≤ destination)
    (dst : t.regValue .rdi = stackPtr s - BitVec.ofNat 64 destination)
    (count : t.regValue .rcx = 12)
    (source : MemReadable t (t.regValue .rsi) 96)
    (disjoint : (t.regValue .rsi).toNat + 96 ≤ (t.regValue .rdi).toNat ∨
      (t.regValue .rdi).toNat + 96 ≤ (t.regValue .rsi).toNat)
    (input : ProjectiveAt t (t.regValue .rsi) point)
    (frameBound : frameOffset ≤ reserve := by decide) :
    ∃ u, Advances boundary 12 t u ∧ FrameState s u outputBytes reserve (BitVec.ofNat 64 frameOffset) ∧
      u.RIP = Extracted.textAddress + BitVec.ofNat 64 codeOffset + (3 : BitVec 64) ∧
      ProjectiveAt u (stackPtr s - BitVec.ofNat 64 destination) point ∧
      AgreesExcept (copyComponents s destination) t u ∧
      ∀ i < 96, u.external[stackPtr s - BitVec.ofNat 64 destination + BitVec.ofNat 64 i]? =
        t.external[t.regValue .rsi + BitVec.ofNat 64 i]? := by
  have hn : (rcx.read t).toNat = 12 := by rw [show rcx.read t = 12#64 from count]; rfl
  have dest : P256.Proofs.Common.Instructions.CrossPageStore.Writable t (t.regValue .rdi) 96 := by
    rw [dst]
    have readable := readable_of_grow (stack_sub_readable pre.stack
      (offset := destination) (len := 96) (by omega) (by omega)) state.allocated
    refine ⟨readable, ?_⟩
    apply tables_of_not_reserved (by decide) readable.low
    intro i hi hreserved
    apply pre.avoids (Stack.region s reserve) (by simp) _ ?_ (.inr hreserved)
    exact stack_contains pre (by omega) (by omega) ⟨i, hi, rfl⟩
  have apart : RangeApart (rdi.read t) 96
      (Extracted.textAddress + BitVec.ofNat 64 codeOffset) 3 := by
    change RangeApart (t.regValue .rdi) 96 _ 3
    rw [dst]
    intro i hi j hj he
    apply pre.avoids (Stack.region s reserve) (by simp) _
      (stack_contains pre (offset := destination) (len := 96) (by omega) (by omega) ⟨i, hi, rfl⟩) (.inl ?_)
    rw [he, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact inProgram_of_textOffset (codeOffset + j) (by omega)
  have pc := P256.Proofs.Common.Instructions.RepMovsqAny.pre_of_memory
    rip state.directionFlag.df hn source dest disjoint apart
  have next : Extracted.textAddress + BitVec.ofNat 64 codeOffset + (3 : BitVec 64) =
      Extracted.textAddress + BitVec.ofNat 64 (codeOffset + 3) := by
    rw [BitVec.ofNat_add, BitVec.add_assoc]
    rfl
  obtain ⟨run, ready, effect, bytes⟩ :=
    P256.Proofs.Common.Instructions.RepMovsqAny.rep_movsq_execution
    pre.bindingsSupported.stringStride (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) codeOffset [0xf3, 0x48, 0xa5]
      (by change codeOffset + 3 ≤ 118431; omega) codeBytes) pc hn
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset codeOffset (by omega)))
    (boundary_ne_program pre.outerBoundary
      (by rw [next]; exact inProgram_of_textOffset _ codeBound))
  simp only [show max 12 1 = 12 from rfl] at run ready effect bytes
  generalize hu : nextStates 12 t = u at run ready effect bytes
  have frame : AgreesExcept (copyComponents s destination) t u := by
    simpa only [repMovsqEffect_components, hn, show rdi.read t =
      stackPtr s - BitVec.ofNat 64 destination from dst, Nat.reduceMul, copyComponents]
      using effect.agrees
  have writes : WritesWithin (copyComponents s destination)
      #v[registerRegion s .rdi outputBytes, workRegion s reserve] := by
    intro c hc a ha
    simp only [copyComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    exact ⟨workRegion s reserve, by simp, work_contains pre (by omega) destSaved ha⟩
  have copied : ∀ i < 96,
      u.external[stackPtr s - BitVec.ofNat 64 destination + BitVec.ofNat 64 i]? =
        t.external[t.regValue .rsi + BitVec.ofNat 64 i]? := by
    intro i hi
    have hb := bytes i (by omega)
    change u.external[t.regValue .rdi + BitVec.ofNat 64 i]? =
      t.external[t.regValue .rsi + BitVec.ofNat 64 i]? at hb
    simpa only [dst] using hb
  exact ⟨u, run, state.after_effect pre (by omega) ready frame writes (by simp [copyComponents]),
    effect.rip, input.of_bytes_eq copied, frame, copied⟩

theorem copy_byte [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {destination offset len i : Nat}
    (pre : CalleePre s boundary entry inputBytes outputBytes reserve)
    (agrees : AgreesExcept (copyComponents s destination) t u)
    (destBound : destination ≤ reserve) (destSaved : 144 ≤ destination)
    (ho : offset ≤ reserve) (hl : len ≤ offset + 8)
    (apart : offset + 96 ≤ destination ∨ destination + len ≤ offset) (hi : i < len) :
    u.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
      t.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
  apply agrees.byte
  intro c hc hv
  simp only [copyComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl
  all_goals try exact hv.elim
  obtain ⟨j, hj, he⟩ := hv
  exact stack_sub_apart pre.stack destBound ho (by omega) hl apart j hj i hi he.symm

theorem stack_source [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {sourceOffset : Nat}
    (pre : CalleePre s boundary entry inputBytes outputBytes reserve) (state : FrameState s t outputBytes reserve (BitVec.ofNat 64 frameOffset))
    (bound : sourceOffset ≤ reserve) (length : 96 ≤ sourceOffset + 8)
    (src : t.regValue .rsi = stackPtr s - BitVec.ofNat 64 sourceOffset) :
    MemReadable t (t.regValue .rsi) 96 := by
  rw [src]
  exact readable_of_grow (stack_sub_readable pre.stack bound length) state.allocated

theorem stack_disjoint [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {sourceOffset destination : Nat}
    (pre : CalleePre s boundary entry inputBytes outputBytes reserve)
    (sourceBound : sourceOffset ≤ reserve) (destBound : destination ≤ reserve)
    (apart : destination + 96 ≤ sourceOffset ∨ sourceOffset + 96 ≤ destination)
    (src : t.regValue .rsi = stackPtr s - BitVec.ofNat 64 sourceOffset)
    (dst : t.regValue .rdi = stackPtr s - BitVec.ofNat 64 destination) :
    (t.regValue .rsi).toNat + 96 ≤ (t.regValue .rdi).toNat ∨
      (t.regValue .rdi).toNat + 96 ≤ (t.regValue .rsi).toNat := by
  rw [src, dst, stack_sub_toNat pre.stack sourceBound, stack_sub_toNat pre.stack destBound]
  have bounds := stack_bounds pre.stack
  omega

theorem copy_generator [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10e6f0 32 65 3352) (state : FrameState s t 65 3352 1944)
    (codeOffset : Nat) (codeBound : codeOffset + 3 < 118431)
    (codeBytes : Extracted.textBytes.toListFrom codeOffset 3 = [0xf3, 0x48, 0xa5])
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 codeOffset)
    (destination : Nat) (destBound : destination ≤ 1944) (destSaved : 144 ≤ destination)
    (dst : t.regValue .rdi = stackPtr s - BitVec.ofNat 64 destination)
    (count : t.regValue .rcx = 12)
    (src : t.regValue .rsi = 0x202ac8) :
    ∃ u, Advances boundary 12 t u ∧ FrameState s u 65 3352 1944 ∧
      u.RIP = Extracted.textAddress + BitVec.ofNat 64 codeOffset + (3 : BitVec 64) ∧
      ProjectiveAt u (stackPtr s - BitVec.ofNat 64 destination) basePoint ∧
      AgreesExcept (copyComponents s destination) t u ∧
      ∀ i < 96, u.external[stackPtr s - BitVec.ofNat 64 destination + BitVec.ofNat 64 i]? =
        t.external[t.regValue .rsi + BitVec.ofNat 64 i]? := by
  apply copy_to_stack pre state codeOffset codeBound codeBytes rip destination destBound destSaved
    dst count
  · rw [src]
    exact generator_readable state.loaded
  · rw [src, dst]
    exact generator_stack_disjoint pre (by omega) (by omega)
  · rw [src]
    exact generator_at state.loaded

theorem copy_stack [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {point : Projective} {sourceOffset : Nat}
    (pre : CalleePre s boundary entry inputBytes outputBytes reserve) (state : FrameState s t outputBytes reserve (BitVec.ofNat 64 frameOffset))
    (codeOffset : Nat) (codeBound : codeOffset + 3 < 118431)
    (codeBytes : Extracted.textBytes.toListFrom codeOffset 3 = [0xf3, 0x48, 0xa5])
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 codeOffset)
    (destination : Nat) (destBound : destination ≤ frameOffset) (destSaved : 144 ≤ destination)
    (dst : t.regValue .rdi = stackPtr s - BitVec.ofNat 64 destination)
    (count : t.regValue .rcx = 12)
    (sourceBound : sourceOffset ≤ reserve) (sourceLength : 96 ≤ sourceOffset + 8)
    (apart : destination + 96 ≤ sourceOffset ∨ sourceOffset + 96 ≤ destination)
    (src : t.regValue .rsi = stackPtr s - BitVec.ofNat 64 sourceOffset)
    (input : ProjectiveAt t (stackPtr s - BitVec.ofNat 64 sourceOffset) point)
    (frameBound : frameOffset ≤ reserve := by decide) :
    ∃ u, Advances boundary 12 t u ∧ FrameState s u outputBytes reserve (BitVec.ofNat 64 frameOffset) ∧
      u.RIP = Extracted.textAddress + BitVec.ofNat 64 codeOffset + (3 : BitVec 64) ∧
      ProjectiveAt u (stackPtr s - BitVec.ofNat 64 destination) point ∧
      AgreesExcept (copyComponents s destination) t u ∧
      ∀ i < 96, u.external[stackPtr s - BitVec.ofNat 64 destination + BitVec.ofNat 64 i]? =
        t.external[t.regValue .rsi + BitVec.ofNat 64 i]? := by
  apply copy_to_stack (frameBound := frameBound) pre state codeOffset codeBound codeBytes rip destination destBound destSaved
    dst count (stack_source pre state sourceBound sourceLength src)
    (stack_disjoint pre sourceBound (by omega) apart src dst)
  rw [src]
  exact input

end P256.Proofs.Projective.Multiply.Machine.Basepoint.TableSteps
