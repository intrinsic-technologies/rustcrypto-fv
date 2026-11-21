import Hkdf.Proofs.Standard.Finalize.Suffix.Outer.Output.Serialize.Payload
import Hkdf.Proofs.Standard.Finalize.Suffix.State
import Hkdf.Proofs.Common.StreamPadding.Execution.Geometry

set_option autoImplicit false

namespace Hkdf.Proofs.Standard.Finalize.Suffix.Outer.Output.Serialize

open Prelude X86 X86.Machine X86.UserProcess X86Proofs Hkdf.Spec.Program
open Hkdf.Proofs.Common Hkdf.Proofs.Common.CallFrame Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.StreamPadding.Execution Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.SHA256

theorem code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x10e020 bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0xe020 bytes
    (by decide +kernel) (by decide +kernel)

theorem pre [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    (caller : CalleePre initial boundary 0x10dd90 144 176 1264)
    (state : Suffix.State initial boundary s) (rip : s.RIP = 0x10e020) : Pre s := by
  have address (i : Nat) (hi : i ≤ 408) :
      stackPtr s + BitVec.ofNat 64 i = stackPtr initial - BitVec.ofNat 64 (408-i) := by
    rw [state.rsp]
    have sum : (408 : BitVec 64) = BitVec.ofNat 64 (408-i) + BitVec.ofNat 64 i := by
      rw [← BitVec.ofNat_add, Nat.sub_add_cancel hi]; rfl
    rw [sum, ← BitVec.sub_sub, BitVec.sub_add_cancel]
  refine ⟨rip, ?_, ?_, ?_⟩
  · intro i member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact local_readable .hmac caller state.running state.rsp _ 4 (by decide)
  · have writable (i : Nat) (hi : i ≤ 408) (align : i % 4 = 0) :
        Hkdf.Proofs.Common.Instructions.CrossPageStore.Writable s
          (stackPtr s + BitVec.ofNat 64 i) 4 := by
      rw [address i hi]
      exact (fun (w : MemWritable s _ 4) => ⟨⟨w.low, w.mem⟩, w.tables⟩)
        (stack_writable4 caller.stack (caller.avoids _ (by simp)) state.running.allocated
          (by omega) (by omega))
    intro i member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact writable _ (by decide) (by decide)
  · intro i member pc len lower upper
    have start : BitVec.ofNat 64 pc =
        Extracted.textAddress + BitVec.ofNat 64 (pc - 0x100000) := by
      change BitVec.ofNat 64 pc = BitVec.ofNat 64 0x100000 + _
      rw [← BitVec.ofNat_add]
      exact congrArg (BitVec.ofNat 64) (by omega)
    have span : ∀ j < len, InProgram (BitVec.ofNat 64 pc + BitVec.ofNat 64 j) := by
      intro j hj
      rw [start, BitVec.add_assoc, ← BitVec.ofNat_add]
      exact inProgram_of_textOffset _ (by omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact local_codeApart .hmac caller state.rsp _ 4 _ len (by decide) span

theorem footprint (s : RamState) :
    ∀ c ∈ (effect s).components, ∀ a, c.Covers a →
      (Component.mem (rspOf s + 216) 32).Covers a := by
  intro c member a covered
  simp only [effect, Effect.components, List.map_cons, List.map_nil,
    Write.component, Operand.component, List.mem_append, List.mem_cons,
    List.not_mem_nil, or_false, or_assoc] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact covered.elim
  all_goals obtain ⟨i, hi, rfl⟩ := covered
  · exact ⟨0 + i, by omega, by
      simp only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat]
      bv_omega⟩
  · exact ⟨4 + i, by omega, by
      simp only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat]
      bv_omega⟩
  · exact ⟨8 + i, by omega, by
      simp only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat]
      bv_omega⟩
  · exact ⟨12 + i, by omega, by
      simp only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat]
      bv_omega⟩
  · exact ⟨16 + i, by omega, by
      simp only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat]
      bv_omega⟩
  · exact ⟨20 + i, by omega, by
      simp only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat]
      bv_omega⟩
  · exact ⟨24 + i, by omega, by
      simp only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat]
      bv_omega⟩
  · exact ⟨28 + i, by omega, by
      simp only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat]
      bv_omega⟩

theorem run_of_state [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {hash : Array UInt32}
    (caller : CalleePre initial boundary 0x10dd90 144 176 1264)
    (state : Suffix.State initial boundary s) (rip : s.RIP = 0x10e020)
    (hashWords : HashStateAt s (stackPtr initial - 232) hash) :
    ∃ t, Suffix.State initial boundary t ∧ t.RIP = 0x10e0a9 ∧
      (⟨(stackPtr initial - 192).toNat, 32⟩ : MemoryRegion).HasBytes
        t.external (serializeHash hash) := by
  have conditions := pre caller state rip
  have outside : ∀ ip : Nat, 0x10e020 ≤ ip → ip ≤ 0x10e0a9 →
      (BitVec.ofNat 64 ip) ≠ boundary.rip := by
    intro ip low high
    apply boundary_ne_program caller.outerBoundary
    have start : BitVec.ofNat 64 ip =
        Extracted.textAddress + BitVec.ofNat 64 (ip - 0x100000) := by
      change BitVec.ofNat 64 ip = BitVec.ofNat 64 0x100000 + _
      rw [← BitVec.ofNat_add]
      exact congrArg (BitVec.ofNat 64) (by omega)
    rw [start]
    exact inProgram_of_textOffset _ (by omega)
  obtain ⟨fuel, t, execution, ready, _, result⟩ := run boundary outside s
    (Hkdf.Proofs.Common.Machine.supportedMachine_readyToStep state.running.machine)
    (code state.running.loaded) conditions
  have target : rspOf s + 216 = stackPtr initial - 192 := by
    change stackPtr s + 216 = _
    rw [state.rsp]; bv_omega
  have within : WritesWithin (effect s).components
      #v[registerRegion initial .rdi 176, Stack.region initial 1264] := by
    intro c member a covered
    have byte := footprint s c member a covered
    rw [target] at byte
    exact ⟨Stack.region initial 1264, by simp,
      Hkdf.Proofs.Common.Machine.stackRegion_contains_sub caller.stack.2.2.1
        (offset := 192) (by decide) (by decide) byte⟩
  have saved : ∀ i < 48, t.external[stackPtr initial - 40 + BitVec.ofNat 64 i]? =
      s.external[stackPtr initial - 40 + BitVec.ofNat 64 i]? := by
    intro i hi
    apply result.agrees.memory
    intro c member covered
    have byte := footprint s c member _ covered
    rw [target] at byte
    obtain ⟨j, hj, equal⟩ := byte
    bv_omega
  have stable := state.of_agrees caller execution ready result.agrees within (by
    intro c member
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp [effect, Effect.components, Write.component, Operand.component]) saved
  refine ⟨t, stable, result.rip, ?_⟩
  rw [← target]
  apply payload conditions ?_ result
  have source : rspOf s + 176 = stackPtr initial - 232 := by
    change stackPtr s + 176 = _
    rw [state.rsp]; bv_omega
  rw [source]
  exact hashWords

end Hkdf.Proofs.Standard.Finalize.Suffix.Outer.Output.Serialize
