import P256.Proofs.Projective.Add.CrossTerms.Memory
import P256.Proofs.Common.EffectCompose.Advance
import P256.Proofs.Common.EffectCompose.Memory
import X86Proofs.Instructions.Lea.Triple

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)

namespace P256.Proofs.Projective.Add.Combinations

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure SetupPre (ip : BitVec 64) (s : RamState) : Prop where
  rip : s.RIP = ip
  readable : ∀ offset : Nat, offset + 8 ≤ 632 → MemReadable s (stackPtr s + BitVec.ofNat 64 offset) 8
  writable : ∀ offset : Nat, offset + 8 ≤ 632 → P256.Proofs.Common.Instructions.CrossPageStore.Writable s (stackPtr s + BitVec.ofNat 64 offset) 8
  apart : ∀ offset : Nat, offset + 8 ≤ 632 → ∀ codeOffset codeLen : Nat,
    codeOffset + codeLen ≤ 118431 → RangeApart (stackPtr s + BitVec.ofNat 64 offset) 8
      (Extracted.textAddress + BitVec.ofNat 64 codeOffset) codeLen

def setupComponents (s : RamState) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 5, .reg 6, .reg 7, .reg 12, .reg 13, .reg 14, .reg 15,
    .mem (stackPtr s + 8) 8, .mem (stackPtr s + 16) 8,
    .mem (stackPtr s + 24) 8, .mem (stackPtr s + 32) 8,
    .mem (stackPtr s + 40) 8, .mem (stackPtr s + 48) 8,
    .mem (stackPtr s + 56) 8, .mem (stackPtr s + 64) 8, .rip]

theorem setup_pre [Bindings] {s t : RamState} {boundary : ReturnBoundary} {ip : BitVec 64}
    (pre : CalleePre s boundary 0x1051f0 96 96 920) (state : FrameState s t 96 920 632)
    (rip : t.RIP = ip) : SetupPre ip t :=
  ⟨rip, fun _ h => stack_readable (frameOffset := 632) pre state (by decide) h,
    fun _ h => stack_writable (frameOffset := 632) pre state (by decide) h (by decide),
    fun _ h _ _ hc => stack_code (frameOffset := 632) pre state (by decide) h hc⟩

theorem setup_covers {t : RamState} {c : Component} {a : BitVec 64}
    (hc : c ∈ setupComponents t) (ha : c.Covers a) :
    ∃ offset : Nat, offset ∈ [8,16,24,32,40,48,56,64] ∧
      (Component.mem (stackPtr t + BitVec.ofNat 64 offset) 8).Covers a := by
  simp only [setupComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact ha.elim
  all_goals first
    | exact ⟨8, by decide, ha⟩
    | exact ⟨16, by decide, ha⟩
    | exact ⟨24, by decide, ha⟩
    | exact ⟨32, by decide, ha⟩
    | exact ⟨40, by decide, ha⟩
    | exact ⟨48, by decide, ha⟩
    | exact ⟨56, by decide, ha⟩
    | exact ⟨64, by decide, ha⟩

theorem setup_after [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x1051f0 96 96 920) (state : FrameState s t 96 920 632)
    (ready : ReadyToStep u) (agrees : AgreesExcept (setupComponents t) t u) : FrameState s u 96 920 632 := by
  apply state.after_effect pre (by decide) ready agrees ?_ (by simp [setupComponents])
  intro c hc a ha
  obtain ⟨offset, hoff, cover⟩ := setup_covers hc ha
  have bound : 8 ≤ offset ∧ offset ≤ 64 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
    omega
  rw [scalar_stack_address (frameOffset := 632) state.rsp (by decide) (by omega)] at cover
  exact ⟨workRegion s 920, by simp, work_contains pre (by omega) (by omega) cover⟩

theorem setup_keep [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x1051f0 96 96 920) (state : FrameState s t 96 920 632)
    (agrees : AgreesExcept (setupComponents t) t u) {offset value : Nat}
    (bound : offset ≤ 560) (input : MontgomeryAt t (stackPtr s - BitVec.ofNat 64 offset) value) :
    MontgomeryAt u (stackPtr s - BitVec.ofNat 64 offset) value := by
  apply input.of_bytes_eq
  intro i hi
  apply agrees.byte
  intro c hc cover
  obtain ⟨off, hoff, j, hj, he⟩ := setup_covers hc cover
  have bound' : 8 ≤ off ∧ off ≤ 64 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hoff
    omega
  rw [scalar_stack_address (frameOffset := 632) state.rsp (by decide) (by omega)] at he
  have bounds := stack_bounds pre.stack
  have lo := stack_sub_toNat pre.stack (offset := 632-off) (by omega)
  have lo' := stack_sub_toNat pre.stack (offset := offset) (by omega)
  have eq := congrArg BitVec.toNat he
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat, lo, lo'] at eq
  omega

theorem setup_run [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {offset : Nat} {bytes : List UInt8} {E : RamState → Effect}
    (pre : CalleePre s boundary 0x1051f0 96 96 920) (state : FrameState s t 96 920 632)
    (block : AdvanceTriple boundary (SetupPre (Extracted.textAddress + BitVec.ofNat 64 offset))
      (codeRange (Extracted.textAddress + BitVec.ofNat 64 offset) bytes) (Effect.post E))
    (bound : offset + bytes.length ≤ 118431)
    (code : Extracted.textBytes.toListFrom offset bytes.length = bytes)
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 offset)
    (components : ∀ c ∈ (E t).components, c ∈ setupComponents t) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u 96 920 632 ∧ (E t).Holds t u ∧
      (∀ offset value : Nat, offset ≤ 560 →
        MontgomeryAt t (stackPtr s - BitVec.ofNat 64 offset) value →
        MontgomeryAt u (stackPtr s - BitVec.ofNat 64 offset) value) := by
  obtain ⟨fuel, u, run, ready, _, effect⟩ := block t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) offset bytes bound code)
    (setup_pre pre state rip)
  have agrees : AgreesExcept (setupComponents t) t u := effect.agrees.mono components
  exact ⟨fuel, u, run, setup_after pre state ready agrees, effect,
    fun _ _ h hx => setup_keep pre state agrees h hx⟩

end P256.Proofs.Projective.Add.Combinations
