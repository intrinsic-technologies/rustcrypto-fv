import P256.Proofs.Generate.Scalar.Load
import P256.Proofs.Program.ScalarFrame.Input

set_option autoImplicit false

namespace P256.Proofs.Generate.Scalar

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program

def Decoded (t : RamState) (value : Nat) : Prop :=
  t.regValue .r13 = BitVec.ofNat 64 value ∧
  t.regValue .r12 = BitVec.ofNat 64 (value / 2^64) ∧
  t.regValue .r15 = BitVec.ofNat 64 (value / 2^128) ∧
  t.regValue .r14 = BitVec.ofNat 64 (value / 2^192)

theorem Decoded.of_agrees {s t : RamState} {value : Nat} {cs : List Component}
    (decoded : Decoded s value) (agrees : AgreesExcept cs s t)
    (registers : ∀ r ∈ ([12,13,14,15] : List (BitVec 5)), .reg r ∉ cs) : Decoded t value :=
  ⟨(agrees.read (n := 64) (r := 13) (registers 13 (by simp))).trans decoded.1,
   (agrees.read (n := 64) (r := 12) (registers 12 (by simp))).trans decoded.2.1,
   (agrees.read (n := 64) (r := 15) (registers 15 (by simp))).trans decoded.2.2.1,
   (agrees.read (n := 64) (r := 14) (registers 14 (by simp))).trans decoded.2.2.2⟩

theorem entry_correct [Bindings] {s : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    (pre : Pre s boundary) (input : (registerRegion s .rsi 32).HasBytes s.external bytes) :
    ∃ n t, Advances boundary n s t ∧ State s t ∧ t.RIP = 0x112efb ∧
      stackPtr t = stackPtr s - 56 ∧ t.regValue .rbx = s.regValue .rdi ∧
      Decoded t (Arith.uint bytes) := by
  obtain ⟨u, run, state, rip, rsp, agrees⟩ := prologue_correct pre
  have inputU := ScalarFrame.input_bytes_of_frame pre state.frame input
  have source : u.regValue .rsi = s.regValue .rsi :=
    agrees.read (n := 64) (r := 6) (by simp [entryComponents, pushSequenceFrame])
  have output : u.regValue .rdi = s.regValue .rdi :=
    agrees.read (n := 64) (r := 7) (by simp [entryComponents, pushSequenceFrame])
  have hp : LoadPre u := by
    refine ⟨rip, ?_⟩
    intro i hi
    change MemReadable u (u.regValue .rsi + i) 8
    rw [source]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    all_goals
      have bound : (s.regValue .rsi).toNat + 32 < 2^32 := pre.inputBounded
      exact readable_of_grow
        (memoryRegion_memReadable pre.inputBounded pre.inputAllocated
          (by simp [registerRegion] <;> omega)
          (by simp [registerRegion] <;> omega)) state.allocated
  obtain ⟨n, t, runT, readyT, _, effect⟩ := load_correct boundary pre.outerBoundary u
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x12edd loadBytes
      (by decide) (by decide +kernel)) hp
  have stateT := state.after_registers pre readyT effect.agrees
    (by simp [loadEffect, Effect.components, Component.Covers])
    (by simp [loadEffect, Effect.components])
  have words := effect.writes
  change t.regValue .r14 = Common.Instructions.bswap64 (memLoad u.external (u.regValue .rsi) 64) ∧
    t.regValue .r15 = Common.Instructions.bswap64 (memLoad u.external (u.regValue .rsi + 8) 64) ∧
    t.regValue .r12 = Common.Instructions.bswap64 (memLoad u.external (u.regValue .rsi + 16) 64) ∧
    t.regValue .rbx = u.regValue .rdi ∧
    t.regValue .r13 = Common.Instructions.bswap64 (memLoad u.external (u.regValue .rsi + 24) 64) at words
  have limb (j : Nat) (hj : j < 4) := ReadBe.bswap_input_memLoad_limb inputU j hj
  refine ⟨6+n, t, run.trans runT, stateT, effect.rip,
    (effect.agrees.read (n := 64) (r := 4) (by simp [loadEffect, Effect.components])).trans rsp,
    words.2.2.2.1.trans output, ?_⟩
  rw [source] at words
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h := limb 3 (by decide)
    change Common.Instructions.bswap64 (memLoad u.external (s.regValue .rsi + 24) 64) =
      BitVec.ofNat 64 (Arith.uint bytes / 1) at h
    rw [Nat.div_one] at h
    exact words.2.2.2.2.trans h
  · exact words.2.2.1.trans (limb 2 (by decide))
  · exact words.2.1.trans (limb 1 (by decide))
  · have h := limb 0 (by decide)
    change Common.Instructions.bswap64 (memLoad u.external (s.regValue .rsi + 0) 64) =
      BitVec.ofNat 64 (Arith.uint bytes / 2^192) at h
    exact words.1.trans (by simpa using h)

end P256.Proofs.Generate.Scalar
