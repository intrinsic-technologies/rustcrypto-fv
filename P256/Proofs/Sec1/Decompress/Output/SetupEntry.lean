import P256.Proofs.Sec1.Decompress.Output.Setup
import P256.Proofs.Sec1.Decompress.State
import P256.Proofs.Program.ScalarFrame.Memory
import P256.Proofs.Program.WrapperMemory
import P256.Proofs.Sec1.Representation

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decompress.Output

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem setup_pre [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10fc00 32 80 2592) (state : Frame s t)
    (rip : t.RIP = 0x11008f) : SetupPre t := by
  refine ⟨rip, ?_, ?_, ?_⟩
  · have hw := ScalarFrame.stack_writable pre state (offset := 64) (len := 1)
      (by decide) (by decide) (by decide)
    exact ⟨hw.low, hw.mem, hw.tables⟩
  · exact ScalarFrame.stack_readable pre state (offset := 184) (len := 8) (by decide) (by decide)
  · intro offset len hc
    exact ScalarFrame.stack_code pre state (offset := 64) (len := 1) (by decide) (by decide) hc

def setupComponents (s : RamState) : List Component :=
  [.reg 6, .reg 1, .reg 3, .reg 7, .mem (stackPtr s - 344) 1, .rip]

theorem setup_point [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10fc00 32 80 2592) (state : Frame s t)
    (rip : t.RIP = 0x11008f)
    (savedOutput : memLoad t.external (stackPtr s - 224) 64 = s.regValue .rdi) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x1100a7 ∧
      u.regValue .rsi = stackPtr s - 408 ∧ u.regValue .rdi = s.regValue .rdi ∧
      u.regValue .rbx = s.regValue .rdi ∧ u.regValue .rcx = 9 ∧
      (∀ x y, Field.MontgomeryAt t (stackPtr s - 408) x →
        Field.MontgomeryAt t (stackPtr s - 376) y →
        AffineAt u (stackPtr s - 408) (.affine x y)) ∧
      AgreesExcept (setupComponents s) t u := by
  obtain ⟨fuel, u, run, ready, _, effect⟩ := setup boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x1008f setupBytes
      (by decide) (by decide +kernel)) (setup_pre pre state rip)
  have flagAddress : stackPtr t + 64 = stackPtr s - 344 :=
    ScalarFrame.scalar_stack_address state.rsp (by decide) (by decide)
  have savedAddress : stackPtr t + 184 = stackPtr s - 224 :=
    ScalarFrame.scalar_stack_address state.rsp (by decide) (by decide)
  have agrees : AgreesExcept (setupComponents s) t u := by
    have h := effect.agrees
    x86_norm [setupEffect] at h
    change AgreesExcept [.reg 6,.reg 1,.reg 3,.reg 7,.mem (stackPtr t + 64) 1,.rip] t u at h
    simpa only [flagAddress, setupComponents] using h
  have writes : WritesWithin (setupComponents s)
      #v[registerRegion s .rdi 80, ScalarFrame.workRegion s 2592] := by
    intro c hc a ha
    simp only [setupComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    exact ⟨_, by simp, ScalarFrame.work_contains pre (by decide) (by decide) ha⟩
  have finalState := state.after_effect pre (by decide) ready agrees writes (by simp [setupComponents])
  have values := effect.writes
  change _ ∧ _ ∧ _ ∧ _ ∧ _ at values
  rcases values with ⟨src, count, rbx, dst, flag⟩
  change u.regValue .rsi = stackPtr t at src
  change u.regValue .rcx = 9 at count
  change u.regValue .rbx = memLoad t.external (stackPtr t + 184) 64 at rbx
  change u.regValue .rdi = memLoad t.external (stackPtr t + 184) 64 at dst
  change memLoad u.external (stackPtr t + 64) 8 = (0 : BitVec 8) at flag
  rw [savedAddress, savedOutput] at rbx dst
  rw [flagAddress] at flag
  refine ⟨fuel, u, run, finalState, effect.rip, src.trans state.rsp, dst, rbx, count, ?_, agrees⟩
  intro x y hx hy
  have keep (offset : Nat) (ho : 376 ≤ offset ∧ offset ≤ 408) (i : Nat) (hi : i < 32) :
      u.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
        t.external[stackPtr s - BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? := by
    apply agrees.byte
    intro c hc hv
    simp only [setupComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact hv.elim
    obtain ⟨j, hj, he⟩ := hv
    exact stack_sub_apart pre.stack (a := 344) (b := offset)
      (by decide) (by omega) (by decide) (by omega) (.inr (by omega)) j hj i hi he.symm
  have hx' := hx.of_bytes_eq (keep 408 (by decide))
  have hy' := hy.of_bytes_eq (keep 376 (by decide))
  have hr := ScalarFrame.stack_readable pre finalState (offset := 64) (len := 1) (by decide) (by decide)
  have addressU : stackPtr u + 64 = stackPtr s - 344 :=
    ScalarFrame.scalar_stack_address finalState.rsp (by decide) (by decide)
  change MemReadable u (stackPtr u + 64) 1 at hr
  rw [addressU] at hr
  have flagByte : u.external[stackPtr s - 344]? = some 0 := by
    have bytes := Bytes.of_memLoad (n := 8) hr.mem
    rw [flag] at bytes
    have zero : storedByte (0#8) 0 = (0 : UInt8) := by decide +kernel
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero, zero] using bytes 0 (by decide)
  refine ⟨hx', ?_, ?_⟩
  · have ha : stackPtr s - 408 + 32 = stackPtr s - 376 := by
      simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
    exact ha.symm ▸ hy'
  · have ha : stackPtr s - 408 + 64 = stackPtr s - 344 := by
      simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
    exact ha.symm ▸ flagByte

end P256.Proofs.Sec1.Decompress.Output
