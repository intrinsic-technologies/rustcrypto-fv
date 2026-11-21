import P256.Proofs.PublicPoint.Normalize.Finish.Memory
import P256.Proofs.Common.Instructions.RepMovsqAny

set_option autoImplicit false

namespace P256.Proofs.PublicPoint.Normalize.Finish

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

theorem movsq72 [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10e6f0 32 65 3352)
    (state : FrameState s t 65 3352 1944)
    (off dst : Nat) (hc : off + 3 < 118431) (hd : dst + 72 ≤ 1896)
    (bytes : Extracted.textBytes.toListFrom off 3 = [0xf3, 0x48, 0xa5])
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 off)
    (destination : t.regValue .rdi = stackPtr t + BitVec.ofNat 64 dst)
    (count : t.regValue .rcx = 9)
    (source : MemReadable t (t.regValue .rsi) 72)
    (apart : (t.regValue .rsi).toNat + 72 ≤ (t.regValue .rdi).toNat ∨
      (t.regValue .rdi).toNat + 72 ≤ (t.regValue .rsi).toNat) :
    ∃ u, Advances boundary 9 t u ∧ FrameState s u 65 3352 1944 ∧
      u.RIP = Extracted.textAddress + BitVec.ofNat 64 (off + 3) ∧
      (∀ i < 72, u.external[t.regValue .rdi + BitVec.ofNat 64 i]? =
        t.external[t.regValue .rsi + BitVec.ofNat 64 i]?) ∧
      AgreesExcept [.reg 6, .reg 7, .reg 1, .mem (t.regValue .rdi) 72, .rip] t u := by
  have hn : (rcx.read t).toNat = 9 := by change (t.regValue .rcx).toNat = 9; rw [count]; rfl
  have writable : P256.Proofs.Common.Instructions.CrossPageStore.Writable t (t.regValue .rdi) 72 := by
    rw [destination]
    exact stack_writable (frameOffset := 1944) pre state (by decide) (by omega) (by decide)
  have pc := P256.Proofs.Common.Instructions.RepMovsqAny.pre_of_memory rip
    state.directionFlag.df hn source writable apart
    (by change RangeApart (t.regValue .rdi) 72 _ 3
        rw [destination]; exact stack_code (frameOffset := 1944) pre state (by decide) (by omega) (by omega))
  have next : Extracted.textAddress + BitVec.ofNat 64 off + (3 : BitVec 64) =
      Extracted.textAddress + BitVec.ofNat 64 (off + 3) := by
    rw [BitVec.ofNat_add, BitVec.add_assoc]
    rfl
  obtain ⟨run, ready, effect, copied⟩ :=
    P256.Proofs.Common.Instructions.RepMovsqAny.rep_movsq_execution state.bindingsSupported.stringStride
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) off [0xf3, 0x48, 0xa5]
        (by change off + 3 ≤ 118431; omega) bytes)
      pc hn (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset _ (by omega)))
      (boundary_ne_program pre.outerBoundary (by rw [next]; exact inProgram_of_textOffset _ hc))
  simp only [show max 9 1 = 9 from rfl] at run ready effect copied
  generalize hu : nextStates 9 t = u at run ready effect copied
  have g : AgreesExcept [.reg 6, .reg 7, .reg 1, .mem (t.regValue .rdi) 72, .rip] t u := by
    have hg := effect.agrees
    simp only [repMovsqEffect_components, hn, Nat.reduceMul] at hg
    exact hg
  have frame := state.after_effect pre (by decide) ready g
    (by intro c hc a ha
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl <;> try exact ha.elim
        rw [destination] at ha
        exact ⟨workRegion s 3352, by simp, local_work pre state hd ha⟩)
    (by simp)
  exact ⟨u, run, frame, effect.rip.trans next, copied, g⟩

end P256.Proofs.PublicPoint.Normalize.Finish
