import P256.Proofs.Verifying.Core.Finish.Memory
import P256.Proofs.Common.Instructions.RepMovsqAny

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Combine

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

theorem movsq [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10d570 72 24 9992)
    (state : FrameState s t 24 9992 1176)
    (off dst count : Nat) (positive : 0 < count) (hc : off + 3 < 118431) (hd : dst + (8 * count) ≤ 1128)
    (bytes : Extracted.textBytes.toListFrom off 3 = [0xf3, 0x48, 0xa5])
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 off)
    (destination : t.regValue .rdi = stackPtr t + BitVec.ofNat 64 dst)
    (hcount : t.regValue .rcx = BitVec.ofNat 64 count)
    (source : MemReadable t (t.regValue .rsi) (8 * count))
    (apart : (t.regValue .rsi).toNat + (8 * count) ≤ (t.regValue .rdi).toNat ∨
      (t.regValue .rdi).toNat + (8 * count) ≤ (t.regValue .rsi).toNat) :
    ∃ u, Advances boundary count t u ∧ FrameState s u 24 9992 1176 ∧
      u.RIP = Extracted.textAddress + BitVec.ofNat 64 (off + 3) ∧
      (∀ i < (8 * count), u.external[t.regValue .rdi + BitVec.ofNat 64 i]? =
        t.external[t.regValue .rsi + BitVec.ofNat 64 i]?) ∧
      AgreesExcept [.reg 6, .reg 7, .reg 1, .mem (t.regValue .rdi) (8 * count), .rip] t u := by
  have hn : (rcx.read t).toNat = count := by
    change (t.regValue .rcx).toNat = count
    rw [hcount,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega)]
  have writable : P256.Proofs.Common.Instructions.CrossPageStore.Writable t (t.regValue .rdi) (8 * count) := by
    rw [destination]
    exact stack_writable (frameOffset := 1176) pre state (by decide) (by omega) (by omega)
  have pc := P256.Proofs.Common.Instructions.RepMovsqAny.pre_of_memory rip
    state.directionFlag.df hn source writable apart
    (by change RangeApart (t.regValue .rdi) (8 * count) _ 3
        rw [destination]; exact stack_code (frameOffset := 1176) pre state (by decide) (by omega) (by omega))
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
  simp only [Nat.max_eq_left (by omega : 1 ≤ count)] at run ready effect copied
  generalize hu : nextStates count t = u at run ready effect copied
  have g : AgreesExcept [.reg 6, .reg 7, .reg 1, .mem (t.regValue .rdi) (8 * count), .rip] t u := by
    have hg := effect.agrees
    simp only [repMovsqEffect_components, hn] at hg
    exact hg
  have frame := state.after_effect pre (by decide) ready g
    (by intro c hc a ha
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl <;> try exact ha.elim
        rw [destination] at ha
        exact ⟨workRegion s 9992, by simp, Core.Finish.local_work pre state hd ha⟩)
    (by simp)
  exact ⟨u, run, frame, effect.rip.trans next, copied, g⟩

end P256.Proofs.Verifying.Core.Combine
