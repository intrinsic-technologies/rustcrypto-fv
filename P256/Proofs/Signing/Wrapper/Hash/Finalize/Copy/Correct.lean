import P256.Proofs.Signing.Wrapper.Hash.Finalize.State
import P256.Proofs.Signing.Wrapper.Hash.Finalize.Copy.Setup
import P256.Proofs.HMAC.State
import P256.Proofs.Common.Instructions.RepMovsqAny

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Hash.Finalize

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common

theorem copy [Bindings] {initial start s : RamState} {secret message : ByteArray}
    (pre : HashEntry initial start secret message)
    (state : Absorb.Result initial start s message) :
    ∃ t, Copied initial start t message := by
  obtain ⟨fuelA, a, runA, readyA, _, effectA⟩ := Copy.setup_run (returnBoundary initial)
    (outside pre.context) s (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x284c Copy.setupBytes
      (by decide) (by decide +kernel)) state.rip
  have agreesA : AgreesExcept [.reg 7, .reg 6, .reg 1, .rip] s a := effectA.agrees
  have frameA := state.toFrame.after_registers pre.context runA readyA agreesA
    (by simp [Component.Covers]) (by simp)
  have memoryA : a.external = s.external := agreesA.external (by simp [Component.Covers])
  have destA : a.regValue .rdi = stackPtr a + 64 := by
    exact effectA.writes.1.trans (congrArg (· + 64) (frameA.rsp.trans state.rsp.symm)).symm
  have sourceA : a.regValue .rsi = stackPtr a + 176 := by
    exact effectA.writes.2.1.trans (congrArg (· + 176)
      (frameA.rsp.trans state.rsp.symm)).symm
  have countA : a.regValue .rcx = 13 := effectA.writes.2.2
  have hn : (rcx.read a).toNat = 13 := by change (a.regValue .rcx).toNat = 13; rw [countA]; rfl
  have src : MemReadable a (rsi.read a) (8 * 13) := by
    change MemReadable a (a.regValue .rsi) 104
    rw [sourceA]
    exact stack_readable pre.context frameA (by decide)
  have dst : Instructions.CrossPageStore.Writable a (rdi.read a) (8 * 13) := by
    change Instructions.CrossPageStore.Writable a (a.regValue .rdi) 104
    rw [destA]
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      stack_writable pre.context frameA (offset := 64) (len := 104)
        (by decide) (by decide)
  have apart : (rsi.read a).toNat + 8 * 13 ≤ (rdi.read a).toNat ∨
      (rdi.read a).toNat + 8 * 13 ≤ (rsi.read a).toNat := by
    right
    change (a.regValue .rdi).toNat + 104 ≤ (a.regValue .rsi).toNat
    rw [destA, sourceA]
    change (stackPtr a + BitVec.ofNat 64 64).toNat + 104 ≤ (stackPtr a + BitVec.ofNat 64 176).toNat
    rw [ScalarFrame.scalar_stack_address frameA.rsp (by decide) (by decide : 176 ≤ 520),
      ScalarFrame.scalar_stack_address frameA.rsp (by decide) (by decide : 64 ≤ 520)]
    change (stackPtr initial - BitVec.ofNat 64 456).toNat + 104 ≤
      (stackPtr initial - BitVec.ofNat 64 344).toNat
    rw [stack_sub_toNat (stack pre.context) (by decide), stack_sub_toNat (stack pre.context) (by decide)]
    have bounds := stack_bounds (stack pre.context)
    omega
  have pc := Instructions.RepMovsqAny.pre_of_memory effectA.rip
    frameA.directionFlag.df hn src dst apart
    (by change RangeApart (a.regValue .rdi) 104
          (Extracted.textAddress + BitVec.ofNat 64 0x285e) 3
        rw [destA]
        simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
          stack_code pre.context frameA (offset := 64) (len := 104)
            (codeOffset := 0x285e) (codeLen := 3) (by decide) (by decide))
  obtain ⟨run, ready, effect, copied⟩ := Instructions.RepMovsqAny.rep_movsq_execution
    pre.context.bindingsSupported.stringStride readyA
    (programText_slice (programLoaded_codeIn frameA.loaded) 0x285e [0xf3,0x48,0xa5]
      (by decide) (by decide +kernel)) pc hn
    (boundary_ne_program (outside pre.context) (inProgram_of_textOffset 0x285e (by decide)))
    (boundary_ne_program (outside pre.context) (inProgram_of_textOffset 0x2861 (by decide)))
  simp only [show max 13 1 = 13 from rfl] at run ready effect copied
  generalize ht : nextStates 13 a = t at run ready effect copied
  have agrees : AgreesExcept [.reg 6, .reg 7, .reg 1, .mem (stackPtr a + 64) 104, .rip] a t := by
    simpa only [repMovsqEffect_components, hn, Nat.reduceMul,
      show rdi.read a = stackPtr a + 64 from destA] using effect.agrees
  have writes : WritesWithin [.reg 6, .reg 7, .reg 1, .mem (stackPtr a + 64) 104, .rip]
      #v[workRegion initial] := by
    intro c hc addr covered
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact covered.elim
    change (Component.mem (stackPtr a + BitVec.ofNat 64 64) 104).Covers addr at covered
    rw [ScalarFrame.scalar_stack_address frameA.rsp (by decide) (by decide : 64 ≤ 520)] at covered
    exact ⟨_, by simp, work_contains pre.context
      (by decide) (by decide) covered⟩
  have frameT := frameA.after_effect pre.context run ready agrees writes
    ((agrees.read (n := 64) (r := 4) (by simp)).trans frameA.rsp) (by simp)
  refine ⟨t, ⟨⟨frameT⟩, effect.rip, ?_⟩⟩
  apply state.hash.copy
  change ∀ i < 104, t.external[a.regValue .rdi + BitVec.ofNat 64 i]? =
    a.external[a.regValue .rsi + BitVec.ofNat 64 i]? at copied
  simpa only [destA, sourceA, frameA.rsp, memoryA, frameBase, BitVec.ofNat_eq_ofNat] using copied

end P256.Proofs.Signing.Wrapper.Hash.Finalize
