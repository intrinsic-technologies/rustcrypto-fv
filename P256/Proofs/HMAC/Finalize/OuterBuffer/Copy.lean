import P256.Proofs.HMAC.Finalize.Interface
import P256.Proofs.HMAC.Finalize.Frame
import P256.Proofs.Common.Instructions.RepMovsqAny

set_option autoImplicit false

namespace P256.Proofs.HMAC.Finalize.OuterBuffer

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Program.ScalarFrame (workRegion)
open P256.Proofs.Common
open P256.Proofs.Program (stack_bounds stack_sub_toNat)

theorem copy_state [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {message : ByteArray} (pre : HashCalleePre initial boundary 0x100f10 168 672)
    (state : ScalarFrame.FrameState initial s 0 672 328)
    (rip : s.RIP = 0x101252)
    (source : s.regValue .rsi = stackPtr s + 176)
    (destination : s.regValue .rdi = stackPtr s + 72)
    (count : s.regValue .rcx = 13)
    (outputPointer : s.regValue .rbx = initial.regValue .rsi)
    (outer : Sha256StateAt s (stackPtr initial - 152#64) message) :
    ∃ t, Advances boundary 13 s t ∧ Buffered initial t message ∧
      t.RIP = paddingStart true := by
  have srcAddress : stackPtr s + 176 = stackPtr initial - 152#64 :=
    stack_address state.rsp (by decide : 176 ≤ 328)
  have dstAddress : stackPtr s + 72 = stackPtr initial - 256#64 :=
    stack_address state.rsp (by decide : 72 ≤ 328)
  have hn : (rcx.read s).toNat = 13 := by
    change (s.regValue .rcx).toNat = 13
    rw [count]
    rfl
  have src : MemReadable s (rsi.read s) (8 * 13) := by
    change MemReadable s (s.regValue .rsi) 104
    rw [source]
    exact ScalarFrame.stack_readable (stackPre pre) state (by decide) (by decide)
  have dst : Common.Instructions.CrossPageStore.Writable s (rdi.read s) (8 * 13) := by
    change Common.Instructions.CrossPageStore.Writable s (s.regValue .rdi) 104
    rw [destination]
    exact ScalarFrame.stack_writable (stackPre pre) state (by decide) (by decide) (by decide)
  have apart : (rsi.read s).toNat + 8 * 13 ≤ (rdi.read s).toNat ∨
      (rdi.read s).toNat + 8 * 13 ≤ (rsi.read s).toNat := by
    right
    change (s.regValue .rdi).toNat + 104 ≤ (s.regValue .rsi).toNat
    rw [destination, source, dstAddress, srcAddress]
    rw [stack_sub_toNat pre.stack (by decide),
      stack_sub_toNat pre.stack (by decide)]
    have bounds := stack_bounds pre.stack
    omega
  have pc := Common.Instructions.RepMovsqAny.pre_of_memory rip state.directionFlag.df hn src dst apart
    (by change RangeApart (s.regValue .rdi) 104 _ 3
        rw [destination]
        exact ScalarFrame.stack_code (stackPre pre) state (by decide) (by decide) (codeOffset := 0x1252) (by decide))
  obtain ⟨run, ready, effect, copied⟩ := Common.Instructions.RepMovsqAny.rep_movsq_execution pre.bindingsSupported.stringStride
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x1252 [0xf3, 0x48, 0xa5]
      (by decide) (by decide +kernel)) pc hn
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1252 (by decide)))
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1255 (by decide)))
  simp only [show max 13 1 = 13 from rfl] at run ready effect copied
  generalize ht : nextStates 13 s = t at run ready effect copied
  have agrees : AgreesExcept [.reg 6, .reg 7, .reg 1,
      .mem (stackPtr s + 72) 104, .rip] s t := by
    simpa only [repMovsqEffect_components, hn, Nat.reduceMul,
      show rdi.read s = stackPtr s + 72 from destination] using effect.agrees
  have frame := state.after_effect (stackPre pre) (by decide) ready agrees (by
    intro c hc a covered
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact covered.elim
    exact ⟨workRegion initial 672, by simp,
      local_work_contains pre state.rsp (by decide) covered⟩) (by simp)
  refine ⟨t, run, ⟨frame,
    (agrees.read (n := 64) (r := 3) (by simp)).trans outputPointer, ?_⟩, effect.rip⟩
  apply outer.copy
  change ∀ i < 104, t.external[s.regValue .rdi + BitVec.ofNat 64 i]? =
    s.external[s.regValue .rsi + BitVec.ofNat 64 i]? at copied
  simpa only [destination, source,
    dstAddress, srcAddress] using copied

end P256.Proofs.HMAC.Finalize.OuterBuffer
