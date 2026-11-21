import P256.Proofs.Sec1.Decompress.Input.CanonicalState
import P256.Proofs.Sec1.Decompress.Input.ConversionSetup
import P256.Proofs.Sec1.Decompress.Input.Call
import P256.Proofs.Sec1.Decompress.Convert.Interface
import P256.Proofs.Program.CalleeStack

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decompress.Input

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Standards.SECG.ECC
open P256.Proofs.SecretKeyFromBytes.Scalar

structure ConversionEntry [Bindings] (s t : RamState) (boundary : ReturnBoundary)
    (x : Nat) (odd : Bool) : Prop extends ScalarFrame.FrameState s t 80 2592 416 where
  pre : Convert.Pre t boundary
  raw : Nat256At t (t.regValue .rsi) x
  output : t.regValue .rdi = stackPtr s - 408
  ret : (returnBoundary t).rip = 0x10fcf4
  parity : memLoad t.external (stackPtr s - 332) 32 = BitVec.ofNat 32 odd.toNat
  savedOutput : memLoad t.external (stackPtr s - 224) 64 = s.regValue .rdi
  valid : t.regValue .rbx = if x < P256.Spec.Operations.domain.p then 1 else 0
  r14 : t.regValue .r14 = 0xffffffff00000001
  r15 : t.regValue .r15 = stackPtr s - 408

def conversionLayout : StackCallLayout 2592 32 32 160 :=
  ⟨416, 328, 408, by decide, by decide, by decide, by decide,
    by decide, by decide, .inr (by decide)⟩

theorem conversion_entry [Bindings] {s u : RamState} {boundary : ReturnBoundary}
    {bytes : ByteArray} {odd : Bool} (pre : Pre s boundary bytes odd)
    (state : CanonicalState s u (Encoding.octetsToNat bytes) odd) :
    ∃ fuel t, Advances boundary fuel u t ∧
      ConversionEntry s t boundary (Encoding.octetsToNat bytes) odd := by
  obtain ⟨n, v, runV, readyV, _, effectV⟩ := conversion_setup_correct boundary pre.outerBoundary u
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0xfcd0 conversionSetupBytes
      (by decide) (by decide +kernel)) state.rip
  have frameV := state.toFrameState.after_registers readyV effectV.agrees
    (by simp [conversionSetupEffect, Effect.components, Component.Covers])
    (by simp [conversionSetupEffect, Effect.components])
  have memoryV := effectV.agrees.external
    (by simp [conversionSetupEffect, Effect.components, Component.Covers])
  obtain ⟨t, runT, readyT, effectT⟩ := ScalarFrame.scalar_call pre.toCalleePre
    (by decide) (by decide) frameV 0xfcef 0xffff927c
    (by decide) (by decide +kernel) (by decide)
    (inProgram_of_textOffset 0x0 (by decide)) effectV.rip
  change (callEffect (fun _ => 0x108f70) 0x10fcf4 v).Holds v t at effectT
  have frameT := ScalarFrame.FrameState.after_call pre.toCalleePre (by decide) (by decide)
    frameV readyT effectT
  have regs (r : BitVec 5) (hr : r ≠ 4) :
      (Operand.reg r : Operand 64).read t = (Operand.reg r : Operand 64).read v :=
    effectT.agrees.read (by simpa [pushEffect_components] using hr)
  have source : t.regValue .rsi = stackPtr s - 328 := by
    have h := (regs 6 (by decide)).trans effectV.writes.2.1
    exact h.trans (ScalarFrame.scalar_stack_address state.rsp (by decide) (by decide))
  have output : t.regValue .rdi = stackPtr s - 408 :=
    ((regs 7 (by decide)).trans effectV.writes.2.2.2.1).trans state.rsp
  have ret : (returnBoundary t).rip = 0x10fcf4 := (callEffect_stack effectT).1
  have cp : Convert.Pre t boundary := by
    refine ⟨CalleePre.of_stack pre.toCalleePre conversionLayout frameT.bindingsSupported
      frameT.machine frameT.directionFlag frameT.loaded frameT.allocated effectT.rip
      frameT.rsp source output ?_, ?_, ?_, ?_⟩
    · rw [ret]; exact inProgram_of_textOffset 0xfcf4 (by decide)
    · exact (regs 2 (by decide)).trans effectV.writes.2.2.2.2.1
    · exact (regs 1 (by decide)).trans effectV.writes.2.2.2.2.2
    · exact (regs 8 (by decide)).trans effectV.writes.2.2.1
  refine ⟨n+1, t, runV.trans runT, ⟨frameT, cp, ?_, output, ret, ?_, ?_, ?_, ?_, ?_⟩⟩
  · rw [source]
    refine ⟨state.raw.1, ?_⟩
    intro i hi
    have h := ScalarFrame.scalar_call_byte (offset := 328) (len := 32)
      (by decide) frameV effectT (by decide) (by decide) hi
    rw [memoryV] at h
    exact h.trans (state.raw.2 i hi)
  · have h := ScalarFrame.scalar_call_read (offset := 332) (n := 32)
      (by decide) frameV effectT (by decide) (by decide)
    change memLoad t.external (stackPtr s - 332) 32 = memLoad v.external (stackPtr s - 332) 32 at h
    rw [memoryV] at h
    exact h.trans state.parity
  · have h := ScalarFrame.scalar_call_read (offset := 224) (n := 64)
      (by decide) frameV effectT (by decide) (by decide)
    change memLoad t.external (stackPtr s - 224) 64 = memLoad v.external (stackPtr s - 224) 64 at h
    rw [memoryV] at h
    exact h.trans state.output
  · exact ((regs 3 (by decide)).trans (effectV.agrees.read (n := 64) (r := 3)
      (by simp [conversionSetupEffect, Effect.components]))).trans state.valid
  · exact ((regs 14 (by decide)).trans (effectV.agrees.read (n := 64) (r := 14)
      (by simp [conversionSetupEffect, Effect.components]))).trans state.r14
  · exact ((regs 15 (by decide)).trans effectV.writes.1).trans state.rsp

end P256.Proofs.Sec1.Decompress.Input
