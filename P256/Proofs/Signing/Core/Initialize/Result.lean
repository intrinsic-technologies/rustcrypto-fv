import P256.Proofs.Signing.Core.Initialize.CallState
import P256.Proofs.Signing.Core.Initialize.Memory
import P256.Proofs.Nonce.Fill.Memory
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.Add.Generated.Imm8.Triple

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Initialize

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open NextNonce (scalarFrame coreFrame base_add base_nat)
open SecretKeyFromBytes.Scalar (Nat256At)

theorem nonce_result [Bindings] {s t u v : RamState} {boundary : ReturnBoundary} {secret : Nat}
    {state : Nonce.State} (pre : SignPre s boundary) (input : CallInput s t secret)
    (entered : Entered s t u) (result : CalleeResult u v boundary 72 2144)
    (generator : Nonce.GeneratorAt v (u.regValue .rdi) (frameBase s + 272) state) :
    ∃ w, Advances boundary 1 v w ∧ Initialized s w state ∧ w.RIP = 0x10ca73 := by
  have out : u.regValue .rdi = frameBase s + 2160 :=
    (entered.registers .rdi (by decide)).trans input.rdi
  have dest : u.regValue .rdi = stackPtr s - 120 := out.trans (base_add s (by decide))
  have frame : ScalarFrame.FrameState s v 65 4584 2296 :=
    FieldCall.after_result (frameOffset := 2296) pre.toCalleePre entered.frame result (by decide)
      (FieldCall.stack_result_work_frame pre.toCalleePre entered.frame result dest
        (by decide) (by decide) (by decide) (by decide))
  have ip : v.RIP = 0x10ca6f := result.rip.trans entered.returnAddress
  obtain ⟨w, run2, ready2, e2⟩ := (add_r64_imm8_effect_step 0x10ca6f 0x48 0xc4 16
    (by simp [RexWPrefix]) rfl rfl).advances
    (readyToStep result.machine result.bindingsSupported)
    (programText_slice (programLoaded_codeIn result.loaded)
      0xca6f _ (by decide) (by decide +kernel)) ip
    (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xca73 (by decide)))
  change (addR64Imm8Effect 0x10ca6f 4 16 v).Holds v w at e2
  have agrees : AgreesExcept [.reg 4,.flags,.rip] v w := e2.agrees
  have memory : w.external = v.external := agrees.external (by simp [Component.Covers])
  have sp : stackPtr w = frameBase s := by
    have wSP : stackPtr w = stackPtr v + 16 := e2.writes
    rw [wSP, frame.rsp]
    simp only [frameBase, BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have finalFrame : Frame s w := by
    refine ⟨supportedMachine_of_ready_agrees frame.machine ready2 agrees,
      bindingsSupported_of_ready_agrees frame.bindingsSupported ready2 agrees,
      ?_, agrees.directionFlagClear (by simp) frame.directionFlag,
      fun a ha => agrees.grow a (frame.allocated a ha), ?_, sp, ?_, ?_,
      (agrees.mxcsr (by simp)).trans frame.mxcsr, (agrees.fcw (by simp)).trans frame.fp87⟩
    · intro a b hb; rw [memory]; exact frame.loaded a b hb
    · simpa only [MemoryWriteFrame, memory] using frame.frame
    · intro entry he; simpa only [Operand.read, memory] using frame.saved entry he
    · simpa only [Operand.read, memory] using frame.returnAddress
  have copy (offset : Nat) (bound : offset < 2288) (apart : offset < 2160 ∨ 2232 ≤ offset) :
      w.external[frameBase s + BitVec.ofNat 64 offset]? =
        t.external[frameBase s + BitVec.ofNat 64 offset]? := by
    rw [memory]
    apply Eq.trans _ (entered.bytes offset bound)
    apply result.frame
    intro region hr hin
    have cases : region = registerRegion u .rdi 72 ∨ region = Stack.region u 2144 := by simpa using hr
    have bounds := stack_bounds pre.stack
    have pn := base_nat pre (offset := offset) (by omega)
    have on : (u.regValue .rdi).toNat = (stackPtr s).toNat - 2280 + 2160 := by
      rw [out]; exact base_nat pre (by decide)
    have sn : (stackPtr u).toNat = (stackPtr s).toNat - 2304 := by
      rw [entered.frame.rsp]; exact stack_sub_toNat pre.stack (by decide)
    rcases cases with rfl | rfl
    · change (u.regValue .rdi).toNat ≤ _ ∧ _ < (u.regValue .rdi).toNat+72 at hin
      rw [on,pn] at hin; omega
    · have high := hin.2
      rw [stack_region_end] at high
      change (frameBase s + BitVec.ofNat 64 offset).toNat < (stackPtr u).toNat + 8 at high
      rw [pn,sn] at high; omega
  have word (offset : Nat) (bound : offset+8 ≤ 2288)
      (apart : offset+8 ≤ 2160 ∨ 2232 ≤ offset) :
      (Operand.mem (frameBase s + BitVec.ofNat 64 offset) : Operand 64).read w =
        (Operand.mem (frameBase s + BitVec.ofNat 64 offset) : Operand 64).read t := by
    apply memLoad_congr
    intro i hi
    change (w.external[_]?).getD 0 = (t.external[_]?).getD 0
    rw [BitVec.add_assoc, ← BitVec.ofNat_add, copy _ (by omega) (by omega)]
  have r14 : v.regValue .r14 = frameBase s + 2160 :=
    (result.calleeSaved .r14 (by simp)).trans ((entered.registers .r14 (by decide)).trans input.r14)
  refine ⟨w, run2, ⟨finalFrame,
    (word 72 (by decide) (.inl (by decide))).trans input.output,
    (word 80 (by decide) (.inl (by decide))).trans input.secret,
    (word 88 (by decide) (.inl (by decide))).trans input.digest, ?_, ?_, ?_, ?_, ?_⟩, e2.rip⟩
  · rw [out] at generator
    simpa only [Nonce.GeneratorAt, Nonce.DrbgAt, Nat256At, memory] using generator
  · exact (agrees.read (n := 64) (r := 12) (by simp)).trans
      ((result.calleeSaved .r12 (by simp)).trans ((entered.registers .r12 (by decide)).trans input.r12))
  · exact (agrees.read (n := 64) (r := 5) (by simp)).trans
      ((result.calleeSaved .rbp (by simp)).trans ((entered.registers .rbp (by decide)).trans input.rbp))
  · exact (agrees.read (n := 64) (r := 14) (by simp)).trans r14
  · exact (agrees.read (n := 64) (r := 15) (by simp)).trans
      ((result.calleeSaved .r15 (by simp)).trans ((entered.registers .r15 (by decide)).trans input.r15))

end P256.Proofs.Signing.Core.Initialize
