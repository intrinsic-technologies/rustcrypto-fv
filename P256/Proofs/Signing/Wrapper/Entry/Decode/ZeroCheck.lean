import P256.Proofs.Signing.Wrapper.Entry.Decode.EqualCall
import P256.Proofs.Common.Instructions.ByteOps.Effects
import P256.Proofs.Common.Instructions.MovzxByte

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Entry.Decode

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program Prelude
open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.SecretKeyFromBytes.Scalar

structure CopyEntry [Bindings] (initial s : RamState) (secret : ByteArray) : Prop extends
    State initial s 520, Saved initial s where
  rip : s.RIP = 0x1025eb
  value : Nat256At s (stackPtr initial-240) (Arith.uint secret)

theorem check_zero [Bindings] {initial s : RamState} {secret message : ByteArray}
    (context : Context initial secret message) (state : EqualState initial s secret) :
    ∃ t, Advances (returnBoundary initial) 10 s t ∧ CopyEntry initial t secret := by
  obtain ⟨slices,call⟩ := context.call
  have outside := outer_boundary call context.machine context.bindingsSupported
  obtain ⟨a,ha,ra,ea⟩ :=
    (P256.Proofs.Common.Instructions.ByteOps.ByteOps.and_al_imm8_effect_step 0x1025d9 1).advances
      (readyToStep state.machine state.bindingsSupported)
      (programText_slice (programLoaded_codeIn state.loaded) 0x25d9 _
        (by decide) (by decide +kernel)) state.rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x25db (by decide)))
  have fa : AgreesExcept [.reg 0,.flags,.rip] s a := ea.agrees
  have ma := fa.external (by simp [Component.Covers])
  have al : (Operand.reg 0 : Operand 8).read a = 0 := by
    have h := ea.writes
    change a.regValue .rax = mergeGPR 8 ((s.regValue .rax).setWidth 8 &&& 1) (s.regValue .rax) at h
    change (a.regValue .rax).setWidth 8 = _
    rw [h,P256.Proofs.Common.Instructions.ByteOps.ByteOps.mergeGPR_low8,state.status]
    decide +kernel
  obtain ⟨b,hb,rb,eb⟩ :=
    (P256.Proofs.Common.Instructions.MovzxByte.movzx_r32_r8_effect_step 0x1025db 0xf8
      (by decide) (by decide)).advances ra
      (programText_slice ((programLoaded_codeIn state.loaded).of_external_eq ma) 0x25db _
        (by decide) (by decide +kernel)) ea.rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x25de (by decide)))
  have fb : AgreesExcept [.reg 7,.rip] a b := eb.agrees
  have f : AgreesExcept [.reg 0,.reg 7,.flags,.rip] s b := (fa.trans fb).mono (by simp)
  have sb := after_stack call state.toState (ha.trans hb) rb f (by simp) (by simp) (by simp)
  have bdi : b.regValue .rdi = 0 := by
    have h : b.regValue .rdi = ((Operand.reg 0 : Operand 8).read a).setWidth 64 := eb.writes
    rw [h,al]
    decide +kernel
  have mb := f.external (by simp [Component.Covers])
  obtain ⟨u,hu,su,ipu,vu,fu⟩ := choice_call context.call context.bindingsSupported context.machine
    sb 0x25de 0x16a8d (by decide) (by decide +kernel) (by decide +kernel) eb.rip
  have ax : u.regValue .rax = 0 := by
    rw [vu]
    change ((b.regValue .rdi).setWidth 8).setWidth 64 = _
    rw [bdi]
    decide +kernel
  obtain ⟨t,ht,rt,ipt,ft⟩ := zero_status (readyToStep su.machine su.bindingsSupported)
    su.loaded ipu (by change (u.regValue .rax).setWidth 8 = 0; rw [ax]; rfl) outside
  have st := after_stack call su ht rt ft (by simp) (by simp) (by simp)
  have mt := ft.external (by simp [Component.Covers])
  have ag := (f.trans fu).trans ft
  have read (off : Nat) (bound : off ≤ 520) :
      memLoad t.external (stackPtr initial-BitVec.ofNat 64 off) 64 =
        memLoad s.external (stackPtr initial-BitVec.ofNat 64 off) 64 := by
    rw [mt,memLoad_agrees_apart fu (choice_memory context.call bound (by omega)),mb]
  have vb : Nat256At b (stackPtr initial-240) (Arith.uint secret) := by
    simpa only [Nat256At,mb] using state.value
  have value := nat256_preserved vb fu (choice_memory context.call (by decide) (by decide))
  refine ⟨t,((ha.trans hb).trans hu).trans ht,⟨st,?_,ipt,?_⟩⟩
  · refine ⟨?_,?_,?_,?_,?_⟩
    · exact (ag.read (n:=64) (r:=12) (by simp [choiceClobbers])).trans state.pointers
    · exact (ag.read (n:=64) (r:=13) (by simp [choiceClobbers])).trans state.count
    · exact (read 192 (by decide)).trans state.lengths
    · exact (read 208 (by decide)).trans state.output
    · exact (read 200 (by decide)).trans state.capacity
  · simpa only [Nat256At,mt] using value

end P256.Proofs.Signing.Wrapper.Entry.Decode
