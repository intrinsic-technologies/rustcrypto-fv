import P256.Proofs.Nonce.Fill.Tail.Compare.Zero.Prepare
import P256.Proofs.Nonce.Fill.Call
import P256.Proofs.SecretKeyFromBytes.Scalar.Equal.Correct
import P256.Proofs.SecretKeyFromBytes.Scalar.Equal.Representation

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill.Tail.Compare

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Signing.Search
open P256.Proofs.SecretKeyFromBytes.Scalar

variable [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
  {orderAddress : BitVec 64} {original state : Nonce.State}

theorem zero_call_pre (pre : Pre initial boundary orderAddress original)
    (input : ZeroPrepared initial s orderAddress state) (ready : ReadyToStep t)
    (effect : (callEffect (fun _ => 0x119270) 0x1075e5 s).Holds s t) :
    Equal.Pre t boundary := by
  have agrees := effect.agrees
  have sp : stackPtr t = stackPtr initial - 240 := effect.writes.1.trans (call_address input.toFrame)
  have di : t.regValue .rdi = frameBase initial + 72 :=
    (agrees.read (n := 64) (r := 7) (by simp [pushEffect_components])).trans input.rdi
  have dx : t.regValue .rdx = frameBase initial + 8 :=
    (agrees.read (n := 64) (r := 2) (by simp [pushEffect_components])).trans input.rdx
  have grow (a : BitVec 64) (ha : (initial.external[a]?).isSome) :
      (t.external[a]?).isSome := agrees.grow a (input.allocated a ha)
  refine ⟨ready, call_loaded pre input.toFrame effect, effect.rip,
    (agrees.read (n := 64) (r := 6) (by simp [pushEffect_components])).trans input.rsi,
    (agrees.read (n := 64) (r := 1) (by simp [pushEffect_components])).trans input.rcx,
    ?_, ?_, ?_, pre.outerBoundary, ?_⟩
  · rw [di]
    have address : frameBase initial + 72 = stackPtr initial - 160 := frameBase_add initial (offset := 72) (by decide)
    rw [address]
    exact readable_of_grow (stack_sub_readable pre.stack (by decide) (by decide)) grow
  · rw [dx]
    have address : frameBase initial + 8 = stackPtr initial - 224 := frameBase_add initial (offset := 8) (by decide)
    rw [address]
    exact readable_of_grow (stack_sub_readable pre.stack (by decide) (by decide)) grow
  · rw [sp]
    exact readable_of_grow (stack_sub_readable pre.stack (by decide) (by decide)) grow
  · change InProgram (stackTop t)
    rw [(callEffect_stack effect).1]
    exact inProgram_of_textOffset 0x75e5 (by decide)

theorem zero_call_nat256 {target : RamState → BitVec 64} {ret : BitVec 64}
    (input : Frame initial s) (effect : (callEffect target ret s).Holds s t)
    {off value : Nat} (bound : off + 32 ≤ 232)
    (integer : Nat256At s (frameBase initial + BitVec.ofNat 64 off) value) :
    Nat256At t (frameBase initial + BitVec.ofNat 64 off) value := by
  refine ⟨integer.1, ?_⟩
  intro i hi
  apply Eq.trans _ (integer.2 i hi)
  rw [frameBase_add initial (by omega)]
  exact ScalarFrame.call_byte (frameOffset := 232) (by decide) input.rsp effect
    (offset := 232-off) (len := 32) (by omega) (by omega) hi

end P256.Proofs.Nonce.Fill.Tail.Compare
