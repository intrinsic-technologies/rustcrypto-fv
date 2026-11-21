import P256.Proofs.Signing.Core.Iteration.Call
import P256.Proofs.Signing.Core.Iteration.Components.Callees

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Components

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open SecretKeyFromBytes.Scalar (Nat256At)

theorem constructor_call [Bindings] {s t : RamState} {boundary : ReturnBoundary} {r scalarS : Nat}
    (constructor : ConstructorContract) (hr : r < Operations.domain.n)
    (hs : scalarS < Operations.domain.n)
    (hp : SignPre s boundary) (frame : Frame s t) (rip : t.RIP = 0x10d339)
    (source : t.regValue .rsi = frameBase s+1328)
    (right : t.regValue .rdx = frameBase s+2096)
    (destination : t.regValue .rdi = frameBase s+528)
    (first : Nat256At t (frameBase s+1328) r)
    (second : Nat256At t (frameBase s+2096) scalarS) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x10d33e ∧
      ConstructorResult u (frameBase s+528) r scalarS ∧
      (∀ offset < 2280, offset < 528 ∨ 600 ≤ offset →
        u.external[frameBase s+BitVec.ofNat 64 offset]? =
          t.external[frameBase s+BitVec.ofNat 64 offset]?) ∧
      (∀ reg ∈ [Syntax.Reg.rbx,.rbp,.r12,.r13,.r14,.r15],
        u.regValue reg = t.regValue reg) := by
  obtain ⟨a,callRun,readyA,call⟩ := ScalarFrame.scalar_call hp.toCalleePre
    (by decide) (by decide) (NextNonce.scalarFrame frame) 0xd339 0xffffc552
    (by decide) (by decide +kernel) (by decide +kernel)
    (inProgram_of_textOffset 0x9890 (by decide)) rip
  have cp := local_call_pre hp frame readyA call
    (inputBytes := 32) (outputBytes := 72) (reserve := 512)
    (inProgram_of_textOffset 0xd33e (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (.inr (by decide)) source destination
  have called := (NextNonce.scalarFrame frame).after_call hp.toCalleePre
    (by decide) (by decide) readyA call
  have src : a.regValue .rsi = frameBase s+1328 :=
    (call.agrees.read (n := 64) (r := 6) (by simp)).trans source
  have rhs : a.regValue .rdx = frameBase s+2096 :=
    (call.agrees.read (n := 64) (r := 2) (by simp)).trans right
  have dst : a.regValue .rdi = frameBase s+528 :=
    (call.agrees.read (n := 64) (r := 7) (by simp)).trans destination
  have bounds := stack_bounds hp.stack
  have sp : (stackPtr a).toNat = (stackPtr s).toNat-2288 := by
    rw [called.rsp]
    exact stack_sub_toNat hp.stack (by decide)
  have rn : (a.regValue .rdx).toNat = (stackPtr s).toNat-2280+2096 := by
    rw [rhs]
    exact NextNonce.base_nat hp (by decide)
  have dn : (a.regValue .rdi).toNat = (stackPtr s).toNat-2280+528 := by
    rw [dst]
    exact NextNonce.base_nat hp (by decide)
  have constructorPre : ConstructorPre a boundary := by
    refine ⟨cp,?_,?_,?_,?_⟩
    · change (a.regValue .rdx).toNat+32 < 2^32
      rw [rn]
      omega
    · intro address ha
      change (a.regValue .rdx).toNat ≤ address.toNat ∧
        address.toNat < (a.regValue .rdx).toNat+32 at ha
      rw [rn] at ha
      apply Option.isSome_iff_exists.mp
      apply called.allocated
      apply Option.isSome_iff_exists.mpr
      apply hp.stack.2.1 address
      change (stackPtr s).toNat-4584 ≤ address.toNat ∧
        address.toNat < (Stack.region s 4584).start+(Stack.region s 4584).size
      rw [stack_region_end]
      constructor <;> omega
    · intro address ha hb
      change (a.regValue .rdx).toNat ≤ address ∧ address < (a.regValue .rdx).toNat+32 at ha
      change (a.regValue .rdi).toNat ≤ address ∧ address < (a.regValue .rdi).toNat+72 at hb
      rw [rn] at ha
      rw [dn] at hb
      omega
    · intro address ha hb
      change (a.regValue .rdx).toNat ≤ address ∧ address < (a.regValue .rdx).toNat+32 at ha
      change (Stack.region a 512).start ≤ address ∧
        address < (Stack.region a 512).start+(Stack.region a 512).size at hb
      rw [stack_region_end] at hb
      change _ ∧ address < (stackPtr a).toNat+8 at hb
      rw [sp] at hb
      rw [rn] at ha
      omega
  have firstA : Nat256At a (a.regValue .rsi) r := by
    rw [src]
    exact ⟨first.1,fun i hi =>
      (local_call_copy frame call (by decide) i hi).trans (first.2 i hi)⟩
  have secondA : Nat256At a (a.regValue .rdx) scalarS := by
    rw [rhs]
    exact ⟨second.1,fun i hi =>
      (local_call_copy frame call (by decide) i hi).trans (second.2 i hi)⟩
  obtain ⟨u,result,value⟩ := constructor constructorPre firstA secondA hr hs
  obtain ⟨n,run⟩ := result.execution
  refine ⟨1+n,u,callRun.trans run,
    after_call hp frame readyA call result (by decide) (by decide) destination,
    result.rip.trans (callEffect_stack call).1,dst ▸ value,?_,?_⟩
  · intro offset bound apart
    have h := local_result_copy (output := 528) hp frame call result destination
      (offset := offset) (len := 1) (by omega) (by decide) (by omega) 0 (by decide)
    simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_zero] using h
  · intro reg hr
    refine (result.calleeSaved reg hr).trans ?_
    rcases (show reg = .rbx ∨ reg = .rbp ∨ reg = .r12 ∨ reg = .r13 ∨ reg = .r14 ∨ reg = .r15
      from by simpa using hr) with rfl|rfl|rfl|rfl|rfl|rfl
    · exact call.agrees.read (n := 64) (r := 3) (by simp)
    · exact call.agrees.read (n := 64) (r := 5) (by simp)
    · exact call.agrees.read (n := 64) (r := 12) (by simp)
    · exact call.agrees.read (n := 64) (r := 13) (by simp)
    · exact call.agrees.read (n := 64) (r := 14) (by simp)
    · exact call.agrees.read (n := 64) (r := 15) (by simp)

end P256.Proofs.Signing.Core.Iteration.Components
