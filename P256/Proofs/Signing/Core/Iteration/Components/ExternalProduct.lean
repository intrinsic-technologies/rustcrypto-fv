import P256.Proofs.Signing.Core.Iteration.Call
import P256.Proofs.Scalar.Multiply

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Components

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open SecretKeyFromBytes.Scalar (Nat256At)

theorem secret_copy [Bindings] {s t : RamState} {boundary : ReturnBoundary} {secret : Nat}
    (hp : SignPre s boundary)
    (memory : MemoryWriteFrame s t #v[registerRegion s .rdi 65,Stack.region s 4584])
    (input : Nat256At s (s.regValue .rsi) secret) :
    Nat256At t (s.regValue .rsi) secret := by
  refine ⟨input.1,fun i hi => ?_⟩
  rw [memory]
  · exact input.2 i hi
  · intro region hr hin
    have contains : (registerRegion s .rsi 32).Contains
        (s.regValue .rsi+BitVec.ofNat 64 i).toNat :=
      memoryRegion_contains_add hp.inputBounded (Nat.le_refl _) (Nat.le_refl _) hi
    rcases (show region = registerRegion s .rdi 65 ∨ region = Stack.region s 4584
      from by simpa using hr) with rfl|rfl
    · exact hp.separation 0 1 (by decide) _ contains hin
    · exact hp.separation 0 2 (by decide) _ contains hin

theorem external_product [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x secret : Nat}
    (hp : SignPre s boundary) (frame : Frame s t) (rip : t.RIP = 0x10d2bd)
    (source : t.regValue .rsi = frameBase s+528)
    (right : t.regValue .rdx = s.regValue .rsi)
    (destination : t.regValue .rdi = frameBase s+1328)
    (left : Nat256At t (frameBase s+528) x)
    (original : Nat256At s (s.regValue .rsi) secret) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x10d2c2 ∧
      Nat256At u (frameBase s+1328) (x*secret % Operations.domain.n) ∧
      (∀ offset < 2280, offset < 1328 ∨ 1360 ≤ offset →
        u.external[frameBase s+BitVec.ofNat 64 offset]? =
          t.external[frameBase s+BitVec.ofNat 64 offset]?) ∧
      (∀ reg ∈ [Syntax.Reg.rbx,.rbp,.r12,.r13,.r14,.r15],
        u.regValue reg = t.regValue reg) := by
  obtain ⟨a,callRun,readyA,call⟩ := ScalarFrame.scalar_call hp.toCalleePre
    (by decide) (by decide) (NextNonce.scalarFrame frame) 0xd2bd 0x5d7e
    (by decide) (by decide +kernel) (by decide +kernel)
    (inProgram_of_textOffset 0x13040 (by decide)) rip
  have cp := local_call_pre hp frame readyA call
    (inputBytes := 32) (outputBytes := 32) (reserve := 280)
    (inProgram_of_textOffset 0xd2c2 (by decide)) (by decide) (by decide) (by decide)
    (by decide) (by decide) (.inl (by decide)) source destination
  have called := (NextNonce.scalarFrame frame).after_call hp.toCalleePre
    (by decide) (by decide) readyA call
  have src : a.regValue .rsi = frameBase s+528 :=
    (call.agrees.read (n := 64) (r := 6) (by simp)).trans source
  have rhs : a.regValue .rdx = s.regValue .rsi :=
    (call.agrees.read (n := 64) (r := 2) (by simp)).trans right
  have dst : a.regValue .rdi = frameBase s+1328 :=
    (call.agrees.read (n := 64) (r := 7) (by simp)).trans destination
  have region : registerRegion a .rdx 32 = registerRegion s .rsi 32 := by
    simp only [registerRegion,rhs]
  have bounds := stack_bounds hp.stack
  have sp : (stackPtr a).toNat = (stackPtr s).toNat-2288 := by
    rw [called.rsp]
    exact stack_sub_toNat hp.stack (by decide)
  have dn : (a.regValue .rdi).toNat = (stackPtr s).toNat-2280+1328 := by
    rw [dst]
    exact NextNonce.base_nat hp (by decide)
  have binary : Scalar.Multiply.MultiplyPre a boundary := by
    refine ⟨cp,?_,?_,?_,?_⟩
    · rw [region]
      exact hp.inputBounded
    · rw [region]
      intro address ha
      exact Option.isSome_iff_exists.mp (called.allocated address
        (Option.isSome_iff_exists.mpr (hp.inputAllocated address ha)))
    · rw [region]
      intro address ha hb
      apply hp.separation 0 2 (by decide) address ha
      change (a.regValue .rdi).toNat ≤ address ∧ address < (a.regValue .rdi).toNat+32 at hb
      rw [dn] at hb
      change (stackPtr s).toNat-4584 ≤ address ∧
        address < (Stack.region s 4584).start+(Stack.region s 4584).size
      rw [stack_region_end]
      constructor <;> omega
    · rw [region]
      intro address ha hb
      apply hp.separation 0 2 (by decide) address ha
      change (stackPtr a).toNat-280 ≤ address ∧
        address < (Stack.region a 280).start+(Stack.region a 280).size at hb
      rw [stack_region_end] at hb
      change _ ∧ address < (stackPtr a).toNat+8 at hb
      rw [sp] at hb
      change (stackPtr s).toNat-4584 ≤ address ∧
        address < (Stack.region s 4584).start+(Stack.region s 4584).size
      rw [stack_region_end]
      constructor <;> omega
  have leftA : Nat256At a (a.regValue .rsi) x := by
    rw [src]
    exact ⟨left.1,fun i hi =>
      (local_call_copy frame call (by decide) i hi).trans (left.2 i hi)⟩
  have rightA : Nat256At a (a.regValue .rdx) secret := by
    rw [rhs]
    exact secret_copy hp called.frame original
  obtain ⟨u,result,value⟩ := Scalar.Multiply.multiply_correct binary leftA rightA
  obtain ⟨n,run⟩ := result.execution
  refine ⟨1+n,u,callRun.trans run,
    after_call hp frame readyA call result (by decide) (by decide) destination,
    result.rip.trans (callEffect_stack call).1,dst ▸ value,?_,?_⟩
  · intro offset bound apart
    have h := local_result_copy (output := 1328) hp frame call result destination
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
