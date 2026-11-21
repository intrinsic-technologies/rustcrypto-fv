import P256.Proofs.Ecdh.Initial.Prefix.Block
import P256.Proofs.Ecdh.Initial.Prefix.Constants

set_option autoImplicit false

namespace P256.Proofs.Ecdh.Initial.Prefix

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame

theorem prepare_pre [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Ecdh.Pre s boundary) (state : Ecdh.Frame s t)
    (rip : t.RIP = 0x100011) (peer : t.regValue .rdx = s.regValue .rdx) : Block.Pre t := by
  have address (c : Nat) (hc : c ≤ 2056) :
      rspOf t+BitVec.ofNat 64 c = stackPtr s-BitVec.ofNat 64 (2056-c) :=
    scalar_stack_address state.rsp (by decide) hc
  have bounds (c : Nat) (hc : c ∈ ([8,248,256,264,272,280,288,296,304,312,320,328,336] : List Nat)) :
      c ≤ 336 ∧ c%8 = 0 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  refine ⟨rip,?_,?_,?_,?_,?_,?_⟩
  · intro k hk
    rw [peer]
    exact peer_readable pre state (by omega)
  · intro k hk
    exact one_readable state.loaded hk
  · intro c hc
    have h := bounds c hc
    rw [address c (by omega)]
    exact writable_of_grow (stack_sub_writable8 pre.stack
      (fun a ha hp => pre.avoids _ (by simp) a ha (.inr hp)) (by omega) (by omega)) state.allocated
  · intro c hc offset len hcode
    have h := bounds c hc
    have code := stack_code (frameOffset := 2056) pre.toCalleePre state (offset := c) (len := 8)
      (codeOffset := 0x11+offset) (codeLen := len) (by decide) (by omega) (by omega)
    simp only [BitVec.ofNat_add,←BitVec.add_assoc,Extracted.textAddress,BitVec.reduceAdd] at code
    exact code
  · intro c hc j hj i hi k hk eq
    have h := bounds c hc
    rw [address c (by omega),peer,BitVec.add_assoc,←BitVec.ofNat_add] at eq
    apply pre.peerStack (s.regValue .rdx+BitVec.ofNat 64 (8*j+k)).toNat
      (memoryRegion_contains_add pre.peerBounded (Nat.le_refl _) (Nat.le_refl _) (by omega : 8*j+k < 72))
    rw [←eq]
    exact stack_contains pre.toCalleePre (by omega) (by omega) ⟨i,hi,rfl⟩
  · intro c hc j hj i hi k hk eq
    have h := bounds c hc
    rw [address c (by omega),BitVec.add_assoc,←BitVec.ofNat_add] at eq
    apply pre.avoids (Stack.region s 3464) (by simp) _
      (stack_contains pre.toCalleePre (offset := 2056-c) (len := 8) (by omega) (by omega) ⟨i,hi,rfl⟩) (.inl ?_)
    rw [eq]
    exact one_byte (by omega)

end P256.Proofs.Ecdh.Initial.Prefix
