import P256.Proofs.Signing.Core.Iteration.Point.Normalize.Finish.Packed
import P256.Proofs.Signing.Core.Iteration.Point.Normalize.Finish.Movsq
import P256.Proofs.Signing.Core.Iteration.Point.Normalize.Finish.Blocks.B101379

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Point.Normalize.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.Program
open NextNonce (scalarFrame coreFrame base_add)
open Projective.Multiply.Machine.Basepoint (register_block)
open P256.Proofs.Signing.Core.Iteration.Point.Normalize.Finish.Blocks

theorem saved [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x y : Nat}
    (pre : SignPre s boundary) (state : Payload s t x y 1328) (rip : t.RIP = 0x10d09d) :
    ∃ fuel u, Advances boundary fuel t u ∧ u.RIP = 0x10d0ab ∧
      Payload s u x y 528 ∧ Preserved s t u := by
  obtain ⟨n,v,run,sf,ef,mem⟩ := register_block (offset := 0xd09d)
    (scalarFrame state.frame) (b101379_correct boundary pre.outerBoundary)
    (by decide +kernel) (by decide +kernel) rip
    (by simp [b101379Effect,Effect.components,Component.Covers])
    (by simp [b101379Effect,Effect.components]) (by simp [b101379Effect,Effect.components])
    (by simp [b101379Effect,Effect.components]) (by simp [b101379Effect,Effect.components])
  have f := coreFrame sf
  have dst : v.regValue .rdi = frameBase s+528 := ef.writes.2.1.trans state.registers.rbp
  have src : v.regValue .rsi = frameBase s+1328 := ef.writes.2.2.trans state.registers.r15
  obtain ⟨u,run1,fu,ip,bytes,ag⟩ := movsq72 pre.toCalleePre sf 0xd0a8 528
    (by decide) (by decide) (by decide +kernel) ef.rip
    (by rw [dst,f.rsp]; rfl) ef.writes.1
    (by rw [src]; exact local_readable pre f (by decide))
    (by rw [src,dst,show frameBase s+1328 = stackPtr s-952 from base_add s (by decide),
          show frameBase s+528 = stackPtr s-1752 from base_add s (by decide),
          show (stackPtr s-952).toNat = (stackPtr s).toNat-952 from stack_sub_toNat pre.stack (by decide),
          show (stackPtr s-1752).toNat = (stackPtr s).toNat-1752 from stack_sub_toNat pre.stack (by decide)]
        have := stack_bounds pre.stack
        omega)
  rw [src,dst] at bytes
  rw [dst] at ag
  have regs := state.registers.preserve (ef.agrees.trans ag) (by
    intro r hr; simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl|rfl|rfl|rfl|rfl <;> simp [b101379Effect,Effect.components])
  refine ⟨n+9,u,run.trans run1,ip,⟨coreFrame fu,regs,state.point.of_bytes_eq ?_⟩,?_⟩
  · intro i hi
    simpa only [mem,BitVec.ofNat_eq_ofNat] using bytes i (by omega)
  · intro i hi
    have h := region_byte ag (s := s) (offset := 528) (len := 72)
      (by intro c hc a ha; simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
          rcases hc with rfl|rfl|rfl|rfl|rfl <;> try exact ha.elim
          exact ha) (by decide) (i := i) (by rcases hi with h|h|h|h <;> omega)
      (by rcases hi with h|h|h|h <;> omega)
    simpa only [mem] using h

end P256.Proofs.Signing.Core.Iteration.Point.Normalize.Finish
