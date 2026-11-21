import P256.Proofs.Verifying.Core.Digest.Finish.Copy
import P256.Proofs.Verifying.Core.Digest.Finish.Arguments
import P256.Proofs.Verifying.Core.Digest.Finish.Reduce

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Digest.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame
open SecretKeyFromBytes.Scalar

theorem finish [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x r scalarS : Nat}
    (pre : Core.Pre s boundary) (state : Frame s t) (rip : t.RIP = 0x10dc30)
    (pointers : Prepare.Pointers s t) (input : Nat256At t (frameBase s) x)
    (savedR : Nat256At t (frameBase s+704) r)
    (savedS : Nat256At t (frameBase s+736) scalarS) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x10dc78 ∧
      Prepare.Pointers s u ∧ Nat256At u (frameBase s+968) (x % Operations.domain.n) ∧
      Nat256At u (frameBase s+704) r ∧ Nat256At u (frameBase s+736) scalarS ∧
      MemoryWriteFrame t u (prefixRegions s) := by
  obtain ⟨n,a,runA,stateA,copyEffect,inputA,_⟩ := copy pre state 0xdc30
    (by decide) (by decide +kernel) rip input
  have memoryA := copyEffect.agrees.memoryWriteFrame (show WritesWithin
      (CopyBlock.effect (Extracted.textAddress+0xdc30) t).components (prefixRegions s) from by
    intro c hc addr covered
    simp only [CopyBlock.effect,Effect.components,List.map_cons,List.map_nil,
      Write.component_reg,Write.component_mem,List.cons_append,List.nil_append,
      List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals try exact covered.elim
    all_goals exact prefix_local_contains pre state (by decide) covered)
  have ptrA := pointers.after copyEffect.agrees (by simp [CopyBlock.effect,Effect.components])
  have rA := copy_slot (offset := 704) state.rsp copyEffect (by decide) (by decide) savedR
  have sA := copy_slot (offset := 736) state.rsp copyEffect (by decide) (by decide) savedS
  obtain ⟨m,b,runB,stateB,args⟩ := arguments pre stateA copyEffect.rip
  have memoryB : b.external = a.external := args.agrees.external (by
    simp [argumentEffect,Effect.components,Component.Covers])
  have ptrB := ptrA.after args.agrees (by simp [argumentEffect,Effect.components])
  have inputB : Nat256At b (frameBase s+128) x := by
    exact ⟨inputA.1,fun i hi => by rw [memoryB]; exact inputA.2 i hi⟩
  have rB : Nat256At b (frameBase s+704) r :=
    ⟨rA.1,fun i hi => by rw [memoryB]; exact rA.2 i hi⟩
  have sB : Nat256At b (frameBase s+736) scalarS :=
    ⟨sA.1,fun i hi => by rw [memoryB]; exact sA.2 i hi⟩
  have si : b.regValue .rsi = frameBase s+128 :=
    args.writes.2.trans (congrArg (·+128) stateA.rsp)
  have di : b.regValue .rdi = frameBase s+968 :=
    args.writes.1.trans (congrArg (·+968) stateA.rsp)
  obtain ⟨k,u,runC,stateU,ripU,ptrU,value,bytes,memoryC⟩ :=
    reduce_call pre stateB args.rip si di ptrB inputB
  have preserved {off y : Nat} (lo : 160 ≤ off) (hi : off+32 ≤ 968)
      (val : Nat256At b (frameBase s+BitVec.ofNat 64 off) y) :
      Nat256At u (frameBase s+BitVec.ofNat 64 off) y := by
    have addr : frameBase s+BitVec.ofNat 64 off = stackPtr s-BitVec.ofNat 64 (1176-off) := by
      simpa only [stateB.rsp,frameBase] using
        scalar_stack_address (frameOffset := 1176) stateB.rsp (offset := off)
          (by decide) (by omega)
    rw [addr] at val ⊢
    exact ⟨val.1,fun i hi' => (bytes (1176-off) 32 (by omega) (by omega)
      (.inr (by omega)) i hi').trans (val.2 i hi')⟩
  refine ⟨n+m+k,u,(runA.trans runB).trans runC,stateU,ripU,ptrU,value,
    preserved (off := 704) (by decide) (by decide) rB,
    preserved (off := 736) (by decide) (by decide) sB,?_⟩
  apply memoryWriteFrame_trans memoryA
  apply memoryWriteFrame_trans (t := b)
  · intro addr _
    rw [memoryB]
  · exact memoryC

end P256.Proofs.Verifying.Core.Digest.Finish
