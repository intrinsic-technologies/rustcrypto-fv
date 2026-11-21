import P256.Proofs.Verifying.Combination.Naf.Interface
import P256.Proofs.Verifying.Combination.Naf.Machine.Entry
import P256.Proofs.Verifying.Combination.Naf.Machine.IteratorCall

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Machine

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar

structure Initialized [Bindings] (s t : RamState) (n : Nat) : Prop extends FrameState s t where
  rip : t.RIP = 0x10f38a
  r12 : t.regValue .r12 = 5
  r13 : t.regValue .r13 = 256
  r15 : t.regValue .r15 = 257
  rbx : t.regValue .rbx = 32
  outputPointer : memLoad t.external (stackPtr s-120) 64 = s.regValue .rdi
  iterator : Iterator.StateAt t (stackPtr s-88) (s.regValue .rdx) n 0

theorem initialize_correct [Bindings] {s : RamState} {boundary : ReturnBoundary} {n : Nat}
    (pre : Pre s boundary) (input : Nat256At s (s.regValue .rdx) n)
    (zeroes : Bytes s.external (s.regValue .rdi) 257 (fun _ => 0)) :
    ∃ fuel t, Advances boundary fuel s t ∧ Initialized s t n ∧
      Nat256At t (s.regValue .rdx) n ∧ Bytes t.external (s.regValue .rdi) 257 (fun _ => 0) := by
  obtain ⟨fuel0, u, run0, state, frame0⟩ := entry pre
  obtain ⟨v, run1, ready1, raw⟩ := direct_call pre.toCalleePre state.toFrameState 0xf385 0x8f06
    (by decide) (by decide +kernel) (by decide +kernel)
    (inProgram_of_textOffset 0x18290 (by decide)) state.rip
  have effect : (callEffect (fun _ => 0x118290) 0x10f38a u).Holds u v := raw
  have sv := FrameState.after_call pre.toCalleePre state.toFrameState ready1 effect
  have src : v.regValue .rsi = s.regValue .rdx :=
    (effect.agrees.read (n := 64) (r := 6) (by simp)).trans state.rsi
  have dst : v.regValue .rdi = stackPtr s-88 :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans state.rdi
  have ret : (returnBoundary v).rip = 0x10f38a := (callEffect_stack effect).1
  have cp : CalleePre v boundary 0x118290 32 40 24 := by
    apply iterator_pre pre sv effect.rip dst
    · change (⟨(v.regValue .rsi).toNat, 32⟩ : MemoryRegion).Bounded
      rw [src]
      exact pre.sourceBounded
    · intro a ha
      change (v.regValue .rsi).toNat ≤ a.toNat ∧ a.toNat < (v.regValue .rsi).toNat+32 at ha
      rw [src] at ha
      exact Option.isSome_iff_exists.mp (sv.allocated a
        (Option.isSome_iff_exists.mpr (pre.sourceAllocated a ha)))
    · change (⟨(v.regValue .rsi).toNat, 32⟩ : MemoryRegion).Disjoint (Stack.region s 168)
      rw [src]
      exact pre.sourceStack
    · rw [ret]
      exact inProgram_of_textOffset 0xf38a (by decide)
  have sourceV := source_preserved pre sv input
  have inputV : Nat256At v (v.regValue .rsi) n := by rw [src]; exact sourceV
  have len : v.regValue .rdx = 32 :=
    (effect.agrees.read (n := 64) (r := 2) (by simp)).trans state.rdx
  obtain ⟨t, result, iterator, _, inputT⟩ := Iterator.initialize_correct cp (by decide) len inputV
  have st := FrameState.after_iterator pre sv result dst
  rw [dst, src] at iterator
  rw [src] at inputT
  have registers (r : Syntax.Reg) (hr : r ∈ [Syntax.Reg.rbx, .rbp, .r12, .r13, .r14, .r15]) :
      t.regValue r = u.regValue r := by
    apply (result.calleeSaved r hr).trans
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact effect.agrees.read (n := 64) (r := 3) (by simp)
    · exact effect.agrees.read (n := 64) (r := 5) (by simp)
    · exact effect.agrees.read (n := 64) (r := 12) (by simp)
    · exact effect.agrees.read (n := 64) (r := 13) (by simp)
    · exact effect.agrees.read (n := 64) (r := 14) (by simp)
    · exact effect.agrees.read (n := 64) (r := 15) (by simp)
  have outputPointer : memLoad t.external (stackPtr s-120) 64 = s.regValue .rdi := by
    change memLoad t.external (stackPtr s-BitVec.ofNat 64 120) 64 = _
    rw [iterator_result_read pre sv result dst (by decide) (by decide) (by decide)]
    exact (call_read state.toFrameState effect (offset := 120) (n := 64)
      (by decide) (by decide)).trans state.outputPointer
  have frame1 := effect.agrees.memoryWriteFrame (call_writes pre.toCalleePre state.toFrameState)
  have frame2 := iterator_result_stack pre sv result dst
  have frame := memoryWriteFrame_trans (memoryWriteFrame_trans frame0 frame1) frame2
  obtain ⟨fuel2, run2⟩ := result.execution
  refine ⟨fuel0+1+fuel2, t, (run0.trans run1).trans run2,
    ⟨st, result.rip.trans ret, (registers .r12 (by simp)).trans state.r12,
      (registers .r13 (by simp)).trans state.r13, (registers .r15 (by simp)).trans state.r15,
      (registers .rbx (by simp)).trans state.rbx, outputPointer, iterator⟩, inputT, ?_⟩
  intro i hi
  rw [frame _]
  · exact zeroes i hi
  · intro region hr hin
    have eq : region = Stack.region s 168 := by simpa using hr
    subst region
    exact pre.separation (1 : Fin 3) (2 : Fin 3) (by decide) _
      (memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) hi) hin

end P256.Proofs.Verifying.Combination.Naf.Machine
