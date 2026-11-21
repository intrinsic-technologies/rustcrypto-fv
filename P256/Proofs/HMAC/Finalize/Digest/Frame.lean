import P256.Proofs.HMAC.Finalize.Digest.Outer
import P256.Proofs.HMAC.Finalize.Frame

set_option autoImplicit false

namespace P256.Proofs.HMAC.Finalize.Digest

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Program.ScalarFrame (workRegion)
open P256.Proofs.Common

theorem pre [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    (call : HashCalleePre initial boundary 0x100f10 168 672)
    (state : ScalarFrame.FrameState initial s 0 672 328) (rip : s.RIP = 0x101111) :
    DigestPre s := by
  refine ⟨rip, ?_, ?_, ?_⟩
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact ScalarFrame.stack_readable (stackPre call) state (by decide) (by decide)
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact ScalarFrame.stack_writable (stackPre call) state (by decide) (by decide) (by decide)
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact ScalarFrame.stack_code (stackPre call) state (by decide) (by decide) (codeOffset := 0x1111) (by decide)

theorem Outer.pre [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    (call : HashCalleePre initial boundary 0x100f10 168 672)
    (state : ScalarFrame.FrameState initial s 0 672 328)
    (pointer : s.regValue .rbx = initial.regValue .rsi) (rip : s.RIP = 0x1013af) :
    Outer.Pre s := by
  refine ⟨rip, ?_, ?_, ?_⟩
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact ScalarFrame.stack_readable (stackPre call) state (by decide) (by decide)
  · intro i hi
    change Instructions.CrossPageStore.Writable s (s.regValue .rbx + i) 4
    rw [pointer]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact Finalize.output_writable call state (by decide) (by decide)
  · intro i hi
    change RangeApart (s.regValue .rbx + i) 4 0x1013af 104
    rw [pointer]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact Finalize.output_code call (by decide) (pc := 0x13af) (by decide)

def components (destination : BitVec 64) : List Component :=
  [.reg 0, .reg 1, .reg 2, .reg 6, .reg 7, .reg 8, .reg 9, .reg 10,
    .mem destination 32, .rip]

theorem serializeEffect_agrees {s t : RamState} {next destination : BitVec 64}
    (h : (serializeEffect next destination s).Holds s t) :
    AgreesExcept (components destination) s t := by
  apply h.agrees.widen
  · intro c hc hm
    simp only [serializeEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
    all_goals try simp [Component.isMem] at hm
    all_goals simp [components]
  · intro a c hc covered
    simp only [serializeEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
    all_goals try exact covered.elim
    all_goals obtain ⟨i, hi, rfl⟩ := covered
    · refine ⟨.mem destination 32, by simp [components], 0 + i, by omega, ?_⟩
      rw [BitVec.ofNat_add, BitVec.add_assoc]
      rfl
    · refine ⟨.mem destination 32, by simp [components], 4 + i, by omega, ?_⟩
      rw [BitVec.ofNat_add, BitVec.add_assoc]
      rfl
    · refine ⟨.mem destination 32, by simp [components], 8 + i, by omega, ?_⟩
      rw [BitVec.ofNat_add, BitVec.add_assoc]
      rfl
    · refine ⟨.mem destination 32, by simp [components], 12 + i, by omega, ?_⟩
      rw [BitVec.ofNat_add, BitVec.add_assoc]
      rfl
    · refine ⟨.mem destination 32, by simp [components], 16 + i, by omega, ?_⟩
      rw [BitVec.ofNat_add, BitVec.add_assoc]
      rfl
    · refine ⟨.mem destination 32, by simp [components], 20 + i, by omega, ?_⟩
      rw [BitVec.ofNat_add, BitVec.add_assoc]
      rfl
    · refine ⟨.mem destination 32, by simp [components], 24 + i, by omega, ?_⟩
      rw [BitVec.ofNat_add, BitVec.add_assoc]
      rfl
    · refine ⟨.mem destination 32, by simp [components], 28 + i, by omega, ?_⟩
      rw [BitVec.ofNat_add, BitVec.add_assoc]
      rfl

theorem frame [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
    (call : HashCalleePre initial boundary 0x100f10 168 672)
    (state : ScalarFrame.FrameState initial s 0 672 328) (ready : ReadyToStep t)
    (h : (effect s).Holds s t) : ScalarFrame.FrameState initial t 0 672 328 := by
  apply state.after_effect (stackPre call) (by decide) ready (serializeEffect_agrees h) ?_ (by simp [components])
  intro c hc a covered
  simp only [components, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals try exact covered.elim
  exact ⟨workRegion initial 672, by simp,
    Finalize.local_work_contains call state.rsp (by decide) covered⟩

theorem Outer.frame [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
    (call : HashCalleePre initial boundary 0x100f10 168 672)
    (state : ScalarFrame.FrameState initial s 0 672 328)
    (pointer : s.regValue .rbx = initial.regValue .rsi) (ready : ReadyToStep t)
    (h : (Outer.effect s).Holds s t) : ScalarFrame.FrameState initial t 32 672 328 .rsi := by
  have ag := serializeEffect_agrees h
  have memory : MemoryWriteFrame s t #v[registerRegion initial .rsi 32] := by
    apply ag.memoryWriteFrame
    intro c hc a covered
    simp only [components,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact covered.elim
    change (Component.mem (s.regValue .rbx) 32).Covers a at covered
    rw [pointer] at covered
    exact ⟨_,by simp, Finalize.output_contains call (offset := 0) (len := 32) (by decide)
      (by simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_zero] using covered)⟩
  have total : MemoryWriteFrame initial t
      #v[registerRegion initial .rsi 32, Stack.region initial 672] := by
    intro a ha
    have hm := memory a (by
      intro region hr
      have eq : region = registerRegion initial .rsi 32 := by simpa using hr
      rw [eq]
      exact ha _ (by simp))
    rw [hm]
    apply state.frame
    intro region hr hin
    have eq : region = registerRegion initial .rdi 0 ∨ region = Stack.region initial 672 := by simpa using hr
    rcases eq with rfl | rfl
    · change _ ≤ _ ∧ _ < _ + 0 at hin; omega
    · exact ha _ (by simp) hin
  have savedRead {offset : Nat} (ho : offset ≤ 48) :
      memLoad t.external (stackPtr initial - BitVec.ofNat 64 offset) 64 =
      memLoad s.external (stackPtr initial - BitVec.ofNat 64 offset) 64 := by
    apply memLoad_congr
    intro i hi
    change (t.external[_]?).getD 0 = (s.external[_]?).getD 0
    rw [memory _]
    intro region hr hin
    have eq : region = registerRegion initial .rsi 32 := by simpa using hr
    subst region
    exact call.separation 0 2 (by decide) _ hin
      (ScalarFrame.stack_contains call.toCalleePre (by omega) (by omega) ⟨i,hi,rfl⟩)
  refine ⟨bindingsSupported_of_ready_agrees state.bindingsSupported ready ag,
    supportedMachine_of_ready_agrees state.machine ready ag, ?_,
    ag.directionFlagClear (by simp [components]) state.directionFlag,
    fun a ha => ag.grow a (state.allocated a ha), total,
    (ag.read (n := 64) (r := 4) (by simp [components])).trans state.rsp, ?_, ?_,
    (ag.mxcsr (by simp [components])).trans state.mxcsr,
    (ag.fcw (by simp [components])).trans state.fp87⟩
  · intro a b hb
    rw [memory a]
    · exact state.loaded a b hb
    · intro region hr hin
      have eq : region = registerRegion initial .rsi 32 := by simpa using hr
      subst region
      exact call.digestAvoids a hin (.inl ⟨b,hb⟩)
  · intro entry he
    have bound : entry.2 ≤ 48 := by
      simp only [savedRegisters,List.mem_cons,List.not_mem_nil,or_false] at he
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    exact (savedRead bound).trans (state.saved entry he)
  · have he := savedRead (offset := 0) (by decide)
    simp only [BitVec.sub_zero] at he
    exact he.trans state.returnAddress

end P256.Proofs.HMAC.Finalize.Digest
