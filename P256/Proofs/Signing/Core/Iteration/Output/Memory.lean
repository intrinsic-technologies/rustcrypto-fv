import P256.Proofs.Signing.Core.Iteration.Call
import P256.Proofs.Program.ScalarFrame.Output
import P256.Proofs.Field.Preserve

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Output

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Program
open SecretKeyFromBytes.Scalar
open NextNonce (scalarFrame coreFrame base_add)

variable [Bindings] {s t u v : RamState} {boundary : ReturnBoundary}

theorem output_stack_apart (pre : SignPre s boundary) :
    RangeApart (s.regValue .rdi) 65 (frameBase s) 2280 := by
  intro i hi j hj eq
  have left := memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) hi
  have right := ScalarFrame.stack_contains pre.toCalleePre (offset:=2280) (len:=2280)
    (by decide) (by decide) ⟨j,hj,rfl⟩
  exact pre.separation (1 : Fin 3) (2 : Fin 3) (by decide) _ left (eq ▸ right)

theorem output_of_stack_frame (pre : SignPre s boundary)
    (memory : MemoryWriteFrame t u #v[ScalarFrame.workRegion s 4584]) :
    ∀ i < 65, u.external[s.regValue .rdi+BitVec.ofNat 64 i]? =
      t.external[s.regValue .rdi+BitVec.ofNat 64 i]? := by
  intro i hi
  apply memory
  intro r hr hin
  have eq : r = ScalarFrame.workRegion s 4584 := by simpa using hr
  subst r
  apply pre.separation (1 : Fin 3) (2 : Fin 3) (by decide) _
    (memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) hi)
  change (stackPtr s).toNat-4584 ≤ _ ∧ _ < (stackPtr s).toNat-4584+(4584-48) at hin
  change (stackPtr s).toNat-4584 ≤ _ ∧ _ < (Stack.region s 4584).start+(Stack.region s 4584).size
  rw [stack_region_end]
  have h := stack_bounds pre.stack
  constructor <;> omega

theorem call_preserved {target ret : BitVec 64} {bytes reserve : Nat}
    (effect : (callEffect (fun _ => target) ret t).Holds t v)
    (result : CalleeResult v u boundary bytes reserve)
    (r : Syntax.Reg) (hr : r ∈ [.rbx,.rbp,.r12,.r13,.r14,.r15]) :
    u.regValue r = t.regValue r := by
  apply (result.calleeSaved r hr).trans
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl|rfl|rfl|rfl
  · exact effect.agrees.read (n:=64) (r:=3) (by simp)
  · exact effect.agrees.read (n:=64) (r:=5) (by simp)
  · exact effect.agrees.read (n:=64) (r:=12) (by simp)
  · exact effect.agrees.read (n:=64) (r:=13) (by simp)
  · exact effect.agrees.read (n:=64) (r:=14) (by simp)
  · exact effect.agrees.read (n:=64) (r:=15) (by simp)

theorem call_output {target ret : BitVec 64} {bytes reserve output : Nat}
    (pre : SignPre s boundary) (frame : Frame s t)
    (effect : (callEffect (fun _ => target) ret t).Holds t v)
    (result : CalleeResult v u boundary bytes reserve)
    (capacity : 2288+reserve ≤ 4584) (bound : output+bytes ≤ 2232)
    (destination : t.regValue .rdi = frameBase s+BitVec.ofNat 64 output) :
    ∀ i < 65, u.external[s.regValue .rdi+BitVec.ofNat 64 i]? =
      t.external[s.regValue .rdi+BitVec.ofNat 64 i]? := by
  have sp := effect.writes.1.trans (ScalarFrame.scalar_call_address (scalarFrame frame))
  have dst := ((effect.agrees.read (n:=64) (r:=7) (by simp)).trans destination).trans
    (base_add s (by omega))
  have memory := result.stack_frame pre.stack sp dst capacity (savedBytes:=48)
    (by decide) (by omega) (by omega)
  have push : pushAddr t = stackPtr s-2288 := ScalarFrame.scalar_call_address (scalarFrame frame)
  have pushed : MemoryWriteFrame t v #v[ScalarFrame.workRegion s 4584] :=
    effect.agrees.memoryWriteFrame (by
      intro c hc a ha
      simp only [callEffect,pushEffect_components,List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl|rfl|rfl <;> try exact ha.elim
      exact ⟨_,by simp,ScalarFrame.work_contains pre.toCalleePre (offset:=2288) (len:=8)
        (by decide) (by decide) (push ▸ ha)⟩)
  exact output_of_stack_frame pre (memoryWriteFrame_trans pushed memory)

structure Payload (s t : RamState) (r scalarS : Nat) : Prop where
  bounded : r < 2^256
  low : t.regValue .r12 = BitVec.ofNat 64 r
  next : t.regValue .rbx = BitVec.ofNat 64 (r/2^64)
  third : memLoad t.external (s.regValue .rdi+16) 64 = BitVec.ofNat 64 (r/2^128)
  fourth : memLoad t.external (s.regValue .rdi+24) 64 = BitVec.ofNat 64 (r/2^192)
  second : Nat256At t (s.regValue .rdi+32) scalarS
  destination : t.regValue .r15 = s.regValue .rdi

omit [Bindings] in
theorem Payload.copy {r scalarS : Nat} (payload : Payload s t r scalarS)
    (memory : ∀ i < 64, u.external[s.regValue .rdi+BitVec.ofNat 64 i]? =
      t.external[s.regValue .rdi+BitVec.ofNat 64 i]?)
    (regs : ∀ r ∈ [Syntax.Reg.r12,.rbx,.r15], u.regValue r = t.regValue r) :
    Payload s u r scalarS := by
  have word (off : Nat) (bound : off+8 ≤ 64) :
      memLoad u.external (s.regValue .rdi+BitVec.ofNat 64 off) 64 =
        memLoad t.external (s.regValue .rdi+BitVec.ofNat 64 off) 64 := by
    apply memLoad_congr
    intro i hi
    apply memByte_congr
    rw [BitVec.add_assoc,← BitVec.ofNat_add]
    exact memory _ (by omega)
  exact ⟨payload.bounded,(regs _ (by simp)).trans payload.low,
    (regs _ (by simp)).trans payload.next,(word 16 (by decide)).trans payload.third,
    (word 24 (by decide)).trans payload.fourth,
    ⟨payload.second.1,fun i hi => by
      have h := memory (32+i) (by omega)
      simp only [BitVec.ofNat_add,← BitVec.add_assoc] at h
      exact h.trans (payload.second.2 i hi)⟩,
    (regs _ (by simp)).trans payload.destination⟩

omit [Bindings] in
theorem Payload.after_registers {r scalarS : Nat} {cs : List Component}
    (payload : Payload s t r scalarS) (agrees : AgreesExcept cs t u)
    (memory : ∀ c ∈ cs, ∀ a, ¬ c.Covers a)
    (r12 : Component.reg 12 ∉ cs) (rbx : Component.reg 3 ∉ cs) (r15 : Component.reg 15 ∉ cs) :
    Payload s u r scalarS := by
  apply payload.copy (fun _ _ => congrArg (·[_]?) (agrees.external memory))
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl
  · exact agrees.read (n:=64) (r:=12) r12
  · exact agrees.read (n:=64) (r:=3) rbx
  · exact agrees.read (n:=64) (r:=15) r15

theorem stack_words_frame {cs : List Component} {offsets : List Nat}
    (pre : SignPre s boundary) (agrees : AgreesExcept cs t u)
    (writes : WordWrites (frameBase s) offsets cs)
    (bound : ∀ off ∈ offsets, off+8 ≤ 2232) :
    MemoryWriteFrame t u #v[ScalarFrame.workRegion s 4584] := by
  apply agrees.memoryWriteFrame
  intro c hc a ha
  obtain ⟨off,ho,i,hi,rfl⟩ := writes c hc a ha
  refine ⟨ScalarFrame.workRegion s 4584,by simp,?_⟩
  rw [base_add s (by have := bound off ho; omega)]
  exact ScalarFrame.work_contains (offset:=2280-off) (len:=8) pre.toCalleePre (by omega)
    (by have := bound off ho; omega) ⟨i,hi,rfl⟩

theorem Payload.after_stack {r scalarS : Nat} {cs : List Component} {offsets : List Nat}
    (pre : SignPre s boundary) (payload : Payload s t r scalarS) (agrees : AgreesExcept cs t u)
    (writes : WordWrites (frameBase s) offsets cs)
    (bound : ∀ off ∈ offsets, off+8 ≤ 2232)
    (r12 : Component.reg 12 ∉ cs) (rbx : Component.reg 3 ∉ cs) (r15 : Component.reg 15 ∉ cs) :
    Payload s u r scalarS := by
  apply payload.copy (fun i hi => output_of_stack_frame pre (stack_words_frame pre agrees writes bound) i (by omega))
  intro r hr
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl|rfl|rfl
  · exact agrees.read (n:=64) (r:=12) r12
  · exact agrees.read (n:=64) (r:=3) rbx
  · exact agrees.read (n:=64) (r:=15) r15

end P256.Proofs.Signing.Core.Iteration.Output
