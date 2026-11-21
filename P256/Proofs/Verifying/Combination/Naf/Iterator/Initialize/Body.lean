import P256.Proofs.Verifying.Combination.Naf.Iterator.Initialize.Memory
import P256.Proofs.Verifying.Combination.Naf.Iterator.Interface
import P256.Proofs.Verifying.Combination.Naf.Iterator.Support

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Naf.Iterator.Initialize

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.SecretKeyFromBytes.Scalar

def bodyComponents (s : RamState) : List Component :=
  saveFrame s ++ [.reg 3, .reg 0, .reg 14, .reg 1, .reg 2, .reg 6, .flags,
    .mem (s.regValue .rdi) 8, .mem (s.regValue .rdi + 8) 8,
    .mem (s.regValue .rdi + 16) 8, .mem (s.regValue .rdi + 24) 8,
    .mem (s.regValue .rdi + 32) 8, .rip]

structure BodyState [Bindings] (s t : RamState) (n reserve : Nat) : Prop where
  ready : ReadyToStep t
  loaded : ProgramLoaded t
  rip : t.RIP = 0x1182df
  rsp : stackPtr t = stackPtr s - 24
  agrees : AgreesExcept (bodyComponents s) s t
  frame : MemoryWriteFrame s t #v[registerRegion s .rdi 40, Stack.region s reserve]
  state : StateAt t (s.regValue .rdi) (s.regValue .rsi) n 0
  rax : t.regValue .rax = s.regValue .rdi
  rbx : memLoad t.external (stackPtr s - 16) 64 = s.regValue .rbx
  r14 : memLoad t.external (stackPtr s - 8) 64 = s.regValue .r14
  returnAddress : memLoad t.external (stackPtr s) 64 = memLoad s.external (stackPtr s) 64

theorem body [Bindings] {s : RamState} {boundary : ReturnBoundary} {n reserve : Nat}
    (pre : CalleePre s boundary 0x118290 32 40 reserve) (reserved : 24 ≤ reserve)
    (length : s.regValue .rdx = 32)
    (input : Nat256At s (s.regValue .rsi) n) :
    ∃ fuel t, Advances boundary fuel s t ∧ BodyState s t n reserve := by
  obtain ⟨u, run0, ready0, loaded0, rip0, sp0, mem0, ag0⟩ := prologue pre reserved
  have rdx0 : u.regValue .rdx = 32 :=
    (ag0.read (n := 64) (r := 2) (by simp [saveFrame])).trans length
  obtain ⟨fuel1, v, run1, ready1, _, e1⟩ := initialize_prefix boundary pre.outerBoundary u ready0
    (programText_slice (programLoaded_codeIn loaded0) 0x18294 initializePrefixBytes
      (by decide) (by decide +kernel)) ⟨rip0, rdx0⟩
  have m1 : v.external = u.external := e1.agrees.external
    (by simp [initializePrefixEffect, Effect.components, Component.Covers])
  have loaded1 : ProgramLoaded v := by
    intro a b hb
    rw [m1]
    exact loaded0 a b hb
  have ag1 := ag0.trans e1.agrees
  have rsi1 : v.regValue .rsi = s.regValue .rsi :=
    ag1.read (n := 64) (r := 6) (by simp [saveFrame, initializePrefixEffect, Effect.components])
  have rdx1 : v.regValue .rdx = 32 :=
    (ag1.read (n := 64) (r := 2) (by simp [saveFrame, initializePrefixEffect, Effect.components])).trans length
  have rbx1 : v.regValue .rbx = s.regValue .rdi :=
    e1.writes.trans (ag0.read (n := 64) (r := 7) (by simp [saveFrame]))
  have readPre : InitializeReadPre v := ⟨e1.rip, rdx1, by rw [rsi1]; exact input_readable pre ag1.grow⟩
  obtain ⟨fuel2, w, run2, ready2, _, e2⟩ := initialize_read boundary pre.outerBoundary v ready1
    (programText_slice (programLoaded_codeIn loaded1) 0x182e7 initializeReadBytes
      (by decide) (by decide +kernel)) readPre
  have m2 : w.external = v.external := e2.agrees.external
    (by simp [initializeReadEffect, Effect.components, Component.Covers])
  have loaded2 : ProgramLoaded w := by
    intro a b hb
    rw [m2]
    exact loaded1 a b hb
  have ag2 := ag1.trans e2.agrees
  have rbx2 : w.regValue .rbx = s.regValue .rdi :=
    (e2.agrees.read (n := 64) (r := 3) (by simp [initializeReadEffect, Effect.components])).trans rbx1
  have storePre : InitializeStorePre w :=
    ⟨e2.rip, by rw [rbx2]; exact output_writable pre ag2.grow,
      by rw [rbx2]; exact output_apart pre⟩
  obtain ⟨fuel3, t, run3, ready3, _, e3⟩ := initialize_store boundary pre.outerBoundary w ready2
    (programText_slice (programLoaded_codeIn loaded2) 0x182c5 initializeStoreBytes
      (by decide) (by decide +kernel)) storePre
  have total : AgreesExcept (bodyComponents s) s t := by
    apply (ag2.trans e3.agrees).mono
    intro c hc
    simp only [bodyComponents, initializePrefixEffect, initializeReadEffect, initializeStoreEffect,
      Effect.components, rbx2, List.map_cons, List.map_nil, Write.component, Operand.component,
      List.append_nil, List.cons_append, List.nil_append, Nat.reduceDiv, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with ((h | h) | h) | h
    · exact Or.inl h
    · rcases h with rfl | rfl | rfl <;> simp
    · rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
    · rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp
  have ps := prologue_frame pre reserved ag0
  have sm : MemoryWriteFrame s w #v[Stack.region s reserve] := by
    intro a ha
    rw [m2, m1]
    exact ps a ha
  have om := output_frame pre rbx2 e3
  have frame : MemoryWriteFrame s t #v[registerRegion s .rdi 40, Stack.region s reserve] := by
    intro a ha
    rw [om a (by
      intro region hr hin
      have he : region = registerRegion s .rdi 40 := by simpa using hr
      exact ha _ (by simp [he]) hin)]
    exact sm a (by
      intro region hr hin
      have he : region = Stack.region s reserve := by simpa using hr
      exact ha _ (by simp [he]) hin)
  have reads := e2.writes
  change w.regValue .rax = v.regValue .rsi + 8 ∧
    w.regValue .r14 = memLoad v.external (v.regValue .rsi) 64 ∧
    w.regValue .rcx = memLoad v.external (v.regValue .rsi + 8) 64 ∧
    w.regValue .rdx = 16 ∧ w.regValue .rsi = v.regValue .rsi + 16 at reads
  have stores := e3.writes
  change memLoad t.external (w.regValue .rbx) 64 = w.regValue .rsi ∧
    memLoad t.external (w.regValue .rbx + 8) 64 = w.regValue .rdx ∧
    memLoad t.external (w.regValue .rbx + 16) 64 = 0 ∧
    memLoad t.external (w.regValue .rbx + 24) 64 = w.regValue .r14 ∧
    memLoad t.external (w.regValue .rbx + 32) 64 = w.regValue .rcx ∧
    t.regValue .rax = w.regValue .rbx at stores
  rw [rbx2] at stores
  have initial0 : memLoad v.external (v.regValue .rsi) 64 = word n 0 := by
    rw [rsi1, m1]
    have h := input_read_of_frame pre ps 0 (by decide)
    simp only [BitVec.add_zero] at h
    rw [h]
    simpa [word] using input.memLoad_limb 0 (by decide)
  have initial1 : memLoad v.external (v.regValue .rsi + 8) 64 = word n 1 := by
    rw [rsi1, m1]
    exact (input_read_of_frame pre ps 8 (by decide)).trans (input.memLoad_limb 1 (by decide))
  refine ⟨3 + fuel1 + fuel2 + fuel3, t, ((run0.trans run1).trans run2).trans run3,
    ⟨ready3, ScalarFrame.loaded_of_frame pre frame, e3.rip, ?_, total, frame, ?_,
      stores.2.2.2.2.2, ?_, ?_, ?_⟩⟩
  · exact (((e1.agrees.trans e2.agrees).trans e3.agrees).read (n := 64) (r := 4)
      (by simp [initializePrefixEffect, initializeReadEffect, initializeStoreEffect, Effect.components])).trans sp0
  · refine ⟨?_, stores.2.1.trans reads.2.2.2.1, stores.2.2.1, ?_, ?_⟩
    · exact stores.1.trans (reads.2.2.2.2.trans (congrArg (fun a : BitVec 64 => a + 16) rsi1))
    · exact stores.2.2.2.1.trans (reads.2.1.trans initial0)
    · exact stores.2.2.2.2.1.trans (reads.2.2.1.trans initial1)
  · change memLoad t.external (stackPtr s - 16#64) 64 = s.regValue .rbx
    rw [output_read_stack pre om 16 (by omega), m2, m1, mem0]
    exact saveMemory_rbx s
  · change memLoad t.external (stackPtr s - 8#64) 64 = s.regValue .r14
    rw [output_read_stack pre om 8 (by omega), m2, m1, mem0]
    exact saveMemory_r14 s
  · have hs := output_read_stack pre om 0 (by omega)
    simp only [BitVec.sub_zero] at hs
    rw [hs, m2, m1, mem0]
    exact saveMemory_return s

end P256.Proofs.Verifying.Combination.Naf.Iterator.Initialize
