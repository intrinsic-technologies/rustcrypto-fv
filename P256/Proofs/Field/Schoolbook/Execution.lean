import P256.Proofs.Field.Schoolbook.BlockFrames

set_option autoImplicit false

open P256.Proofs.Common.Field.SquareRoot.Multiply (prologueComponents savedMemory)
open P256.Proofs.Program (memoryRegion_contains_add)

namespace P256.Proofs.Field.Schoolbook

open P256.Proofs.Program P256.Proofs.Common.Field
open P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Spec.Program.Routines

open P256.Spec P256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure ExecutionContext [Bindings] (s : RamState) (boundary : ReturnBoundary)
    (entry : RamState) : Prop where
  pre : SchoolbookPre s boundary
  execution : Advances boundary 11 s entry
  ready : ReadyToStep entry
  rip : entry.RIP = 0x11c982
  rsp : stackPtr entry = stackPtr s-136
  memory : entry.external = savedMemory s
  agrees : AgreesExcept (prologueComponents s) s entry

structure BodyState [Bindings] {s : RamState} {boundary : ReturnBoundary} {entry : RamState}
    (ctx : ExecutionContext s boundary entry) (t : RamState) : Prop where
  execution : ∃ fuel, Advances boundary fuel s t
  ready : ReadyToStep t
  agrees : AgreesExcept (scratchComponents (stackPtr s-136)) entry t

theorem execution_context [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : SchoolbookPre s boundary) : ∃ entry, ExecutionContext s boundary entry := by
  obtain ⟨entry, run, ready, _, rip, rsp, memory, agrees⟩ :=
    prologue_correct pre
  exact ⟨entry, pre, run, ready, rip, rsp, memory, agrees⟩

namespace BodyState

variable [Bindings] {s entry t u : RamState} {boundary : ReturnBoundary}
  {ctx : ExecutionContext s boundary entry}

theorem initial (ctx : ExecutionContext s boundary entry) : BodyState ctx entry :=
  ⟨⟨11, ctx.execution⟩, ctx.ready, AgreesExcept.refl _ _⟩

theorem rsp (h : BodyState ctx t) : stackPtr t = stackPtr s-136 :=
  (h.agrees.read (n := 64) (r := 4) (by simp [scratchComponents])).trans ctx.rsp

theorem destination (h : BodyState ctx t) : t.regValue .rdi = s.regValue .rdi := by
  exact (h.agrees.read (n := 64) (r := 7) (by simp [scratchComponents])).trans
    (ctx.agrees.read (by simp [prologueComponents]))

theorem grow (h : BodyState ctx t) :
    ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome :=
  (ctx.agrees.trans h.agrees).grow

theorem frame (h : BodyState ctx t) :
    MemoryWriteFrame s t #v[registerRegion s .rdi 64, Stack.region s 136] :=
  memoryWriteFrame_trans (ctx.agrees.memoryWriteFrame (prologue_within ctx.pre))
    (h.agrees.memoryWriteFrame (scratchComponents_within ctx.pre))

theorem loaded (h : BodyState ctx t) : ProgramLoaded t :=
  by
    intro a b ha
    rw [h.frame a]
    · exact ctx.pre.loaded a b ha
    · intro r hr hc
      exact ctx.pre.avoids r (by simpa using hr) a hc (.inl ⟨b, ha⟩)

theorem nat256 (h : BodyState ctx t) {address : BitVec 64} {value : Nat}
    (bounded : (MemoryRegion.mk address.toNat 32).Bounded)
    (output : (MemoryRegion.mk address.toNat 32).Disjoint (registerRegion s .rdi 64))
    (stack : (MemoryRegion.mk address.toNat 32).Disjoint (Stack.region s 136))
    (initial : Nat256At s address value) : Nat256At t address value := by
  refine ⟨initial.1, ?_⟩
  intro i hi
  rw [h.frame _]
  · exact initial.2 i hi
  · intro region hr hin
    have here := memoryRegion_contains_add bounded (len := 32)
      (Nat.le_refl _) (Nat.le_refl _) hi
    have hr' : region = registerRegion s .rdi 64 ∨ region = Stack.region s 136 := by simpa using hr
    rcases hr' with rfl | rfl
    · exact output _ here hin
    · exact stack _ here hin

theorem scratchPre (h : BodyState ctx t) {p : BitVec 64} {len : Nat}
    (rip : t.RIP = p) (code : ∀ j < len, InProgram (p+BitVec.ofNat 64 j)) :
    ScratchPre p len t :=
  scratchPre_of_callee ctx.pre rip h.rsp h.grow code

theorem advance (h : BodyState ctx t) {pre : RamState → Prop} {code : CodeMap}
    {effect : RamState → Effect}
    (block : AdvanceTriple boundary pre code (Effect.post effect))
    (codeIn : CodeIn code t) (hp : pre t)
    (preserves : ∀ u, (effect t).Holds t u → AgreesExcept (scratchComponents (rspOf t)) t u) :
    ∃ u, BodyState ctx u ∧ (effect t).Holds t u := by
  obtain ⟨fuel, u, run, ready, _, he⟩ := block t h.ready codeIn hp
  obtain ⟨prior, hr⟩ := h.execution
  have hag := preserves u he
  change AgreesExcept (scratchComponents (stackPtr t)) t u at hag
  rw [h.rsp] at hag
  exact ⟨u, ⟨⟨prior+fuel, hr.trans run⟩, ready, scratch_agrees_trans h.agrees hag⟩, he⟩

end BodyState

end P256.Proofs.Field.Schoolbook
