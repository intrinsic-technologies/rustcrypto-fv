import P256.Proofs.Projective.Multiply.Machine.Radix.Interface
import P256.Proofs.Program.ScalarFrame.Memory

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Radix

open P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs Program

def registers : List Component :=
  [.reg 0,.reg 1,.reg 2,.reg 3,.reg 4,.reg 6,.reg 7,.reg 8,.reg 9,.reg 10,.reg 11,
    .flags,.rip]

def components (s : RamState) : List Component :=
  registers ++ [.mem (s.regValue .rdi) 65,.mem (stackPtr s - 136) 136]

abbrev workRegion (s : RamState) : MemoryRegion := ScalarFrame.Work.region s 136 8

structure State [Bindings] (s t : RamState) (offset : BitVec 64 := 120) : Prop where
  ready : ReadyToStep t
  agrees : AgreesExcept (components s) s t
  rsp : stackPtr t = stackPtr s - offset
  saved : memLoad t.external (stackPtr s - 8) 64 = s.regValue .rbx

theorem covers_of_bounds {base a : BitVec 64} {n : Nat}
    (lo : base.toNat ≤ a.toNat) (hi : a.toNat < base.toNat + n) :
    (Component.mem base n).Covers a := by
  refine ⟨a.toNat - base.toNat, by omega, ?_⟩
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (show a.toNat - base.toNat < 2^64 by have := a.isLt; omega),
    Nat.add_sub_of_le lo, Nat.mod_eq_of_lt a.isLt]

theorem memory_component [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10b720 32 65 136) {a : BitVec 64} {region : MemoryRegion}
    (member : region ∈ #v[registerRegion s .rdi 65,workRegion s])
    (covered : region.Contains a.toNat) :
    ∃ c ∈ components s, c.Covers a := by
  have hm : region = registerRegion s .rdi 65 ∨ region = workRegion s := by simpa using member
  rcases hm with rfl | rfl
  · exact ⟨.mem (s.regValue .rdi) 65, by simp [components],
      covers_of_bounds covered.1 covered.2⟩
  · refine ⟨.mem (stackPtr s - 136) 136, by simp [components], ?_⟩
    have low : (stackPtr s - 136).toNat = (stackPtr s).toNat - 136 :=
      stack_sub_toNat pre.stack (offset := 136) (by decide)
    apply covers_of_bounds
    · rw [low]
      exact covered.1
    · rw [low]
      have hc : a.toNat < (stackPtr s).toNat - 136 + (136-8) := covered.2
      omega

theorem State.frame [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {offset : BitVec 64} (pre : CalleePre s boundary 0x10b720 32 65 136)
    (state : State s t offset) :
    MemoryWriteFrame s t #v[registerRegion s .rdi 65,Stack.region s 136] := by
  apply state.agrees.memoryWriteFrame
  intro c hc a ha
  simp only [components, registers, List.mem_append, List.mem_cons, List.not_mem_nil,
    or_false] at hc
  rcases hc with (rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl) | rfl | rfl
  all_goals try exact ha.elim
  · refine ⟨registerRegion s .rdi 65, by simp, ?_⟩
    obtain ⟨i,hi,rfl⟩ := ha
    exact memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) hi
  · exact ⟨Stack.region s 136, by simp,
      ScalarFrame.stack_contains pre (by decide) (by decide) ha⟩

theorem State.loaded [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {offset : BitVec 64} (pre : CalleePre s boundary 0x10b720 32 65 136)
    (state : State s t offset) : ProgramLoaded t :=
  ScalarFrame.loaded_of_frame pre (state.frame pre)

theorem State.after [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {offset offset' : BitVec 64} {cs : List Component}
    (pre : CalleePre s boundary 0x10b720 32 65 136) (state : State s t offset)
    (ready : ReadyToStep u) (agrees : AgreesExcept cs t u)
    (regs : ∀ c ∈ cs, c.isMem = false → c ∈ registers)
    (writes : WritesWithin cs #v[registerRegion s .rdi 65,workRegion s])
    (rsp : stackPtr u = stackPtr s - offset') : State s u offset' := by
  have narrow : AgreesExcept (components s) t u := by
    apply agrees.widen
    · intro c hc hm
      exact List.mem_append_left _ (regs c hc hm)
    · intro a c hc ha
      obtain ⟨region, hr, hin⟩ := writes c hc a ha
      exact memory_component pre hr hin
  refine ⟨ready, (state.agrees.trans narrow).mono (by simp), rsp, ?_⟩
  exact (ScalarFrame.Work.read pre (savedBytes := 8) (by decide)
    (agrees.memoryWriteFrame writes) (offset := 8) (n := 64) (by decide) (by decide)).trans
      state.saved

theorem State.after_registers [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {offset offset' : BitVec 64} {cs : List Component}
    (pre : CalleePre s boundary 0x10b720 32 65 136) (state : State s t offset)
    (ready : ReadyToStep u) (agrees : AgreesExcept cs t u)
    (regs : cs ⊆ registers) (noMemory : ∀ c ∈ cs, ∀ a, ¬c.Covers a)
    (rsp : stackPtr u = stackPtr s - offset') : State s u offset' :=
  state.after pre ready agrees (fun _ hc _ => regs hc)
    (fun c hc a ha => (noMemory c hc a ha).elim) rsp

end P256.Proofs.Projective.Multiply.Machine.Radix
