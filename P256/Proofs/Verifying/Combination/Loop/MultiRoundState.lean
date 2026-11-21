import P256.Proofs.Verifying.Combination.Loop.MultiMemory

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Loop.Multi

open P256.Spec P256.Spec.Program P256.Proofs.Projective P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure RoundData [Bindings] (s t : RamState) (tables digits : BitVec 64)
    (p q : Projective) (u v k : Nat) (point : Projective) : Prop
    extends Memory s t tables digits p q u v where
  count : t.regValue .rbx = BitVec.ofNat 64 k
  positive : 0 < k
  bounded : k ≤ max (Naf.digits u).length (Naf.digits v).length
  scratch : t.regValue .r15 = stackPtr s - 144
  value : ProjectiveAt t (stackPtr s - 336) point
  total : memLoad t.external (stackPtr s - 400) 64 = 2
  tableBase : memLoad t.external (stackPtr s - 384) 64 = tables
  output : memLoad t.external (stackPtr s - 392) 64 = s.regValue .rdi

structure RoundState [Bindings] (s t : RamState) (tables digits : BitVec 64)
    (p q : Projective) (u v k : Nat) (point : Projective)
    (address : BitVec 64 := 0x10f174) : Prop extends RoundData s t tables digits p q u v k point where
  rip : t.RIP = address
  cursor : t.regValue .r13 = digits + BitVec.ofNat 64 (k+7)
  identity : (t.regValue .r14).getLsbD 0 = false → point = Projective.identity

theorem Memory.after_registers [Bindings] {s t w : RamState}
    {tables digits : BitVec 64} {p q : Projective} {u v : Nat} {cs : List Component}
    (state : Memory s t tables digits p q u v) (ready : ReadyToStep w)
    (agrees : AgreesExcept cs t w) (memory : ∀ c ∈ cs, ∀ a, ¬c.Covers a)
    (stack : Component.reg 4 ∉ cs)
    (hdf : Component.df ∉ cs := by component_not_mem)
    (hmxcsr : Component.mxcsr ∉ cs := by component_not_mem)
    (hfcw : Component.fcw ∉ cs := by component_not_mem) :
    Memory s w tables digits p q u v := by
  have external := agrees.external memory
  exact ⟨state.toFrameState.after_registers ready agrees memory stack,
    state.leftTable.of_copy (fun _ _ => congrArg (fun m : Ram => m[_]?) external),
    state.rightTable.of_copy (fun _ _ => congrArg (fun m : Ram => m[_]?) external),
    state.leftDigits.of_copy (fun _ _ => congrArg (fun m : Ram => m[_]?) external),
    state.rightDigits.of_copy (fun _ _ => congrArg (fun m : Ram => m[_]?) external)⟩

theorem RoundData.after_registers [Bindings] {s t w : RamState}
    {tables digits : BitVec 64} {p q point : Projective} {u v k : Nat} {cs : List Component}
    (state : RoundData s t tables digits p q u v k point) (ready : ReadyToStep w)
    (agrees : AgreesExcept cs t w) (memory : ∀ c ∈ cs, ∀ a, ¬c.Covers a)
    (kept : ∀ r ∈ [3, 4, 15], Component.reg r ∉ cs)
    (hdf : Component.df ∉ cs := by component_not_mem)
    (hmxcsr : Component.mxcsr ∉ cs := by component_not_mem)
    (hfcw : Component.fcw ∉ cs := by component_not_mem) :
    RoundData s w tables digits p q u v k point := by
  have external := agrees.external memory
  refine ⟨state.toMemory.after_registers ready agrees memory (kept 4 (by simp)),
    (agrees.read (n := 64) (r := 3) (kept 3 (by simp))).trans state.count,
    state.positive, state.bounded,
    (agrees.read (n := 64) (r := 15) (kept 15 (by simp))).trans state.scratch,
    state.value.of_bytes_eq (fun _ _ => congrArg (fun m : Ram => m[_]?) external), ?_, ?_, ?_⟩
  · rw [external]; exact state.total
  · rw [external]; exact state.tableBase
  · rw [external]; exact state.output

theorem RoundState.after_registers [Bindings] {s t w : RamState}
    {tables digits : BitVec 64} {p q point : Projective} {u v k : Nat}
    {address next : BitVec 64} {cs : List Component}
    (state : RoundState s t tables digits p q u v k point address) (ready : ReadyToStep w)
    (agrees : AgreesExcept cs t w) (memory : ∀ c ∈ cs, ∀ a, ¬c.Covers a)
    (kept : ∀ r ∈ [3, 4, 13, 14, 15], Component.reg r ∉ cs)
    (rip : w.RIP = next)
    (hdf : Component.df ∉ cs := by component_not_mem)
    (hmxcsr : Component.mxcsr ∉ cs := by component_not_mem)
    (hfcw : Component.fcw ∉ cs := by component_not_mem) :
    RoundState s w tables digits p q u v k point next := by
  refine ⟨state.toRoundData.after_registers ready agrees memory
      (fun r hr => kept r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl <;> simp)), rip,
    (agrees.read (n := 64) (r := 13) (kept 13 (by simp))).trans state.cursor, ?_⟩
  intro h
  have eq : w.regValue .r14 = t.regValue .r14 := agrees.read (n := 64) (r := 14) (kept 14 (by simp))
  exact state.identity (by rwa [eq] at h)

end P256.Proofs.Verifying.Combination.Loop.Multi
