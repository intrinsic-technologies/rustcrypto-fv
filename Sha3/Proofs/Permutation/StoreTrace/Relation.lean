import Sha3.Proofs.Permutation.StoreTrace.Basic

namespace Sha3.Proofs.Permutation.StoreTrace

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

theorem moveEffect_components (sp pointer next : BitVec 64) (op : Move) (s : RamState) :
    (moveEffect sp pointer next op s).components =
      [(operand sp pointer op.dst).component, .rip] := rfl

theorem moveEffect_covers {sp pointer next : BitVec 64} {op : Move} {s : RamState}
    {c : Component} {address : BitVec 64}
    (hc : c ∈ (moveEffect sp pointer next op s).components) (hcov : c.Covers address) :
    (operand sp pointer op.dst).component.Covers address := by
  rw [moveEffect_components] at hc
  rcases List.mem_cons.mp hc with rfl | hc
  · exact hcov
  · have : c = .rip := by simpa using hc
    subst c
    exact hcov.elim

theorem read_mem_moveEffect {sp pointer next address : BitVec 64} {op : Move} {s t : RamState}
    (he : (moveEffect sp pointer next op s).Holds s t)
    (hc : ∀ i, i < 8 → ¬ (operand sp pointer op.dst).component.Covers
      (address + BitVec.ofNat 64 i)) :
    (Operand.mem address : Operand 64).read t = (Operand.mem address : Operand 64).read s := by
  apply memLoad_congr
  intro i hi
  unfold memByte
  change (t.external[_]?).getD 0 = (s.external[_]?).getD 0
  rw [he.agrees.byte]
  intro c hm hv
  exact hc i hi (moveEffect_covers hm hv)

theorem output_offset_bound (i : Fin 25) : (BitVec.ofNat 64 (8 * i.val)).toNat + 8 ≤ 200 := by
  simp only [BitVec.toNat_ofNat]
  have := i.isLt
  omega

theorem stack_offset_bound (i : Fin 34) : (BitVec.ofNat 64 (8 * i.val)).toNat + 8 ≤ 272 := by
  simp only [BitVec.toNat_ofNat]
  have := i.isLt
  omega

theorem read_moveEffect_of_ne {sp pointer next : BitVec 64} {op : Move} {loc : Location}
    {s t : RamState} (he : (moveEffect sp pointer next op s).Holds s t)
    (hv : AllowedWrite op.dst) (ha : RangeApart pointer 200 sp 272) (hne : loc ≠ op.dst) :
    (operand sp pointer loc).read t = (operand sp pointer loc).read s := by
  cases hd : op.dst with
  | stack i => simp only [hd, AllowedWrite] at hv
  | reg r =>
    cases loc with
    | reg r' =>
      apply he.agrees.read
      simpa [moveEffect_components, hd, operand, Operand.component,
        RoundMachine.regNumber_inj] using hne
    | stack i =>
      apply read_mem_moveEffect he
      simp [hd, operand, Operand.component, Component.Covers]
    | output i =>
      apply read_mem_moveEffect he
      simp [hd, operand, Operand.component, Component.Covers]
  | output i =>
    cases loc with
    | reg r =>
      apply he.agrees.read
      simp [moveEffect_components, hd, operand, Operand.component]
    | stack j =>
      apply read_mem_moveEffect he
      intro k hk hcov
      simp only [hd, operand, Operand.component, Component.Covers] at hcov
      obtain ⟨l, hl, heq⟩ := hcov
      have hap := Store.apart_offset ha (output_offset_bound i) (stack_offset_bound j)
      exact hap l hl k hk heq.symm
    | output j =>
      apply read_mem_moveEffect he
      intro k hk hcov
      simp only [hd, operand, Operand.component, Component.Covers] at hcov
      obtain ⟨l, hl, heq⟩ := hcov
      have hi : 8 * i.val % 8 = 0 ∧ 8 * i.val < 272 := by
        have := i.isLt
        omega
      have hj : 8 * j.val % 8 = 0 ∧ 8 * j.val < 272 := by
        have := j.isLt
        omega
      have hneq : 8 * i.val ≠ 8 * j.val := by
        intro heq
        apply hne
        rw [hd]
        congr 1
        apply Fin.ext
        omega
      exact RoundMachine.stackBytes_ne pointer hi hj hneq hl hk heq.symm

theorem models_execute {sp pointer next : BitVec 64} {op : Move} {a : State} {s t : RamState}
    (hm : Models sp pointer a s) (hv : AllowedWrite op.dst)
    (ha : RangeApart pointer 200 sp 272) (he : (moveEffect sp pointer next op s).Holds s t) :
    Models sp pointer (execute a op) t := by
  intro loc
  by_cases heq : loc = op.dst
  · subst loc
    have hw : (operand sp pointer op.dst).read t = (operand sp pointer op.src).read s := he.writes
    rw [hw, hm]
    simp [execute]
  · rw [read_moveEffect_of_ne he hv ha heq, hm]
    simp [execute, heq]

theorem Memory.of_holds {copy : Copy} {sp pointer : BitVec 64} {s t : RamState} {e : Effect}
    (hm : Memory copy sp pointer s) (he : e.Holds s t) : Memory copy sp pointer t :=
  ⟨⟨hm.frameRead.low, fun i hi ↦ he.agrees.grow _ (hm.frameRead.mem i hi)⟩,
    ⟨hm.outputRead.low, fun i hi ↦ he.agrees.grow _ (hm.outputRead.mem i hi)⟩,
    hm.apart, hm.codeApart, hm.tables⟩

theorem moveEffect_avoids {copy : Copy} {sp pointer next : BitVec 64} {op : Move} {s : RamState}
    (hv : AllowedWrite op.dst) (hm : Memory copy sp pointer s) :
    (moveEffect sp pointer next op s).Avoids (codeRange (storeAddress copy) Store.bytes) := by
  apply Effect.avoids_codeRange
  intro c hc addr len hcl
  rw [moveEffect_components] at hc
  rcases List.mem_cons.mp hc with rfl | hc
  · cases hd : op.dst with
    | reg r => simp [hd, operand, Operand.component] at hcl
    | stack i => simp only [hd, AllowedWrite] at hv
    | output i =>
      have hh : pointer + BitVec.ofNat 64 (8 * i.val) = addr ∧ 8 = len := by
        simpa [hd, operand, Operand.component] using hcl
      rcases hh with ⟨rfl, rfl⟩
      exact Store.codeApart_offset hm.codeApart (output_offset_bound i)
  · have : c = .rip := by simpa using hc
    rw [this] at hcl
    cases hcl

theorem finalComponents (copy : Copy) (sp pointer : BitVec 64) (s : RamState) :
    (Store.effect copy sp pointer s).components =
      List.ofFn (fun i : Fin 25 ↦ Component.mem (pointer + BitVec.ofNat 64 (8 * i.val)) 8) ++
        [.reg 0, .reg 2, .reg 6, .rip] := by
  simp [Store.effect, Effect.components, List.ofFn_succ]

theorem allowedWrite_mem {copy : Copy} {sp pointer : BitVec 64} {s : RamState} {loc : Location}
    (hv : AllowedWrite loc) :
    (operand sp pointer loc).component ∈ (Store.effect copy sp pointer s).components := by
  rw [finalComponents]
  cases loc with
  | reg r =>
    have hr : r = 0 ∨ r = 2 ∨ r = 6 := by
      simpa [AllowedWrite] using hv
    apply List.mem_append_right
    rcases hr with rfl | rfl | rfl <;>
      dsimp only [operand, Operand.component] <;> decide +kernel
  | stack i => exact hv.elim
  | output i =>
    apply List.mem_append_left
    exact List.mem_ofFn.mpr ⟨i, rfl⟩

theorem moveEffect_frame {copy : Copy} {sp pointer next : BitVec 64} {op : Move}
    {initial s t : RamState}
    (hv : AllowedWrite op.dst) (he : (moveEffect sp pointer next op s).Holds s t)
    (hf : AgreesExcept (Store.effect copy sp pointer initial).components initial s) :
    AgreesExcept (Store.effect copy sp pointer initial).components initial t := by
  apply (hf.trans he.agrees).mono
  intro c hc
  rcases List.mem_append.mp hc with hc | hc
  · exact hc
  · rw [moveEffect_components] at hc
    rcases List.mem_cons.mp hc with rfl | hc
    · exact allowedWrite_mem hv
    · have : c = .rip := by simpa using hc
      subst c
      simp [finalComponents]

end Sha3.Proofs.Permutation.StoreTrace
