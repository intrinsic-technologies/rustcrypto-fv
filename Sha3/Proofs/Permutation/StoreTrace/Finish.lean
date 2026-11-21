import Sha3.Proofs.Permutation.StoreTrace.Program

namespace Sha3.Proofs.Permutation.StoreTrace

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

def sourcePrefix (n : Nat) : Location → Location :=
  (program.take n).foldl
    (fun a e loc ↦ if loc = e.2.1.dst then a e.2.1.src else a loc) id

theorem runPrefix_source (a : State) (n : Nat) (loc : Location) :
    runPrefix a n loc = a (sourcePrefix n loc) := by
  have h := List.foldl_hom (fun f : Location → Location ↦ a ∘ f)
    (g₁ := fun f (e : Nat × Move × List UInt8) loc ↦
      if loc = e.2.1.dst then f e.2.1.src else f loc)
    (g₂ := fun f e ↦ execute f e.2.1)
    (l := program.take n) (init := id) (by
      intro f e
      funext loc
      simp only [execute, Function.comp_apply]
      split <;> rfl)
  exact congrFun h loc

theorem sourcePrefix_stack (i : Fin 42) : sourcePrefix i.val (.reg 4) = .reg 4 := by
  have h : ∀ j : Fin 42, sourcePrefix j.val (.reg 4) = .reg 4 := by decide +kernel
  exact h i

theorem sourcePrefix_pointer (i : Fin 41) (j : Fin 25)
    (hd : (dataOp i).dst = .output j) : sourcePrefix i.val (.reg 2) = .stack 20 := by
  have h : ∀ k : Fin 41, ∀ l : Fin 25,
      (dataOp k).dst = .output l → sourcePrefix k.val (.reg 2) = .stack 20 := by
    decide +kernel
  exact h i j hd

theorem runPrefix_stack (a : State) (i : Fin 42) :
    runPrefix a i.val (.reg 4) = a (.reg 4) := by
  rw [runPrefix_source, sourcePrefix_stack]

theorem models_stack {copy : Copy} {sp pointer : BitVec 64} {s t : RamState}
    (hp : Store.Pre copy sp pointer s) (i : Fin 42)
    (hm : Models sp pointer (runPrefix (model sp pointer s) i.val) t) :
    (Operand.reg 4 : Operand 64).read t = sp := by
  have h := (hm (.reg 4)).trans (runPrefix_stack (model sp pointer s) i)
  exact h.trans hp.stack

theorem pointerPre_prefix {copy : Copy} {sp pointer : BitVec 64} {s t : RamState}
    (hp : Store.Pre copy sp pointer s) (i : Fin 41)
    (hm : Models sp pointer (runPrefix (model sp pointer s) i.val) t) :
    PointerPre pointer (dataOp i) t := by
  have hm' := hm (.reg 2)
  rw [runPrefix_source] at hm'
  unfold PointerPre
  cases hd : (dataOp i).dst with
  | reg r => trivial
  | stack j => trivial
  | output j =>
    rw [sourcePrefix_pointer i j hd] at hm'
    exact hm'.trans hp.pointerValue

def laneSources : Vector Location 25 := #v[
  .stack 3, .stack 16, .stack 17, .stack 15, .stack 14, .stack 4, .reg 9, .stack 6,
  .reg 11, .stack 2, .reg 0, .stack 5, .reg 12, .stack 7, .reg 13, .reg 5,
  .reg 1, .reg 15, .reg 14, .reg 3, .stack 10, .stack 12, .stack 11, .stack 13, .stack 0]

theorem sourcePrefix_output (i : Fin 25) :
    sourcePrefix 41 (.output i) = laneSources[i.val] := by
  have h : ∀ j : Fin 25, sourcePrefix 41 (.output j) = laneSources[j.val] := by
    decide +kernel
  exact h i

theorem model_laneSource (sp pointer : BitVec 64) (s : RamState) (i : Fin 25) :
    model sp pointer s laneSources[i.val] = readLanes sp s i := by
  finite_cases i <;> try rfl
  change (Operand.mem (sp + 0) : Operand 64).read s = (Operand.mem sp : Operand 64).read s
  exact congrArg (fun a : BitVec 64 ↦ (Operand.mem a : Operand 64).read s) (BitVec.add_zero sp)

theorem models_output {sp pointer : BitVec 64} {s t : RamState}
    (hm : Models sp pointer (runPrefix (model sp pointer s) 41) t) (i : Fin 25) :
    (Operand.mem (pointer + BitVec.ofNat 64 (8 * i.val)) : Operand 64).read t =
      readLanes sp s i := by
  have h := hm (.output i)
  rw [runPrefix_source, sourcePrefix_output, model_laneSource] at h
  exact h

def registerLanes : Vector (Fin 16 × Fin 25) 2 := #v[(0, 9), (6, 24)]

theorem sourcePrefix_register (i : Fin 2) :
    sourcePrefix 41 (.reg registerLanes[i.val].1) = laneSources[registerLanes[i.val].2.val] := by
  have h : ∀ j : Fin 2,
      sourcePrefix 41 (.reg registerLanes[j.val].1) = laneSources[registerLanes[j.val].2.val] := by
    decide +kernel
  exact h i

theorem models_register {sp pointer : BitVec 64} {s t : RamState}
    (hm : Models sp pointer (runPrefix (model sp pointer s) 41) t) (i : Fin 2) :
    (Operand.reg (BitVec.ofNat 5 registerLanes[i.val].1.val) : Operand 64).read t =
      readLanes sp s registerLanes[i.val].2 := by
  have h := hm (.reg registerLanes[i.val].1)
  rw [runPrefix_source, sourcePrefix_register, model_laneSource] at h
  exact h

theorem models_pointer {copy : Copy} {sp pointer : BitVec 64} {s t : RamState}
    (hp : Store.Pre copy sp pointer s)
    (hm : Models sp pointer (runPrefix (model sp pointer s) 41) t) :
    (Operand.reg 2 : Operand 64).read t = pointer := by
  have h := hm (.reg 2)
  rw [runPrefix_source] at h
  have hs : sourcePrefix 41 (.reg 2) = .stack 20 := by decide +kernel
  rw [hs] at h
  exact h.trans hp.pointerValue

theorem effect_holds {copy : Copy} {sp pointer : BitVec 64} {s t : RamState}
    (hp : Store.Pre copy sp pointer s)
    (hm : Models sp pointer (runPrefix (model sp pointer s) 41) t)
    (ht : t.RIP = Store.restoreAddress copy)
    (ha : AgreesExcept (Store.effect copy sp pointer s).components s t) :
    (Store.effect copy sp pointer s).Holds s t := by
  refine ⟨ht, ?_, trivial, ha⟩
  exact ⟨models_output hm 0, models_output hm 1, models_output hm 2,
    models_output hm 3, models_output hm 4, models_output hm 5, models_output hm 6,
    models_output hm 7, models_output hm 8, models_output hm 9, models_output hm 10,
    models_output hm 11, models_output hm 12, models_output hm 13, models_output hm 14,
    models_output hm 15, models_output hm 16, models_output hm 17, models_output hm 18,
    models_output hm 19, models_output hm 20, models_output hm 21, models_output hm 22,
    models_output hm 23, models_output hm 24, models_register hm 0,
    models_pointer hp hm, models_register hm 1⟩

end Sha3.Proofs.Permutation.StoreTrace
