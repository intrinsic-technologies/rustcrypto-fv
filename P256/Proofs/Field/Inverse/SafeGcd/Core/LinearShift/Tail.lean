import P256.Proofs.Field.Inverse.SafeGcd.Core.LinearCombination.Blocks.Basic
import P256.Proofs.Field.Inverse.SafeGcd.Core.LinearShift.Defs

namespace P256.Proofs.Field.Inverse.SafeGcd.Core.LinearShift.Tail

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift P256.Proofs.Refine Prelude

inductive Label where | first | second | third | finish

def program : Program Support.Op Label (fun _ => 0) 0 where
  blocks
  | .first => .terminate (.br ⟨.second, #v[]⟩)
  | .second => .terminate (.br ⟨.third, #v[]⟩)
  | .third => .terminate (.br ⟨.finish, #v[]⟩)
  | .finish => .terminate (.ret #v[])

def dialect : Dialect Support.Op Unit Inputs where
  eval op := nomatch op
  truth _ := false

@[refine_layout] def start : Label → Machine.Label
  | .first => .l1170c6 | .second => .l1170d6 | .third => .l1170db | .finish => .l1170e3

@[refine_layout] def atoms (l : Label) (fr : Activation) (controls : RamState) (p : Inputs) : List Atom :=
  linearReturned fr controls p ++ match l with
    | .first => []
    | _ => [.gpr 0 ((64 - p.shift : BitVec 32).setWidth 64)]

@[refine_layout] def outputWords (p : Inputs) : Vector (BitVec 64) 4 :=
  #v[(LinearCombination.resultWords p.linear)[0] >>> p.shift.toNat |||
        (LinearCombination.resultWords p.linear)[1] <<< (64 - p.shift.toNat),
       (LinearCombination.resultWords p.linear)[1] >>> p.shift.toNat |||
        (LinearCombination.resultWords p.linear)[2] <<< (64 - p.shift.toNat),
       (LinearCombination.resultWords p.linear)[2] >>> p.shift.toNat |||
        (LinearCombination.resultWords p.linear)[3] <<< (64 - p.shift.toNat),
       (LinearCombination.resultWords p.linear)[3] >>> p.shift.toNat |||
        (LinearCombination.resultWords p.linear)[4] <<< (64 - p.shift.toNat)]

@[refine_layout] def outputAtoms (fr : Activation) (controls : RamState) (p : Inputs) : List Atom :=
  Machine.Shift.doneAt fr ++
  [.words fr.rdi 64 (outputWords p), .mem (fr.rdi + 32) 8 (resultSign p), .readable fr.rdi 33,
      .reg 39 ⟨32, controls.MXCSR⟩, .reg 51 ⟨16, controls.FP87_Control⟩]

def layout (fr : Activation) (controls : RamState) : Layout program dialect Machine.lifted Unit where
  start := start
  Params _ := Inputs
  args _ _ := #v[]
  store _ p := p
  atoms l _ p := atoms l fr controls p
  Result := Inputs
  output p := ⟨#v[], none, p⟩
  done _ p := outputAtoms fr controls p
  retAddr _ := fr.ret
  original _ := fr.original
  regions _ := [fr.region, outputRegion fr]

attribute [local cfg_eval] Operand.read_reg_get

set_option maxHeartbeats 1000000 in
theorem first_block (code : CodeMap) (fr : Activation) (controls : RamState) :
    (layout fr controls).BlockSimulation code .first := by
  x86_refine []
  all_goals bv_omega

set_option maxHeartbeats 1000000 in
theorem second_block (code : CodeMap) (fr : Activation) (controls : RamState) :
    (layout fr controls).BlockSimulation code .second := by
  x86_refine []
  all_goals bv_omega

set_option maxHeartbeats 1000000 in
theorem third_block (code : CodeMap) (fr : Activation) (controls : RamState) :
    (layout fr controls).BlockSimulation code .third := by
  x86_refine []
  all_goals bv_omega

macro "shift_output_store" fr:ident mem:ident hc:ident : tactic =>
  `(tactic| first
    | (apply P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.CrossPage.StoreOk.of_region (b := ($fr).rdi) (len := 33)
       · repeat' first | assumption | apply Writable.memStore
       · refine_arith
       · refine_arith
       · apply P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.writable_codeApart (mem := $mem) _ $hc (by decide) (by decide)
         apply Writable.sub (b := ($fr).rdi) (len := 33)
         · repeat' first | assumption | apply Writable.memStore
         · refine_arith
         · refine_arith)
    | (apply StoreOk.of_region (b := ($fr).rdi) (len := 33)
       · repeat' first | assumption | apply Writable.memStore
       · refine_arith
       · refine_arith
       · apply P256.Proofs.Field.Inverse.SafeGcd.Correction.Execution.writable_codeApart (mem := $mem) _ $hc (by decide) (by decide)
         apply Writable.sub (b := ($fr).rdi) (len := 33)
         · repeat' first | assumption | apply Writable.memStore
         · refine_arith
         · refine_arith))

theorem count_eq (s : BitVec 32) (h : s.toNat < 64) :
    shiftCount 64 (s.setWidth 8) = s.toNat := by
  simp only [shiftCount, ↓reduceIte, BitVec.toNat_setWidth]
  omega

theorem complement_nat (s : BitVec 32) (h : s.toNat < 64) :
    (64 - s : BitVec 32).toNat = 64 - s.toNat := by
  bv_omega

theorem shiftedWords_eq (p : Inputs) : shiftedWords p =
    #v[(LinearCombination.resultWords p.linear)[0] >>> p.shift.toNat |||
        (LinearCombination.resultWords p.linear)[1] <<< (64 - p.shift.toNat),
       (LinearCombination.resultWords p.linear)[1] >>> p.shift.toNat |||
        (LinearCombination.resultWords p.linear)[2] <<< (64 - p.shift.toNat),
       (LinearCombination.resultWords p.linear)[2] >>> p.shift.toNat |||
        (LinearCombination.resultWords p.linear)[3] <<< (64 - p.shift.toNat),
       (LinearCombination.resultWords p.linear)[3] >>> p.shift.toNat |||
        (LinearCombination.resultWords p.linear)[4] <<< (64 - p.shift.toNat)] := by
  apply Vector.ext
  intro i hi
  have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  rcases h with rfl | rfl | rfl | rfl <;> rfl

set_option maxHeartbeats 1500000 in
theorem finish_block (code : CodeMap) (hcode : ∀ x ∈ Machine.fnCode, x ∈ code)
    (fr : Activation) (controls : RamState) : (layout fr controls).BlockSimulation code .finish := by
  refine_intro
  have hc := count_eq shift atom20
  have hd := count_eq (64 - shift) (by rw [complement_nat shift atom20]; omega)
  rw [complement_nat shift atom20] at hd
  refine_uir []
  all_goals refine_lifted [Correction.low_byte, Correction.byte_extend,
    setWidth_mergeGPR8]
  all_goals try refine_close [outputWords, outputRegion, hc, hd]
  all_goals try simp only [cfg_eval, BitVec.reduceSetWidth, BitVec.reduceSignExtend,
    BitVec.reduceEq, ite_false, ite_true, Value.get_mk_setWidth, BitVec.setWidth_eq]
  all_goals try shift_output_store fr mem hcode
  all_goals intro i hi
  all_goals have h : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 := by omega
  all_goals rcases h with rfl | rfl | rfl | rfl
  all_goals simp only [wordAddr, Vector.getElem_mk, Array.reduceGetElem]
  all_goals refine_norm [hc, hd]
  all_goals simp only [Nat.reduceMul, BitVec.add_zero]
  all_goals rw [memLoad_memStore_eq _ _ (by rfl) (by decide) (by decide)]
  all_goals simp only [word0, word1, word2, word3, word4, hc, hd]


end P256.Proofs.Field.Inverse.SafeGcd.Core.LinearShift.Tail
