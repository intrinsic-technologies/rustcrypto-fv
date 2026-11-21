import AesGcm.Proofs.Machine.Fixslice.Memory
import AesGcm.Proofs.Machine.Fixslice.Operations
import AesGcm.Proofs.Machine.LIR.Fn10a690.Frame
import AesGcm.Proofs.Machine.LIR.Program
import AesGcm.Proofs.Machine.Runtime.Guards
import AesGcm.Proofs.Copied.X86Proofs.Lift.Generated.Values
import AesGcm.Proofs.Machine.Runtime.Contracts
import AesGcm.Proofs.Machine.Fixslice.Conversion
import AesGcm.Proofs.Copied.X86Proofs.Refine.Frame
import AesGcm.Proofs.Copied.X86Proofs.Refine.Lemma.Store

namespace AesGcm.Proofs.Machine.AES64

open AesGcm.Proofs.Machine.Fixslice AesGcm.Proofs.Machine.Runtime
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift
  X86Proofs.Refine

theorem byte_shift32_eq (b : BitVec 8) (s : Nat) (hs : s ≤ 24) :
    (((b.setWidth 32) <<< s).setWidth 64) = (b.setWidth 64) <<< s := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_shiftLeft, hi, decide_true,
    Bool.true_and]
  by_cases h : i < s
  · simp only [h, decide_true, Bool.not_true, Bool.false_and, Bool.and_false]
  · have his : s ≤ i := by omega
    by_cases hi32 : i < 32
    · simp only [hi32, decide_true, h, decide_false, Bool.not_false, Bool.true_and]
      have h64 : i - s < 64 := by omega
      have h32 : i - s < 32 := by omega
      simp only [h64, h32, decide_true, Bool.true_and]
    · have hib : 8 ≤ i - s := by omega
      simp only [hi32, decide_false, Bool.false_and, h, Bool.not_false,
        BitVec.getLsbD_of_ge _ _ hib, Bool.and_false]

theorem add_self_eq_shift (a : BitVec 64) : a + a = a <<< (1 : Nat) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_add, BitVec.toNat_shiftLeft, Nat.shiftLeft_eq]
  congr 1
  omega

theorem bitvec_or_left_comm (a b c : BitVec 64) :
    a ||| (b ||| c) = b ||| (a ||| c) := by
  rw [← BitVec.or_assoc, BitVec.or_comm a b, BitVec.or_assoc]

theorem assembly_pack_eq (b : Fin 8 → BitVec 8) :
    (b 7).setWidth 64 <<< (56 : Nat) |||
      ((b 5).setWidth 64 <<< (40 : Nat) |||
        (((b 3).setWidth 32 <<< (24 : Nat)).setWidth 64 |||
          (((b 1).setWidth 32 <<< (8 : Nat)).setWidth 64 |||
            ((b 6).setWidth 64 <<< (48 : Nat) |||
              ((b 4).setWidth 64 <<< (32 : Nat) |||
                ((b 0).setWidth 64 |||
                  ((b 2).setWidth 32 <<< (16 : Nat)).setWidth 64)))))) =
      packBytes b := by
  rw [byte_shift32_eq _ _ (by decide), byte_shift32_eq _ _ (by decide),
    byte_shift32_eq _ _ (by decide)]
  simp only [packBytes, BitVec.or_assoc, BitVec.or_comm, bitvec_or_left_comm]


def assemblyInputWords (x : Planes) : Planes :=
  let t01 := ((x 0 >>> (1 : Nat)) ^^^ x 1) &&& 0x5555555555555555
  let a1 := x 1 ^^^ t01
  let t23 := ((x 2 >>> (1 : Nat)) ^^^ x 3) &&& 0x5555555555555555
  let a3 := x 3 ^^^ t23
  let t45 := ((x 4 >>> (1 : Nat)) ^^^ x 5) &&& 0x5555555555555555
  let t67 := ((x 6 >>> (1 : Nat)) ^^^ x 7) &&& 0x5555555555555555
  let t13 := ((a1 >>> (2 : Nat)) ^^^ a3) &&& 0x3333333333333333
  let b3 := a3 ^^^ t13
  let a5 := x 5 ^^^ t45
  let a7 := x 7 ^^^ t67
  let t57 := ((a5 >>> (2 : Nat)) ^^^ a7) &&& 0x3333333333333333
  let b7 := a7 ^^^ t57
  let t37 := ((b3 >>> (4 : Nat)) ^^^ b7) &&& 0x0f0f0f0f0f0f0f0f
  let o3 := (t37 <<< (4 : Nat)) ^^^ b3
  let o7 := t37 ^^^ b7
  let a0 := (t01 + t01) ^^^ x 0
  let a2 := (t23 + t23) ^^^ x 2
  let a4 := (t45 + t45) ^^^ x 4
  let t02 := ((a0 >>> (2 : Nat)) ^^^ a2) &&& 0x3333333333333333
  let b2 := a2 ^^^ t02
  let a6 := (t67 + t67) ^^^ x 6
  let t46 := ((a4 >>> (2 : Nat)) ^^^ a6) &&& 0x3333333333333333
  let b6 := a6 ^^^ t46
  let t26 := ((b2 >>> (4 : Nat)) ^^^ b6) &&& 0x0f0f0f0f0f0f0f0f
  let o2 := (t26 <<< (4 : Nat)) ^^^ b2
  let o6 := t26 ^^^ b6
  let b1 := (t13 <<< (2 : Nat)) ^^^ a1
  let b5 := (t57 <<< (2 : Nat)) ^^^ a5
  let t15 := ((b1 >>> (4 : Nat)) ^^^ b5) &&& 0x0f0f0f0f0f0f0f0f
  let o1 := (t15 <<< (4 : Nat)) ^^^ b1
  let o5 := t15 ^^^ b5
  let b0 := (t02 <<< (2 : Nat)) ^^^ a0
  let b4 := (t46 <<< (2 : Nat)) ^^^ a4
  let t04 := ((b0 >>> (4 : Nat)) ^^^ b4) &&& 0x0f0f0f0f0f0f0f0f
  let o0 := (t04 <<< (4 : Nat)) ^^^ b0
  let o4 := t04 ^^^ b4
  fun p ↦ match p.val with
  | 0 => o0
  | 1 => o1
  | 2 => o2
  | 3 => o3
  | 4 => o4
  | 5 => o5
  | 6 => o6
  | _ => o7

theorem assemblyInputWords_eq (x : Planes) : assemblyInputWords x = bitsliceSwaps x := by
  unfold assemblyInputWords
  extract_lets t01 a1 t23 a3 t45 t67 t13 b3 a5 a7 t57 b7 t37 o3 o7 a0 a2 a4 t02 b2 a6 t46 b6 t26 o2 o6 b1 b5 t15 o1 o5 b0 b4 t04 o0 o4
  let y := swapStage 0 x
  let z := swapStage 1 y
  have ha0 : a0 = y 0 := by
    change a0 = (deltaSwap2 (x 1) (x 0) 1 0x5555555555555555).2
    simp only [a0, t01, deltaSwap2, add_self_eq_shift]
    rw [BitVec.xor_comm (x 0 >>> (1 : Nat)) (x 1)]
    exact BitVec.xor_comm _ _
  have ha1 : a1 = y 1 := by
    change a1 = (deltaSwap2 (x 1) (x 0) 1 0x5555555555555555).1
    simp only [a1, t01, deltaSwap2]
    rw [BitVec.xor_comm (x 0 >>> (1 : Nat)) (x 1)]
  have ha2 : a2 = y 2 := by
    change a2 = (deltaSwap2 (x 3) (x 2) 1 0x5555555555555555).2
    simp only [a2, t23, deltaSwap2, add_self_eq_shift]
    rw [BitVec.xor_comm (x 2 >>> (1 : Nat)) (x 3)]
    exact BitVec.xor_comm _ _
  have ha3 : a3 = y 3 := by
    change a3 = (deltaSwap2 (x 3) (x 2) 1 0x5555555555555555).1
    simp only [a3, t23, deltaSwap2]
    rw [BitVec.xor_comm (x 2 >>> (1 : Nat)) (x 3)]
  have ha4 : a4 = y 4 := by
    change a4 = (deltaSwap2 (x 5) (x 4) 1 0x5555555555555555).2
    simp only [a4, t45, deltaSwap2, add_self_eq_shift]
    rw [BitVec.xor_comm (x 4 >>> (1 : Nat)) (x 5)]
    exact BitVec.xor_comm _ _
  have ha5 : a5 = y 5 := by
    change a5 = (deltaSwap2 (x 5) (x 4) 1 0x5555555555555555).1
    simp only [a5, t45, deltaSwap2]
    rw [BitVec.xor_comm (x 4 >>> (1 : Nat)) (x 5)]
  have ha6 : a6 = y 6 := by
    change a6 = (deltaSwap2 (x 7) (x 6) 1 0x5555555555555555).2
    simp only [a6, t67, deltaSwap2, add_self_eq_shift]
    rw [BitVec.xor_comm (x 6 >>> (1 : Nat)) (x 7)]
    exact BitVec.xor_comm _ _
  have ha7 : a7 = y 7 := by
    change a7 = (deltaSwap2 (x 7) (x 6) 1 0x5555555555555555).1
    simp only [a7, t67, deltaSwap2]
    rw [BitVec.xor_comm (x 6 >>> (1 : Nat)) (x 7)]
  have hb0 : b0 = z 0 := by
    change b0 = (deltaSwap2 (y 2) (y 0) 2 0x3333333333333333).2
    simp only [b0, t02, ha0, ha2, deltaSwap2]
    rw [BitVec.xor_comm (y 0 >>> (2 : Nat)) (y 2)]
    exact BitVec.xor_comm _ _
  have hb1 : b1 = z 1 := by
    change b1 = (deltaSwap2 (y 3) (y 1) 2 0x3333333333333333).2
    simp only [b1, t13, ha1, ha3, deltaSwap2]
    rw [BitVec.xor_comm (y 1 >>> (2 : Nat)) (y 3)]
    exact BitVec.xor_comm _ _
  have hb2 : b2 = z 2 := by
    change b2 = (deltaSwap2 (y 2) (y 0) 2 0x3333333333333333).1
    simp only [b2, t02, ha0, ha2, deltaSwap2]
    rw [BitVec.xor_comm (y 0 >>> (2 : Nat)) (y 2)]
  have hb3 : b3 = z 3 := by
    change b3 = (deltaSwap2 (y 3) (y 1) 2 0x3333333333333333).1
    simp only [b3, t13, ha1, ha3, deltaSwap2]
    rw [BitVec.xor_comm (y 1 >>> (2 : Nat)) (y 3)]
  have hb4 : b4 = z 4 := by
    change b4 = (deltaSwap2 (y 6) (y 4) 2 0x3333333333333333).2
    simp only [b4, t46, ha4, ha6, deltaSwap2]
    rw [BitVec.xor_comm (y 4 >>> (2 : Nat)) (y 6)]
    exact BitVec.xor_comm _ _
  have hb5 : b5 = z 5 := by
    change b5 = (deltaSwap2 (y 7) (y 5) 2 0x3333333333333333).2
    simp only [b5, t57, ha5, ha7, deltaSwap2]
    rw [BitVec.xor_comm (y 5 >>> (2 : Nat)) (y 7)]
    exact BitVec.xor_comm _ _
  have hb6 : b6 = z 6 := by
    change b6 = (deltaSwap2 (y 6) (y 4) 2 0x3333333333333333).1
    simp only [b6, t46, ha4, ha6, deltaSwap2]
    rw [BitVec.xor_comm (y 4 >>> (2 : Nat)) (y 6)]
  have hb7 : b7 = z 7 := by
    change b7 = (deltaSwap2 (y 7) (y 5) 2 0x3333333333333333).1
    simp only [b7, t57, ha5, ha7, deltaSwap2]
    rw [BitVec.xor_comm (y 5 >>> (2 : Nat)) (y 7)]
  have ho0 : o0 = swapStage 2 z 0 := by
    change o0 = (deltaSwap2 (z 4) (z 0) 4 0x0f0f0f0f0f0f0f0f).2
    simp only [o0, t04, hb0, hb4, deltaSwap2]
    rw [BitVec.xor_comm (z 0 >>> (4 : Nat)) (z 4)]
    exact BitVec.xor_comm _ _
  have ho1 : o1 = swapStage 2 z 1 := by
    change o1 = (deltaSwap2 (z 5) (z 1) 4 0x0f0f0f0f0f0f0f0f).2
    simp only [o1, t15, hb1, hb5, deltaSwap2]
    rw [BitVec.xor_comm (z 1 >>> (4 : Nat)) (z 5)]
    exact BitVec.xor_comm _ _
  have ho2 : o2 = swapStage 2 z 2 := by
    change o2 = (deltaSwap2 (z 6) (z 2) 4 0x0f0f0f0f0f0f0f0f).2
    simp only [o2, t26, hb2, hb6, deltaSwap2]
    rw [BitVec.xor_comm (z 2 >>> (4 : Nat)) (z 6)]
    exact BitVec.xor_comm _ _
  have ho3 : o3 = swapStage 2 z 3 := by
    change o3 = (deltaSwap2 (z 7) (z 3) 4 0x0f0f0f0f0f0f0f0f).2
    simp only [o3, t37, hb3, hb7, deltaSwap2]
    rw [BitVec.xor_comm (z 3 >>> (4 : Nat)) (z 7)]
    exact BitVec.xor_comm _ _
  have ho4 : o4 = swapStage 2 z 4 := by
    change o4 = (deltaSwap2 (z 4) (z 0) 4 0x0f0f0f0f0f0f0f0f).1
    simp only [o4, t04, hb0, hb4, deltaSwap2]
    rw [BitVec.xor_comm (z 0 >>> (4 : Nat)) (z 4)]
    exact BitVec.xor_comm _ _
  have ho5 : o5 = swapStage 2 z 5 := by
    change o5 = (deltaSwap2 (z 5) (z 1) 4 0x0f0f0f0f0f0f0f0f).1
    simp only [o5, t15, hb1, hb5, deltaSwap2]
    rw [BitVec.xor_comm (z 1 >>> (4 : Nat)) (z 5)]
    exact BitVec.xor_comm _ _
  have ho6 : o6 = swapStage 2 z 6 := by
    change o6 = (deltaSwap2 (z 6) (z 2) 4 0x0f0f0f0f0f0f0f0f).1
    simp only [o6, t26, hb2, hb6, deltaSwap2]
    rw [BitVec.xor_comm (z 2 >>> (4 : Nat)) (z 6)]
    exact BitVec.xor_comm _ _
  have ho7 : o7 = swapStage 2 z 7 := by
    change o7 = (deltaSwap2 (z 7) (z 3) 4 0x0f0f0f0f0f0f0f0f).1
    simp only [o7, t37, hb3, hb7, deltaSwap2]
    rw [BitVec.xor_comm (z 3 >>> (4 : Nat)) (z 7)]
    exact BitVec.xor_comm _ _
  funext p
  change (match p.val with
    | 0 => o0 | 1 => o1 | 2 => o2 | 3 => o3
    | 4 => o4 | 5 => o5 | 6 => o6 | _ => o7) = swapStage 2 z p
  have hp : p.val = 0 ∨ p.val = 1 ∨ p.val = 2 ∨ p.val = 3 ∨
      p.val = 4 ∨ p.val = 5 ∨ p.val = 6 ∨ p.val = 7 := by omega
  rcases hp with hp | hp | hp | hp | hp | hp | hp | hp
  · have he : p = (0 : Fin 8) := Fin.ext hp
    subst p
    exact ho0
  · have he : p = (1 : Fin 8) := Fin.ext hp
    subst p
    exact ho1
  · have he : p = (2 : Fin 8) := Fin.ext hp
    subst p
    exact ho2
  · have he : p = (3 : Fin 8) := Fin.ext hp
    subst p
    exact ho3
  · have he : p = (4 : Fin 8) := Fin.ext hp
    subst p
    exact ho4
  · have he : p = (5 : Fin 8) := Fin.ext hp
    subst p
    exact ho5
  · have he : p = (6 : Fin 8) := Fin.ext hp
    subst p
    exact ho6
  · have he : p = (7 : Fin 8) := Fin.ext hp
    subst p
    exact ho7


def assemblyPackRead (b : Fin 16 → BitVec 8) (h : Fin 2) : BitVec 64 :=
  (b ⟨4 * h.val + 11, by omega⟩).setWidth 64 <<< (56 : Nat) |||
    ((b ⟨4 * h.val + 10, by omega⟩).setWidth 64 <<< (40 : Nat) |||
      (((b ⟨4 * h.val + 9, by omega⟩).setWidth 32 <<< (24 : Nat)).setWidth 64 |||
        (((b ⟨4 * h.val + 8, by omega⟩).setWidth 32 <<< (8 : Nat)).setWidth 64 |||
          ((b ⟨4 * h.val + 3, by omega⟩).setWidth 64 <<< (48 : Nat) |||
            ((b ⟨4 * h.val + 2, by omega⟩).setWidth 64 <<< (32 : Nat) |||
              ((b ⟨4 * h.val, by omega⟩).setWidth 64 |||
                ((b ⟨4 * h.val + 1, by omega⟩).setWidth 32 <<< (16 : Nat)).setWidth 64))))))

theorem assemblyPackRead_eq (b : Fin 16 → BitVec 8) (h : Fin 2) :
    assemblyPackRead b h = readReordered b h := by
  simpa [assemblyPackRead, readReordered, Nat.add_assoc,
    show (0 : Fin 8).val = 0 from rfl,
    show (1 : Fin 8).val = 1 from rfl,
    show (2 : Fin 8).val = 2 from rfl,
    show (3 : Fin 8).val = 3 from rfl,
    show (4 : Fin 8).val = 4 from rfl,
    show (5 : Fin 8).val = 5 from rfl,
    show (6 : Fin 8).val = 6 from rfl,
    show (7 : Fin 8).val = 7 from rfl] using
    assembly_pack_eq (fun q ↦ b ⟨4 * h.val + 8 * (q.val % 2) + q.val / 2, by omega⟩)

def assemblyPacking (x : Blocks) : Planes := fun p ↦
  assemblyPackRead (x ⟨p.val % 4, by omega⟩) ⟨p.val / 4, by omega⟩

theorem assemblyPacking_eq (x : Blocks) : assemblyPacking x = inputPacking x := by
  funext p
  exact assemblyPackRead_eq _ _

theorem assemblyInputWords_bitslice (x : Blocks) :
    assemblyInputWords (assemblyPacking x) = bitslice x := by
  rw [assemblyPacking_eq, assemblyInputWords_eq]
  rfl


def inputSavedMemory (fr : Activation) : Ram :=
  memStore (memStore (memStore (memStore (memStore (memStore fr.original
    (fr.rsp - 8) fr.rbp) (fr.rsp - 16) fr.r15) (fr.rsp - 24) fr.r14)
    (fr.rsp - 32) fr.r13) (fr.rsp - 40) fr.r12) (fr.rsp - 48) fr.rbx

theorem inputStackLoad_store (m : Ram) (rsp : BitVec 64) (i j : Fin 10) (v : BitVec 64) :
    memLoad (memStore m (rsp - BitVec.ofNat 64 (8 * i.val)) v)
      (rsp - BitVec.ofNat 64 (8 * j.val)) 64 =
        if i = j then v else memLoad m (rsp - BitVec.ofNat 64 (8 * j.val)) 64 := by
  by_cases h : i = j
  · subst j
    simp only [ite_true]
    exact memLoad_memStore_same m _ v (by decide) (by decide)
  · simp only [h, ↓reduceIte]
    apply memLoad_memStore_of_rangeApart
    apply RangeApart.of_offsets (addr_sub _ _) (addr_sub _ _)
    have hp : ∀ (i j : Fin 10), i ≠ j →
        8 ≤ ((0 - BitVec.ofNat 64 (8 * j.val)) -
          (0 - BitVec.ofNat 64 (8 * i.val))).toNat ∧
        8 ≤ ((0 - BitVec.ofNat 64 (8 * i.val)) -
          (0 - BitVec.ofNat 64 (8 * j.val))).toNat := by decide +kernel
    exact hp i j h

def inputSavedValue (fr : Activation) (j : Fin 7) : BitVec 64 :=
  match j.val with
  | 0 => memLoad fr.original fr.rsp 64
  | 1 => fr.rbp
  | 2 => fr.r15
  | 3 => fr.r14
  | 4 => fr.r13
  | 5 => fr.r12
  | _ => fr.rbx

theorem inputSavedMemory_memLoad (fr : Activation) (j : Fin 7) :
    memLoad (inputSavedMemory fr) (fr.rsp - BitVec.ofNat 64 (8 * j.val)) 64 =
      inputSavedValue fr j := by
  have h6 (m : Ram) : memLoad (memStore m (fr.rsp - 48) fr.rbx)
      (fr.rsp - BitVec.ofNat 64 (8 * j.val)) 64 =
        if 6 = j.val then fr.rbx else
          memLoad m (fr.rsp - BitVec.ofNat 64 (8 * j.val)) 64 := by
    have h := inputStackLoad_store m fr.rsp ⟨6, by decide⟩ ⟨j.val, by omega⟩ fr.rbx
    simp only [Fin.ext_iff] at h
    exact h
  have h5 (m : Ram) : memLoad (memStore m (fr.rsp - 40) fr.r12)
      (fr.rsp - BitVec.ofNat 64 (8 * j.val)) 64 =
        if 5 = j.val then fr.r12 else
          memLoad m (fr.rsp - BitVec.ofNat 64 (8 * j.val)) 64 := by
    have h := inputStackLoad_store m fr.rsp ⟨5, by decide⟩ ⟨j.val, by omega⟩ fr.r12
    simp only [Fin.ext_iff] at h
    exact h
  have h4 (m : Ram) : memLoad (memStore m (fr.rsp - 32) fr.r13)
      (fr.rsp - BitVec.ofNat 64 (8 * j.val)) 64 =
        if 4 = j.val then fr.r13 else
          memLoad m (fr.rsp - BitVec.ofNat 64 (8 * j.val)) 64 := by
    have h := inputStackLoad_store m fr.rsp ⟨4, by decide⟩ ⟨j.val, by omega⟩ fr.r13
    simp only [Fin.ext_iff] at h
    exact h
  have h3 (m : Ram) : memLoad (memStore m (fr.rsp - 24) fr.r14)
      (fr.rsp - BitVec.ofNat 64 (8 * j.val)) 64 =
        if 3 = j.val then fr.r14 else
          memLoad m (fr.rsp - BitVec.ofNat 64 (8 * j.val)) 64 := by
    have h := inputStackLoad_store m fr.rsp ⟨3, by decide⟩ ⟨j.val, by omega⟩ fr.r14
    simp only [Fin.ext_iff] at h
    exact h
  have h2 (m : Ram) : memLoad (memStore m (fr.rsp - 16) fr.r15)
      (fr.rsp - BitVec.ofNat 64 (8 * j.val)) 64 =
        if 2 = j.val then fr.r15 else
          memLoad m (fr.rsp - BitVec.ofNat 64 (8 * j.val)) 64 := by
    have h := inputStackLoad_store m fr.rsp ⟨2, by decide⟩ ⟨j.val, by omega⟩ fr.r15
    simp only [Fin.ext_iff] at h
    exact h
  have h1 (m : Ram) : memLoad (memStore m (fr.rsp - 8) fr.rbp)
      (fr.rsp - BitVec.ofNat 64 (8 * j.val)) 64 =
        if 1 = j.val then fr.rbp else
          memLoad m (fr.rsp - BitVec.ofNat 64 (8 * j.val)) 64 := by
    have h := inputStackLoad_store m fr.rsp ⟨1, by decide⟩ ⟨j.val, by omega⟩ fr.rbp
    simp only [Fin.ext_iff] at h
    exact h
  simp only [inputSavedMemory, h6, h5, h4, h3, h2, h1]
  have h : j.val = 0 ∨ j.val = 1 ∨ j.val = 2 ∨ j.val = 3 ∨ j.val = 4 ∨
      j.val = 5 ∨ j.val = 6 := by omega
  rcases h with h | h | h | h | h | h | h <;>
    simp [inputSavedValue, h]



theorem inputSavedMemory_frame (fr : Activation)
    (hroom : fr.low.toNat + 0x30 ≤ fr.rsp.toNat) :
    RamWriteFrame fr.original (inputSavedMemory fr) [fr.region] := by
  have hin (k : Nat) (hk0 : 8 ≤ k) (hk1 : k ≤ 0x30) :
      InRegions [fr.region] (fr.rsp - BitVec.ofNat 64 k) 8 := by
    have hkn : k < 2 ^ 64 := by omega
    have hle : BitVec.ofNat 64 k ≤ fr.rsp := by
      change (BitVec.ofNat 64 k).toNat ≤ fr.rsp.toNat
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hkn]
      omega
    have he : (fr.rsp - BitVec.ofNat 64 k).toNat = fr.rsp.toNat - k := by
      rw [BitVec.toNat_sub_of_le hle, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hkn]
    refine ⟨fr.region, by simp, ?_⟩
    simp only [InRegion, Activation.region, he]
    have := fr.rsp.isLt
    omega
  have h1 := (RamWriteFrame.refl fr.original [fr.region]).memStore fr.rbp
    (hin 8 (by decide) (by decide))
  have h2 := h1.memStore fr.r15 (hin 16 (by decide) (by decide))
  have h3 := h2.memStore fr.r14 (hin 24 (by decide) (by decide))
  have h4 := h3.memStore fr.r13 (hin 32 (by decide) (by decide))
  have h5 := h4.memStore fr.r12 (hin 40 (by decide) (by decide))
  exact h5.memStore fr.rbx (hin 48 (by decide) (by decide))



def inputStoredPlanes (m : Ram) (a : BitVec 64) (x : Planes) : Ram :=
  memStore (memStore (memStore (memStore (memStore (memStore (memStore (memStore m
    (wordAddr a 64 0) (x 0)) (wordAddr a 64 1) (x 1)) (wordAddr a 64 2) (x 2))
    (wordAddr a 64 3) (x 3)) (wordAddr a 64 4) (x 4)) (wordAddr a 64 5) (x 5))
    (wordAddr a 64 6) (x 6)) (wordAddr a 64 7) (x 7)

theorem inputPlaneLoad_store (m : Ram) (a : BitVec 64) (i j : Nat)
    (hi : i < 8) (hj : j < 8) (v : BitVec 64) :
    memLoad (memStore m (wordAddr a 64 i) v) (wordAddr a 64 j) 64 =
      if i = j then v else memLoad m (wordAddr a 64 j) 64 := by
  by_cases h : i = j
  · subst j
    simp only [ite_true]
    exact memLoad_memStore_same m _ v (by decide) (by decide)
  · simp only [h, ↓reduceIte]
    apply memLoad_memStore_of_rangeApart
    apply RangeApart.of_offsets rfl rfl
    have hp : ∀ (i j : Fin 8), i ≠ j →
        8 ≤ (BitVec.ofNat 64 (8 * j.val) - BitVec.ofNat 64 (8 * i.val)).toNat ∧
        8 ≤ (BitVec.ofNat 64 (8 * i.val) - BitVec.ofNat 64 (8 * j.val)).toNat :=
      by decide +kernel
    exact hp ⟨i, hi⟩ ⟨j, hj⟩ (fun he ↦ h (congrArg Fin.val he))

theorem inputStoredPlanes_memLoad (m : Ram) (a : BitVec 64) (x : Planes) (p : Fin 8) :
    memLoad (inputStoredPlanes m a x) (a + BitVec.ofNat 64 (8 * p.val)) 64 = x p := by
  change memLoad (inputStoredPlanes m a x) (wordAddr a 64 p.val) 64 = x p
  simp (disch := omega) only [inputStoredPlanes, inputPlaneLoad_store]
  have hp : p.val = 0 ∨ p.val = 1 ∨ p.val = 2 ∨ p.val = 3 ∨ p.val = 4 ∨
      p.val = 5 ∨ p.val = 6 ∨ p.val = 7 := by omega
  rcases hp with h | h | h | h | h | h | h | h <;>
    simp only [h, Nat.reduceEqDiff, ite_true, ite_false]
  all_goals congr 1 <;> exact Fin.ext h.symm



theorem inputStoredPlanes_frame {original m : Ram} {a : BitVec 64}
    {regions : List MemoryRegion} (x : Planes) (hf : RamWriteFrame original m regions)
    (hin : InRegions regions a 64) :
    RamWriteFrame original (inputStoredPlanes m a x) regions := by
  obtain ⟨r, hr, hlo, hhi, hwrap⟩ := hin
  have hp (p : Nat) (h : p < 8) : InRegions regions (wordAddr a 64 p) 8 := by
    have he : (wordAddr a 64 p).toNat = a.toNat + 8 * p := by
      simp only [wordAddr, BitVec.toNat_add, BitVec.toNat_ofNat]
      rw [Nat.mod_eq_of_lt (a := 8 * p) (by omega), Nat.mod_eq_of_lt (by omega)]
    refine ⟨r, hr, ?_⟩
    simp only [InRegion, he]
    omega
  exact ((((((((hf.memStore (x 0) (hp 0 (by decide))).memStore (x 1)
    (hp 1 (by decide))).memStore (x 2) (hp 2 (by decide))).memStore (x 3)
    (hp 3 (by decide))).memStore (x 4) (hp 4 (by decide))).memStore (x 5)
    (hp 5 (by decide))).memStore (x 6) (hp 6 (by decide))).memStore (x 7)
    (hp 7 (by decide)))




set_option maxRecDepth 4096 in
theorem inputInstruction_code (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) (p len : Nat)
    (hp : 0x10a690 ≤ p) (hend : p + len ≤ 0x10aa99) :
    ∀ j < len, ∃ b, (BitVec.ofNat 64 p + BitVec.ofNat 64 j, b) ∈ code := by
  intro j hj
  by_cases h : p + j < 0x10a6a8
  · let k := p + j - 0x10a690
    have hoff : k < LIR.bytes_l10a690.length := by
      change p + j - 0x10a690 < 24
      omega
    have hm := hcode _ (LIR.code_l10a690 _
      (mem_codeRange 0x10a690 LIR.bytes_l10a690 k hoff))
    have he : BitVec.ofNat 64 p + BitVec.ofNat 64 j =
        (0x10a690 : BitVec 64) + BitVec.ofNat 64 k := by
      change BitVec.ofNat 64 p + BitVec.ofNat 64 j =
        BitVec.ofNat 64 0x10a690 + BitVec.ofNat 64 k
      simp only [← BitVec.ofNat_add]
      apply congrArg (BitVec.ofNat 64)
      omega
    rw [he]
    exact Exists.intro _ hm
  · let k := p + j - 0x10a6a8
    have hoff : k < LIR.bytes_l10a6a8.length := by
      change p + j - 0x10a6a8 < 0x3f1
      omega
    have hm := hcode _ (LIR.code_l10a6a8 _
      (mem_codeRange 0x10a6a8 LIR.bytes_l10a6a8 k hoff))
    have he : BitVec.ofNat 64 p + BitVec.ofNat 64 j =
        (0x10a6a8 : BitVec 64) + BitVec.ofNat 64 k := by
      change BitVec.ofNat 64 p + BitVec.ofNat 64 j =
        BitVec.ofNat 64 0x10a6a8 + BitVec.ofNat 64 k
      simp only [← BitVec.ofNat_add]
      apply congrArg (BitVec.ofNat 64)
      omega
    rw [he]
    exact Exists.intro _ hm

theorem input_store_guard {code : CodeMap} {mem : Ram} {a : BitVec 64} {len : Nat}
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) (p size : Nat)
    (hp : 0x10a690 ≤ p) (hend : p + size ≤ 0x10aa99)
    (hw : Writable code mem a len) :
    StoreOk code mem a len (BitVec.ofNat 64 p) size := by
  apply storeOk_of_writable hw
  intro i hi j hj he
  obtain ⟨b, hb⟩ := inputInstruction_code code hcode p size hp hend j hj
  exact hw.notCode _ hb i hi he.symm

theorem_by inputEntry_eval (code : CodeMap) (args : Values Value Reg.count) (mem : Ram) :
    LIR.program.runBlock (dialect code) ⟨.l10a690, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

theorem inputEntry_runBlock (code : CodeMap) (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (args : Values Value Reg.count) (fr : Activation)
    (hsp : args[4].get 64 = fr.rsp)
    (hsave : ∀ r ∈ ([3, 5, 12, 13, 14, 15] : List (Fin Reg.count)),
      args[r].get 64 = fr.entryReg r.val)
    (hsi : args[6].get 64 = 8)
    (hw : Writable code fr.original (fr.rsp - 0x48) 0x48) :
    ∃ nextArgs : Values Value Reg.count,
      LIR.program.runBlock (dialect code) ⟨.l10a690, args, fr.original⟩ =
        .jump ⟨.l10a6a8, nextArgs, inputSavedMemory fr⟩ ∧
      nextArgs[4] = ⟨64, fr.rsp - 0x48⟩ ∧ nextArgs[2] = args[2] ∧
      nextArgs[7] = args[7] ∧ nextArgs[22] = args[22] ∧
      nextArgs[39] = args[39] ∧ nextArgs[50] = args[50] ∧ nextArgs[51] = args[51] := by
  have h3 := hsave 3 (by decide)
  have h5 := hsave 5 (by decide)
  have h12 := hsave 12 (by decide)
  have h13 := hsave 13 (by decide)
  have h14 := hsave 14 (by decide)
  have h15 := hsave 15 (by decide)
  change args[3].get 64 = fr.rbx at h3
  change args[5].get 64 = fr.rbp at h5
  change args[12].get 64 = fr.r12 at h12
  change args[13].get 64 = fr.r13 at h13
  change args[14].get 64 = fr.r14 at h14
  change args[15].get 64 = fr.r15 at h15
  let m1 := memStore fr.original (fr.rsp - 8) fr.rbp
  let m2 := memStore m1 (fr.rsp - 16) fr.r15
  let m3 := memStore m2 (fr.rsp - 24) fr.r14
  let m4 := memStore m3 (fr.rsp - 32) fr.r13
  let m5 := memStore m4 (fr.rsp - 40) fr.r12
  have hw1 : Writable code fr.original (fr.rsp - 8) 8 :=
    hw.of_offsets (addr_sub _ _) (addr_sub _ _) (by decide +kernel)
  have hg1 : StoreOk code fr.original (fr.rsp - 8) 8 0x10a690 1 :=
    input_store_guard hcode 0x10a690 1 (by decide) (by decide) hw1
  have hw2 : Writable code m1 (fr.rsp - 16) 8 :=
    (hw.memStore (fr.rsp - 8) fr.rbp).of_offsets (addr_sub _ _) (addr_sub _ _) (by decide +kernel)
  have hg2 : StoreOk code m1 (fr.rsp - 16) 8 0x10a691 2 :=
    input_store_guard hcode 0x10a691 2 (by decide) (by decide) hw2
  have hw3 : Writable code m2 (fr.rsp - 24) 8 :=
    ((hw.memStore (fr.rsp - 8) fr.rbp).memStore (fr.rsp - 16) fr.r15).of_offsets
      (addr_sub _ _) (addr_sub _ _) (by decide +kernel)
  have hg3 : StoreOk code m2 (fr.rsp - 24) 8 0x10a693 2 :=
    input_store_guard hcode 0x10a693 2 (by decide) (by decide) hw3
  have hw4 : Writable code m3 (fr.rsp - 32) 8 :=
    (((hw.memStore (fr.rsp - 8) fr.rbp).memStore (fr.rsp - 16) fr.r15).memStore
      (fr.rsp - 24) fr.r14).of_offsets (addr_sub _ _) (addr_sub _ _) (by decide +kernel)
  have hg4 : StoreOk code m3 (fr.rsp - 32) 8 0x10a695 2 :=
    input_store_guard hcode 0x10a695 2 (by decide) (by decide) hw4
  have hw5 : Writable code m4 (fr.rsp - 40) 8 :=
    ((((hw.memStore (fr.rsp - 8) fr.rbp).memStore (fr.rsp - 16) fr.r15).memStore
      (fr.rsp - 24) fr.r14).memStore (fr.rsp - 32) fr.r13).of_offsets
        (addr_sub _ _) (addr_sub _ _) (by decide +kernel)
  have hg5 : StoreOk code m4 (fr.rsp - 40) 8 0x10a697 2 :=
    input_store_guard hcode 0x10a697 2 (by decide) (by decide) hw5
  have hw6 : Writable code m5 (fr.rsp - 48) 8 :=
    (((((hw.memStore (fr.rsp - 8) fr.rbp).memStore (fr.rsp - 16) fr.r15).memStore
      (fr.rsp - 24) fr.r14).memStore (fr.rsp - 32) fr.r13).memStore
      (fr.rsp - 40) fr.r12).of_offsets (addr_sub _ _) (addr_sub _ _) (by decide +kernel)
  have hg6 : StoreOk code m5 (fr.rsp - 48) 8 0x10a699 1 :=
    input_store_guard hcode 0x10a699 1 (by decide) (by decide) hw6
  have hc : (cmpSpec (8 : BitVec 64) 7).CF = false ∧
      (cmpSpec (8 : BitVec 64) 7).ZF = false := by decide +kernel
  rw [inputEntry_eval]
  simp only [hsp, h3, h5, h12, h13, h14, h15, hsi, hc.1, hc.2, Bool.false_or,
    Bool.false_eq_true, ↓reduceIte]
  dsimp only [m1, m2, m3, m4, m5] at hg2 hg3 hg4 hg5 hg6
  simp only [hg1, hg2, hg3, hg4, hg5, hg6, ↓reduceIte]
  refine ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩


simproc_decl inputReturned_stop
    ((Transfer.returned _ : Transfer Value Ram LIR.Label signature Reg.count)) :=
  fun e => return .done { expr := e }

set_option maxRecDepth 4096 in
theorem_by inputBody_eval (code : CodeMap) (args : Values Value Reg.count) (mem : Ram) :
    AesGcm.Proofs.Machine.LIR.program.runBlock (dialect code) ⟨.l10a6a8, args, mem⟩ = _ := by
  cfg_eval [LIR.b_l10a6a8, LIR.b_l10a6a8_1, LIR.b_l10a6a8_2, LIR.b_l10a6a8_3, LIR.b_l10a6a8_4, LIR.b_l10a6a8_5, LIR.b_l10a6a8_6, LIR.b_l10a6a8_7, LIR.b_l10a6a8_8, LIR.b_l10a6a8_9, LIR.b_l10a6a8_10, LIR.b_l10a6a8_11, LIR.b_l10a6a8_12, LIR.b_l10a6a8_13, LIR.b_l10a6a8_14]
  cfg_name_stores
  rfl



theorem inputBody_spill_loads (m : Ram) (sp : BitVec 64) (v0 v1 v2 : BitVec 64) :
    let m1 := memStore m (sp + 8) v0
    let m2 := memStore m1 (sp + 16) v1
    let m3 := memStore m2 sp v2
    memLoad m3 sp 64 = v2 ∧ memLoad m3 (sp + 8) 64 = v0 ∧
      memLoad m3 (sp + 16) 64 = v1 := by
  intro m1 m2 m3
  have h08 : RangeApart sp 8 (sp + 8) 8 := by
    apply RangeApart.of_offsets (addr_self sp) rfl
    decide +kernel
  have h016 : RangeApart sp 8 (sp + 16) 8 := by
    apply RangeApart.of_offsets (addr_self sp) rfl
    decide +kernel
  have h168 : RangeApart (sp + 16) 8 (sp + 8) 8 := by
    apply RangeApart.of_offsets rfl rfl
    decide +kernel
  constructor
  · exact memLoad_memStore_same m2 sp v2 (by decide) (by decide)
  constructor
  · rw [memLoad_memStore_of_rangeApart m2 sp (sp + 8) v2 64 h08,
      memLoad_memStore_of_rangeApart m1 (sp + 16) (sp + 8) v1 64 h168]
    exact memLoad_memStore_same m (sp + 8) v0 (by decide) (by decide)
  · rw [memLoad_memStore_of_rangeApart m2 sp (sp + 16) v2 64 h016]
    exact memLoad_memStore_same m1 (sp + 16) v1 (by decide) (by decide)


set_option maxRecDepth 4096 in
set_option maxHeartbeats 1200000 in
theorem inputBody_data (args : Values Value Reg.count) (mem original : Ram) (input : BitVec 64) :
  let pack0 :=
  BitVec.setWidth 64 (memLoad mem (Value.get 64 args[2] + 11) 8) <<< 56 |||
    (BitVec.setWidth 64 (memLoad mem (Value.get 64 args[2] + 10) 8) <<< 40 |||
      (BitVec.setWidth 64 (BitVec.setWidth 32 (memLoad mem (Value.get 64 args[2] + 9) 8) <<< 24) |||
        (BitVec.setWidth 64 (BitVec.setWidth 32 (memLoad mem (Value.get 64 args[2] + 8) 8) <<< 8) |||
          (BitVec.setWidth 64 (memLoad mem (Value.get 64 args[2] + 3) 8) <<< 48 |||
            (BitVec.setWidth 64 (memLoad mem (Value.get 64 args[2] + 2) 8) <<< 32 |||
              (BitVec.setWidth 64 (memLoad mem (Value.get 64 args[2]) 8) |||
                BitVec.setWidth 64
                  (BitVec.setWidth 32 (memLoad mem (Value.get 64 args[2] + 1) 8) <<< 16)))))))

  let m1 :=
  memStore mem (Value.get 64 args[4] + 8) pack0

  let pack1 :=
  BitVec.setWidth 64 (memLoad m1 (Value.get 64 args[2] + 27) 8) <<< 56 |||
    (BitVec.setWidth 64 (memLoad m1 (Value.get 64 args[2] + 26) 8) <<< 40 |||
      (BitVec.setWidth 64 (BitVec.setWidth 32 (memLoad m1 (Value.get 64 args[2] + 25) 8) <<< 24) |||
        (BitVec.setWidth 64 (BitVec.setWidth 32 (memLoad m1 (Value.get 64 args[2] + 24) 8) <<< 8) |||
          (BitVec.setWidth 64 (memLoad m1 (Value.get 64 args[2] + 19) 8) <<< 48 |||
            (BitVec.setWidth 64 (memLoad m1 (Value.get 64 args[2] + 18) 8) <<< 32 |||
              (BitVec.setWidth 64 (memLoad m1 (Value.get 64 args[2] + 16) 8) |||
                BitVec.setWidth 64
                  (BitVec.setWidth 32 (memLoad m1 (Value.get 64 args[2] + 17) 8) <<< 16)))))))

  let m2 :=
  memStore m1 (Value.get 64 args[4] + 16) (pack1 ^^^ (pack0 >>> 1 ^^^ pack1) &&& (6148914691236517205 : BitVec 64))

  let pack2 :=
  BitVec.setWidth 64 (memLoad m2 (Value.get 64 args[2] + 43) 8) <<< 56 |||
    (BitVec.setWidth 64 (memLoad m2 (Value.get 64 args[2] + 42) 8) <<< 40 |||
      (BitVec.setWidth 64 (BitVec.setWidth 32 (memLoad m2 (Value.get 64 args[2] + 41) 8) <<< 24) |||
        (BitVec.setWidth 64 (BitVec.setWidth 32 (memLoad m2 (Value.get 64 args[2] + 40) 8) <<< 8) |||
          (BitVec.setWidth 64 (memLoad m2 (Value.get 64 args[2] + 35) 8) <<< 48 |||
            (BitVec.setWidth 64 (memLoad m2 (Value.get 64 args[2] + 34) 8) <<< 32 |||
              (BitVec.setWidth 64 (memLoad m2 (Value.get 64 args[2] + 32) 8) |||
                BitVec.setWidth 64
                  (BitVec.setWidth 32 (memLoad m2 (Value.get 64 args[2] + 33) 8) <<< 16)))))))

  let m3 :=
  memStore m2 (Value.get 64 args[4]) pack2

  let pack3 :=
  BitVec.setWidth 64 (memLoad m3 (Value.get 64 args[2] + 59) 8) <<< 56 |||
    (BitVec.setWidth 64 (memLoad m3 (Value.get 64 args[2] + 58) 8) <<< 40 |||
      (BitVec.setWidth 64 (BitVec.setWidth 32 (memLoad m3 (Value.get 64 args[2] + 57) 8) <<< 24) |||
        (BitVec.setWidth 64 (BitVec.setWidth 32 (memLoad m3 (Value.get 64 args[2] + 56) 8) <<< 8) |||
          (BitVec.setWidth 64 (memLoad m3 (Value.get 64 args[2] + 51) 8) <<< 48 |||
            (BitVec.setWidth 64 (memLoad m3 (Value.get 64 args[2] + 50) 8) <<< 32 |||
              (BitVec.setWidth 64 (memLoad m3 (Value.get 64 args[2] + 48) 8) |||
                BitVec.setWidth 64
                  (BitVec.setWidth 32 (memLoad m3 (Value.get 64 args[2] + 49) 8) <<< 16)))))))

  let pack4 :=
  BitVec.setWidth 64 (memLoad m3 (Value.get 64 args[2] + 15) 8) <<< 56 |||
    (BitVec.setWidth 64 (memLoad m3 (Value.get 64 args[2] + 14) 8) <<< 40 |||
      (BitVec.setWidth 64 (BitVec.setWidth 32 (memLoad m3 (Value.get 64 args[2] + 13) 8) <<< 24) |||
        (BitVec.setWidth 64 (BitVec.setWidth 32 (memLoad m3 (Value.get 64 args[2] + 12) 8) <<< 8) |||
          (BitVec.setWidth 64 (memLoad m3 (Value.get 64 args[2] + 7) 8) <<< 48 |||
            (BitVec.setWidth 64 (memLoad m3 (Value.get 64 args[2] + 6) 8) <<< 32 |||
              (BitVec.setWidth 64 (memLoad m3 (Value.get 64 args[2] + 4) 8) |||
                BitVec.setWidth 64
                  (BitVec.setWidth 32 (memLoad m3 (Value.get 64 args[2] + 5) 8) <<< 16)))))))

  let pack5 :=
  BitVec.setWidth 64 (memLoad m3 (Value.get 64 args[2] + 31) 8) <<< 56 |||
    (BitVec.setWidth 64 (memLoad m3 (Value.get 64 args[2] + 30) 8) <<< 40 |||
      (BitVec.setWidth 64 (BitVec.setWidth 32 (memLoad m3 (Value.get 64 args[2] + 29) 8) <<< 24) |||
        (BitVec.setWidth 64 (BitVec.setWidth 32 (memLoad m3 (Value.get 64 args[2] + 28) 8) <<< 8) |||
          (BitVec.setWidth 64 (memLoad m3 (Value.get 64 args[2] + 23) 8) <<< 48 |||
            (BitVec.setWidth 64 (memLoad m3 (Value.get 64 args[2] + 22) 8) <<< 32 |||
              (BitVec.setWidth 64 (memLoad m3 (Value.get 64 args[2] + 20) 8) |||
                BitVec.setWidth 64
                  (BitVec.setWidth 32 (memLoad m3 (Value.get 64 args[2] + 21) 8) <<< 16)))))))

  let pack6 :=
  BitVec.setWidth 64 (memLoad m3 (Value.get 64 args[2] + 47) 8) <<< 56 |||
    (BitVec.setWidth 64 (memLoad m3 (Value.get 64 args[2] + 46) 8) <<< 40 |||
      (BitVec.setWidth 64 (BitVec.setWidth 32 (memLoad m3 (Value.get 64 args[2] + 45) 8) <<< 24) |||
        (BitVec.setWidth 64 (BitVec.setWidth 32 (memLoad m3 (Value.get 64 args[2] + 44) 8) <<< 8) |||
          (BitVec.setWidth 64 (memLoad m3 (Value.get 64 args[2] + 39) 8) <<< 48 |||
            (BitVec.setWidth 64 (memLoad m3 (Value.get 64 args[2] + 38) 8) <<< 32 |||
              (BitVec.setWidth 64 (memLoad m3 (Value.get 64 args[2] + 36) 8) |||
                BitVec.setWidth 64
                  (BitVec.setWidth 32 (memLoad m3 (Value.get 64 args[2] + 37) 8) <<< 16)))))))

  let pack7 :=
  BitVec.setWidth 64 (memLoad m3 (Value.get 64 args[2] + 63) 8) <<< 56 |||
    (BitVec.setWidth 64 (memLoad m3 (Value.get 64 args[2] + 62) 8) <<< 40 |||
      (BitVec.setWidth 64 (BitVec.setWidth 32 (memLoad m3 (Value.get 64 args[2] + 61) 8) <<< 24) |||
        (BitVec.setWidth 64 (BitVec.setWidth 32 (memLoad m3 (Value.get 64 args[2] + 60) 8) <<< 8) |||
          (BitVec.setWidth 64 (memLoad m3 (Value.get 64 args[2] + 55) 8) <<< 48 |||
            (BitVec.setWidth 64 (memLoad m3 (Value.get 64 args[2] + 54) 8) <<< 32 |||
              (BitVec.setWidth 64 (memLoad m3 (Value.get 64 args[2] + 52) 8) |||
                BitVec.setWidth 64
                  (BitVec.setWidth 32 (memLoad m3 (Value.get 64 args[2] + 53) 8) <<< 16)))))))

  let m4 :=
  memStore m3 (Value.get 64 args[7])
    (((((((((pack0 >>> 1 ^^^ pack1) &&& (6148914691236517205 : BitVec 64)) +
                            ((pack0 >>> 1 ^^^ pack1) &&& (6148914691236517205 : BitVec 64)) ^^^
                          memLoad m3 (Value.get 64 args[4] + 8) 64) >>>
                        2 ^^^
                      (((pack2 >>> 1 ^^^ pack3) &&& (6148914691236517205 : BitVec 64)) +
                          ((pack2 >>> 1 ^^^ pack3) &&& (6148914691236517205 : BitVec 64)) ^^^
                        memLoad m3 (Value.get 64 args[4]) 64)) &&&
                    (3689348814741910323 : BitVec 64)) <<<
                  2 ^^^
                (((pack0 >>> 1 ^^^ pack1) &&& (6148914691236517205 : BitVec 64)) +
                    ((pack0 >>> 1 ^^^ pack1) &&& (6148914691236517205 : BitVec 64)) ^^^
                  memLoad m3 (Value.get 64 args[4] + 8) 64)) >>>
              4 ^^^
            ((((((pack4 >>> 1 ^^^ pack5) &&& (6148914691236517205 : BitVec 64)) +
                          ((pack4 >>> 1 ^^^ pack5) &&& (6148914691236517205 : BitVec 64)) ^^^
                        pack4) >>>
                      2 ^^^
                    (((pack6 >>> 1 ^^^ pack7) &&& (6148914691236517205 : BitVec 64)) +
                        ((pack6 >>> 1 ^^^ pack7) &&& (6148914691236517205 : BitVec 64)) ^^^
                      pack6)) &&&
                  (3689348814741910323 : BitVec 64)) <<<
                2 ^^^
              (((pack4 >>> 1 ^^^ pack5) &&& (6148914691236517205 : BitVec 64)) +
                  ((pack4 >>> 1 ^^^ pack5) &&& (6148914691236517205 : BitVec 64)) ^^^
                pack4))) &&&
          (1085102592571150095 : BitVec 64)) <<<
        4 ^^^
      ((((((pack0 >>> 1 ^^^ pack1) &&& (6148914691236517205 : BitVec 64)) +
                    ((pack0 >>> 1 ^^^ pack1) &&& (6148914691236517205 : BitVec 64)) ^^^
                  memLoad m3 (Value.get 64 args[4] + 8) 64) >>>
                2 ^^^
              (((pack2 >>> 1 ^^^ pack3) &&& (6148914691236517205 : BitVec 64)) +
                  ((pack2 >>> 1 ^^^ pack3) &&& (6148914691236517205 : BitVec 64)) ^^^
                memLoad m3 (Value.get 64 args[4]) 64)) &&&
            (3689348814741910323 : BitVec 64)) <<<
          2 ^^^
        (((pack0 >>> 1 ^^^ pack1) &&& (6148914691236517205 : BitVec 64)) +
            ((pack0 >>> 1 ^^^ pack1) &&& (6148914691236517205 : BitVec 64)) ^^^
          memLoad m3 (Value.get 64 args[4] + 8) 64)))

  let m5 :=
  memStore m4 (Value.get 64 args[7] + 8)
    (((((((pack1 ^^^ (pack0 >>> 1 ^^^ pack1) &&& (6148914691236517205 : BitVec 64)) >>> 2 ^^^
                      (pack3 ^^^ (pack2 >>> 1 ^^^ pack3) &&& (6148914691236517205 : BitVec 64))) &&&
                    (3689348814741910323 : BitVec 64)) <<<
                  2 ^^^
                memLoad m3 (Value.get 64 args[4] + 16) 64) >>>
              4 ^^^
            ((((pack5 ^^^ (pack4 >>> 1 ^^^ pack5) &&& (6148914691236517205 : BitVec 64)) >>> 2 ^^^
                    (pack7 ^^^ (pack6 >>> 1 ^^^ pack7) &&& (6148914691236517205 : BitVec 64))) &&&
                  (3689348814741910323 : BitVec 64)) <<<
                2 ^^^
              (pack5 ^^^ (pack4 >>> 1 ^^^ pack5) &&& (6148914691236517205 : BitVec 64)))) &&&
          (1085102592571150095 : BitVec 64)) <<<
        4 ^^^
      ((((pack1 ^^^ (pack0 >>> 1 ^^^ pack1) &&& (6148914691236517205 : BitVec 64)) >>> 2 ^^^
              (pack3 ^^^ (pack2 >>> 1 ^^^ pack3) &&& (6148914691236517205 : BitVec 64))) &&&
            (3689348814741910323 : BitVec 64)) <<<
          2 ^^^
        memLoad m3 (Value.get 64 args[4] + 16) 64))

  let m6 :=
  memStore m5 (Value.get 64 args[7] + 16)
    ((((((pack2 >>> 1 ^^^ pack3) &&& (6148914691236517205 : BitVec 64)) +
                    ((pack2 >>> 1 ^^^ pack3) &&& (6148914691236517205 : BitVec 64)) ^^^
                  memLoad m3 (Value.get 64 args[4]) 64 ^^^
                ((((pack0 >>> 1 ^^^ pack1) &&& (6148914691236517205 : BitVec 64)) +
                          ((pack0 >>> 1 ^^^ pack1) &&& (6148914691236517205 : BitVec 64)) ^^^
                        memLoad m3 (Value.get 64 args[4] + 8) 64) >>>
                      2 ^^^
                    (((pack2 >>> 1 ^^^ pack3) &&& (6148914691236517205 : BitVec 64)) +
                        ((pack2 >>> 1 ^^^ pack3) &&& (6148914691236517205 : BitVec 64)) ^^^
                      memLoad m3 (Value.get 64 args[4]) 64)) &&&
                  (3689348814741910323 : BitVec 64)) >>>
              4 ^^^
            (((pack6 >>> 1 ^^^ pack7) &&& (6148914691236517205 : BitVec 64)) +
                  ((pack6 >>> 1 ^^^ pack7) &&& (6148914691236517205 : BitVec 64)) ^^^
                pack6 ^^^
              ((((pack4 >>> 1 ^^^ pack5) &&& (6148914691236517205 : BitVec 64)) +
                        ((pack4 >>> 1 ^^^ pack5) &&& (6148914691236517205 : BitVec 64)) ^^^
                      pack4) >>>
                    2 ^^^
                  (((pack6 >>> 1 ^^^ pack7) &&& (6148914691236517205 : BitVec 64)) +
                      ((pack6 >>> 1 ^^^ pack7) &&& (6148914691236517205 : BitVec 64)) ^^^
                    pack6)) &&&
                (3689348814741910323 : BitVec 64))) &&&
          (1085102592571150095 : BitVec 64)) <<<
        4 ^^^
      (((pack2 >>> 1 ^^^ pack3) &&& (6148914691236517205 : BitVec 64)) +
            ((pack2 >>> 1 ^^^ pack3) &&& (6148914691236517205 : BitVec 64)) ^^^
          memLoad m3 (Value.get 64 args[4]) 64 ^^^
        ((((pack0 >>> 1 ^^^ pack1) &&& (6148914691236517205 : BitVec 64)) +
                  ((pack0 >>> 1 ^^^ pack1) &&& (6148914691236517205 : BitVec 64)) ^^^
                memLoad m3 (Value.get 64 args[4] + 8) 64) >>>
              2 ^^^
            (((pack2 >>> 1 ^^^ pack3) &&& (6148914691236517205 : BitVec 64)) +
                ((pack2 >>> 1 ^^^ pack3) &&& (6148914691236517205 : BitVec 64)) ^^^
              memLoad m3 (Value.get 64 args[4]) 64)) &&&
          (3689348814741910323 : BitVec 64)))

  let m7 :=
  memStore m6 (Value.get 64 args[7] + 24)
    ((((pack3 ^^^ (pack2 >>> 1 ^^^ pack3) &&& (6148914691236517205 : BitVec 64) ^^^
                ((pack1 ^^^ (pack0 >>> 1 ^^^ pack1) &&& (6148914691236517205 : BitVec 64)) >>> 2 ^^^
                    (pack3 ^^^ (pack2 >>> 1 ^^^ pack3) &&& (6148914691236517205 : BitVec 64))) &&&
                  (3689348814741910323 : BitVec 64)) >>>
              4 ^^^
            (pack7 ^^^ (pack6 >>> 1 ^^^ pack7) &&& (6148914691236517205 : BitVec 64) ^^^
              ((pack5 ^^^ (pack4 >>> 1 ^^^ pack5) &&& (6148914691236517205 : BitVec 64)) >>> 2 ^^^
                  (pack7 ^^^ (pack6 >>> 1 ^^^ pack7) &&& (6148914691236517205 : BitVec 64))) &&&
                (3689348814741910323 : BitVec 64))) &&&
          (1085102592571150095 : BitVec 64)) <<<
        4 ^^^
      (pack3 ^^^ (pack2 >>> 1 ^^^ pack3) &&& (6148914691236517205 : BitVec 64) ^^^
        ((pack1 ^^^ (pack0 >>> 1 ^^^ pack1) &&& (6148914691236517205 : BitVec 64)) >>> 2 ^^^
            (pack3 ^^^ (pack2 >>> 1 ^^^ pack3) &&& (6148914691236517205 : BitVec 64))) &&&
          (3689348814741910323 : BitVec 64)))

  let m8 :=
  memStore m7 (Value.get 64 args[7] + 32)
    ((((((((pack0 >>> 1 ^^^ pack1) &&& (6148914691236517205 : BitVec 64)) +
                          ((pack0 >>> 1 ^^^ pack1) &&& (6148914691236517205 : BitVec 64)) ^^^
                        memLoad m3 (Value.get 64 args[4] + 8) 64) >>>
                      2 ^^^
                    (((pack2 >>> 1 ^^^ pack3) &&& (6148914691236517205 : BitVec 64)) +
                        ((pack2 >>> 1 ^^^ pack3) &&& (6148914691236517205 : BitVec 64)) ^^^
                      memLoad m3 (Value.get 64 args[4]) 64)) &&&
                  (3689348814741910323 : BitVec 64)) <<<
                2 ^^^
              (((pack0 >>> 1 ^^^ pack1) &&& (6148914691236517205 : BitVec 64)) +
                  ((pack0 >>> 1 ^^^ pack1) &&& (6148914691236517205 : BitVec 64)) ^^^
                memLoad m3 (Value.get 64 args[4] + 8) 64)) >>>
            4 ^^^
          ((((((pack4 >>> 1 ^^^ pack5) &&& (6148914691236517205 : BitVec 64)) +
                        ((pack4 >>> 1 ^^^ pack5) &&& (6148914691236517205 : BitVec 64)) ^^^
                      pack4) >>>
                    2 ^^^
                  (((pack6 >>> 1 ^^^ pack7) &&& (6148914691236517205 : BitVec 64)) +
                      ((pack6 >>> 1 ^^^ pack7) &&& (6148914691236517205 : BitVec 64)) ^^^
                    pack6)) &&&
                (3689348814741910323 : BitVec 64)) <<<
              2 ^^^
            (((pack4 >>> 1 ^^^ pack5) &&& (6148914691236517205 : BitVec 64)) +
                ((pack4 >>> 1 ^^^ pack5) &&& (6148914691236517205 : BitVec 64)) ^^^
              pack4))) &&&
        (1085102592571150095 : BitVec 64) ^^^
      ((((((pack4 >>> 1 ^^^ pack5) &&& (6148914691236517205 : BitVec 64)) +
                    ((pack4 >>> 1 ^^^ pack5) &&& (6148914691236517205 : BitVec 64)) ^^^
                  pack4) >>>
                2 ^^^
              (((pack6 >>> 1 ^^^ pack7) &&& (6148914691236517205 : BitVec 64)) +
                  ((pack6 >>> 1 ^^^ pack7) &&& (6148914691236517205 : BitVec 64)) ^^^
                pack6)) &&&
            (3689348814741910323 : BitVec 64)) <<<
          2 ^^^
        (((pack4 >>> 1 ^^^ pack5) &&& (6148914691236517205 : BitVec 64)) +
            ((pack4 >>> 1 ^^^ pack5) &&& (6148914691236517205 : BitVec 64)) ^^^
          pack4)))

  let m9 :=
  memStore m8 (Value.get 64 args[7] + 40)
    ((((((pack1 ^^^ (pack0 >>> 1 ^^^ pack1) &&& (6148914691236517205 : BitVec 64)) >>> 2 ^^^
                    (pack3 ^^^ (pack2 >>> 1 ^^^ pack3) &&& (6148914691236517205 : BitVec 64))) &&&
                  (3689348814741910323 : BitVec 64)) <<<
                2 ^^^
              memLoad m3 (Value.get 64 args[4] + 16) 64) >>>
            4 ^^^
          ((((pack5 ^^^ (pack4 >>> 1 ^^^ pack5) &&& (6148914691236517205 : BitVec 64)) >>> 2 ^^^
                  (pack7 ^^^ (pack6 >>> 1 ^^^ pack7) &&& (6148914691236517205 : BitVec 64))) &&&
                (3689348814741910323 : BitVec 64)) <<<
              2 ^^^
            (pack5 ^^^ (pack4 >>> 1 ^^^ pack5) &&& (6148914691236517205 : BitVec 64)))) &&&
        (1085102592571150095 : BitVec 64) ^^^
      ((((pack5 ^^^ (pack4 >>> 1 ^^^ pack5) &&& (6148914691236517205 : BitVec 64)) >>> 2 ^^^
              (pack7 ^^^ (pack6 >>> 1 ^^^ pack7) &&& (6148914691236517205 : BitVec 64))) &&&
            (3689348814741910323 : BitVec 64)) <<<
          2 ^^^
        (pack5 ^^^ (pack4 >>> 1 ^^^ pack5) &&& (6148914691236517205 : BitVec 64))))

  let m10 :=
  memStore m9 (Value.get 64 args[7] + 48)
    (((((pack2 >>> 1 ^^^ pack3) &&& (6148914691236517205 : BitVec 64)) +
                  ((pack2 >>> 1 ^^^ pack3) &&& (6148914691236517205 : BitVec 64)) ^^^
                memLoad m3 (Value.get 64 args[4]) 64 ^^^
              ((((pack0 >>> 1 ^^^ pack1) &&& (6148914691236517205 : BitVec 64)) +
                        ((pack0 >>> 1 ^^^ pack1) &&& (6148914691236517205 : BitVec 64)) ^^^
                      memLoad m3 (Value.get 64 args[4] + 8) 64) >>>
                    2 ^^^
                  (((pack2 >>> 1 ^^^ pack3) &&& (6148914691236517205 : BitVec 64)) +
                      ((pack2 >>> 1 ^^^ pack3) &&& (6148914691236517205 : BitVec 64)) ^^^
                    memLoad m3 (Value.get 64 args[4]) 64)) &&&
                (3689348814741910323 : BitVec 64)) >>>
            4 ^^^
          (((pack6 >>> 1 ^^^ pack7) &&& (6148914691236517205 : BitVec 64)) +
                ((pack6 >>> 1 ^^^ pack7) &&& (6148914691236517205 : BitVec 64)) ^^^
              pack6 ^^^
            ((((pack4 >>> 1 ^^^ pack5) &&& (6148914691236517205 : BitVec 64)) +
                      ((pack4 >>> 1 ^^^ pack5) &&& (6148914691236517205 : BitVec 64)) ^^^
                    pack4) >>>
                  2 ^^^
                (((pack6 >>> 1 ^^^ pack7) &&& (6148914691236517205 : BitVec 64)) +
                    ((pack6 >>> 1 ^^^ pack7) &&& (6148914691236517205 : BitVec 64)) ^^^
                  pack6)) &&&
              (3689348814741910323 : BitVec 64))) &&&
        (1085102592571150095 : BitVec 64) ^^^
      (((pack6 >>> 1 ^^^ pack7) &&& (6148914691236517205 : BitVec 64)) +
            ((pack6 >>> 1 ^^^ pack7) &&& (6148914691236517205 : BitVec 64)) ^^^
          pack6 ^^^
        ((((pack4 >>> 1 ^^^ pack5) &&& (6148914691236517205 : BitVec 64)) +
                  ((pack4 >>> 1 ^^^ pack5) &&& (6148914691236517205 : BitVec 64)) ^^^
                pack4) >>>
              2 ^^^
            (((pack6 >>> 1 ^^^ pack7) &&& (6148914691236517205 : BitVec 64)) +
                ((pack6 >>> 1 ^^^ pack7) &&& (6148914691236517205 : BitVec 64)) ^^^
              pack6)) &&&
          (3689348814741910323 : BitVec 64)))

  let m11 :=
  memStore m10 (Value.get 64 args[7] + 56)
    (((pack3 ^^^ (pack2 >>> 1 ^^^ pack3) &&& (6148914691236517205 : BitVec 64) ^^^
              ((pack1 ^^^ (pack0 >>> 1 ^^^ pack1) &&& (6148914691236517205 : BitVec 64)) >>> 2 ^^^
                  (pack3 ^^^ (pack2 >>> 1 ^^^ pack3) &&& (6148914691236517205 : BitVec 64))) &&&
                (3689348814741910323 : BitVec 64)) >>>
            4 ^^^
          (pack7 ^^^ (pack6 >>> 1 ^^^ pack7) &&& (6148914691236517205 : BitVec 64) ^^^
            ((pack5 ^^^ (pack4 >>> 1 ^^^ pack5) &&& (6148914691236517205 : BitVec 64)) >>> 2 ^^^
                (pack7 ^^^ (pack6 >>> 1 ^^^ pack7) &&& (6148914691236517205 : BitVec 64))) &&&
              (3689348814741910323 : BitVec 64))) &&&
        (1085102592571150095 : BitVec 64) ^^^
      (pack7 ^^^ (pack6 >>> 1 ^^^ pack7) &&& (6148914691236517205 : BitVec 64) ^^^
        ((pack5 ^^^ (pack4 >>> 1 ^^^ pack5) &&& (6148914691236517205 : BitVec 64)) >>> 2 ^^^
            (pack7 ^^^ (pack6 >>> 1 ^^^ pack7) &&& (6148914691236517205 : BitVec 64))) &&&
          (3689348814741910323 : BitVec 64)))

  (∀ off : BitVec 64, off.toNat < 64 →
    memLoad mem (Value.get 64 args[2] + off) 8 = memLoad original (input + off) 8) →
  (∀ off : BitVec 64, off.toNat < 64 →
    memLoad m1 (Value.get 64 args[2] + off) 8 = memLoad original (input + off) 8) →
  (∀ off : BitVec 64, off.toNat < 64 →
    memLoad m2 (Value.get 64 args[2] + off) 8 = memLoad original (input + off) 8) →
  (∀ off : BitVec 64, off.toNat < 64 →
    memLoad m3 (Value.get 64 args[2] + off) 8 = memLoad original (input + off) 8) →
  m11 = inputStoredPlanes m3 (Value.get 64 args[7]) (bitslice (memoryBlocks original input)) := by
  intro pack0 m1 pack1 m2 pack2 m3 pack3 pack4 pack5 pack6 pack7 m4 m5 m6 m7 m8 m9 m10 m11 hb0 hb1 hb2 hb3
  have hb0z : memLoad mem (Value.get 64 args[2]) 8 = memLoad original input 8 := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hb0 0 (by decide)
  let x := memoryBlocks original input
  have hp0 : pack0 = assemblyPacking x 0 := by
    dsimp only [pack0]
    simp (disch := decide +kernel) only [hb0, hb0z]
    simp only [x, assemblyPacking, assemblyPackRead, memoryBlocks, memoryBlock,
      show (0 : Fin 8).val = 0 from rfl, Nat.reduceMod, Nat.reduceDiv,
      Nat.mul_zero, Nat.zero_add,
      memLoad_8,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero]
  have hp1 : pack1 = assemblyPacking x 1 := by
    dsimp only [pack1]
    simp (disch := decide +kernel) only [hb1]
    simp only [x, assemblyPacking, assemblyPackRead, memoryBlocks, memoryBlock,
      show (1 : Fin 8).val = 1 from rfl, Nat.reduceMod, Nat.reduceDiv,
      Nat.reduceMul, Nat.reduceAdd, Nat.mul_zero, Nat.zero_add,
      BitVec.add_assoc, ← BitVec.ofNat_add, memLoad_8,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero]
  have hp2 : pack2 = assemblyPacking x 2 := by
    dsimp only [pack2]
    simp (disch := decide +kernel) only [hb2]
    simp only [x, assemblyPacking, assemblyPackRead, memoryBlocks, memoryBlock,
      show (2 : Fin 8).val = 2 from rfl, Nat.reduceMod, Nat.reduceDiv,
      Nat.reduceMul, Nat.reduceAdd, Nat.mul_zero, Nat.zero_add,
      BitVec.add_assoc, ← BitVec.ofNat_add, memLoad_8,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero]
  have hp3 : pack3 = assemblyPacking x 3 := by
    dsimp only [pack3]
    simp (disch := decide +kernel) only [hb3]
    simp only [x, assemblyPacking, assemblyPackRead, memoryBlocks, memoryBlock,
      show (3 : Fin 8).val = 3 from rfl, Nat.reduceMod, Nat.reduceDiv,
      Nat.reduceMul, Nat.reduceAdd, Nat.mul_zero, Nat.zero_add,
      BitVec.add_assoc, ← BitVec.ofNat_add, memLoad_8,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero]
  have hp4 : pack4 = assemblyPacking x 4 := by
    dsimp only [pack4]
    simp (disch := decide +kernel) only [hb3]
    simp only [x, assemblyPacking, assemblyPackRead, memoryBlocks, memoryBlock,
      show (4 : Fin 8).val = 4 from rfl, Nat.reduceMod, Nat.reduceDiv,
      Nat.reduceMul, Nat.reduceAdd, Nat.mul_zero,
      memLoad_8,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero]
  have hp5 : pack5 = assemblyPacking x 5 := by
    dsimp only [pack5]
    simp (disch := decide +kernel) only [hb3]
    simp only [x, assemblyPacking, assemblyPackRead, memoryBlocks, memoryBlock,
      show (5 : Fin 8).val = 5 from rfl, Nat.reduceMod, Nat.reduceDiv,
      Nat.reduceMul, Nat.reduceAdd,
      BitVec.add_assoc, ← BitVec.ofNat_add, memLoad_8,
      BitVec.ofNat_eq_ofNat]
  have hp6 : pack6 = assemblyPacking x 6 := by
    dsimp only [pack6]
    simp (disch := decide +kernel) only [hb3]
    simp only [x, assemblyPacking, assemblyPackRead, memoryBlocks, memoryBlock,
      show (6 : Fin 8).val = 6 from rfl, Nat.reduceMod, Nat.reduceDiv,
      Nat.reduceMul, Nat.reduceAdd,
      BitVec.add_assoc, ← BitVec.ofNat_add, memLoad_8,
      BitVec.ofNat_eq_ofNat]
  have hp7 : pack7 = assemblyPacking x 7 := by
    dsimp only [pack7]
    simp (disch := decide +kernel) only [hb3]
    simp only [x, assemblyPacking, assemblyPackRead, memoryBlocks, memoryBlock,
      show (7 : Fin 8).val = 7 from rfl, Nat.reduceMod, Nat.reduceDiv,
      Nat.reduceMul, Nat.reduceAdd,
      BitVec.add_assoc, ← BitVec.ofNat_add, memLoad_8,
      BitVec.ofNat_eq_ofNat]
  let packs : Planes := fun p ↦ match p.val with
    | 0 => pack0 | 1 => pack1 | 2 => pack2 | 3 => pack3
    | 4 => pack4 | 5 => pack5 | 6 => pack6 | _ => pack7
  have hpacks : packs = assemblyPacking x := by
    funext p
    have hp : p.val = 0 ∨ p.val = 1 ∨ p.val = 2 ∨ p.val = 3 ∨
      p.val = 4 ∨ p.val = 5 ∨ p.val = 6 ∨ p.val = 7 := by omega
    rcases hp with hp | hp | hp | hp | hp | hp | hp | hp
    · have he : p = (0 : Fin 8) := Fin.ext hp
      subst p
      exact hp0
    · have he : p = (1 : Fin 8) := Fin.ext hp
      subst p
      exact hp1
    · have he : p = (2 : Fin 8) := Fin.ext hp
      subst p
      exact hp2
    · have he : p = (3 : Fin 8) := Fin.ext hp
      subst p
      exact hp3
    · have he : p = (4 : Fin 8) := Fin.ext hp
      subst p
      exact hp4
    · have he : p = (5 : Fin 8) := Fin.ext hp
      subst p
      exact hp5
    · have he : p = (6 : Fin 8) := Fin.ext hp
      subst p
      exact hp6
    · have he : p = (7 : Fin 8) := Fin.ext hp
      subst p
      exact hp7
  have hs := inputBody_spill_loads mem (Value.get 64 args[4]) pack0
    (pack1 ^^^ ((pack0 >>> (1 : Nat)) ^^^ pack1) &&& 0x5555555555555555) pack2
  have hs0 : memLoad m3 (Value.get 64 args[4]) 64 = pack2 := hs.1
  have hs8 : memLoad m3 (Value.get 64 args[4] + 8) 64 = pack0 := hs.2.1
  have hs16 : memLoad m3 (Value.get 64 args[4] + 16) 64 =
      pack1 ^^^ ((pack0 >>> (1 : Nat)) ^^^ pack1) &&& 0x5555555555555555 := hs.2.2
  have hstores : m11 = inputStoredPlanes m3 (Value.get 64 args[7])
      (assemblyInputWords packs) := by
    dsimp only [m11, m10, m9, m8, m7, m6, m5, m4]
    rw [hs0, hs8, hs16]
    have ha0 : wordAddr (Value.get 64 args[7]) 64 0 = Value.get 64 args[7] := by
      change Value.get 64 args[7] + (0 : BitVec 64) = Value.get 64 args[7]
      exact BitVec.add_zero _
    simp only [inputStoredPlanes, ha0]
    rfl
  rw [hstores, hpacks, assemblyInputWords_bitslice]


attribute [local irreducible] memStore memLoad

set_option maxHeartbeats 2000000 in
theorem inputBody_runBlock (code : CodeMap) (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (args : Values Value Reg.count) (fr : Activation)
    (hregs : args[4].get 64 = fr.rsp - 0x48 ∧ args[2].get 64 = fr.rdx ∧
      args[7].get 64 = fr.rdi)
    (hdf : args[22] = ⟨1, 0⟩)
    (hfp : args[39] = ⟨32, fr.mxcsr⟩ ∧ args[50] = ⟨16, fr.ftw⟩ ∧
      args[51] = ⟨16, fr.fcw⟩)
    (hstack : Writable code fr.original (fr.rsp - 0x48) 0x48 ∧
      Readable fr.original fr.rsp 8 ∧ memLoad fr.original fr.rsp 64 = fr.ret ∧
      fr.ret.toNat < 2 ^ 32 ∧ fr.low.toNat + 0x48 ≤ fr.rsp.toNat)
    (hio : Readable fr.original fr.rdx 64 ∧
      Writable code fr.original fr.rdi 64 ∧
      (AesGcm.Proofs.Machine.Runtime.callStack fr).Disjoint (AesGcm.Proofs.Machine.Runtime.span fr.rdx 64) ∧
      (AesGcm.Proofs.Machine.Runtime.callStack fr).Disjoint (AesGcm.Proofs.Machine.Runtime.span fr.rdi 64) ∧
      (AesGcm.Proofs.Machine.Runtime.span fr.rdi 64).Disjoint (AesGcm.Proofs.Machine.Runtime.span fr.rdx 64)) :
    ∃ out, LIR.program.runBlock (dialect code) ⟨.l10a6a8, args, inputSavedMemory fr⟩ =
      .returned out ∧ out.tag = some ⟨64, fr.ret⟩ ∧
      Atom.All code out.values out.store (LIR.Fn10a690.frameInfo.doneAtoms fr) ∧
      RamWriteFrame fr.original out.store [fr.region, Runtime.span fr.rdi 64] ∧
      (∀ r : Fin 16, out.values[r.val].width = 64) ∧
      (∀ p : Fin 8, memLoad out.store (fr.rdi + BitVec.ofNat 64 (8 * p.val)) 64 =
        encode (memoryBlocks fr.original fr.rdx) p) := by
  have he := inputBody_eval code args (inputSavedMemory fr)
  extract_lets m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 at he
  have hsp := hregs.1
  have h2 := hregs.2.1
  have h7 := hregs.2.2
  simp only [↓inputReturned_stop, hsp, h2, h7] at he

  have hroom := hstack.2.2.2.2
  have hretLow := hstack.2.1.low
  have hsub (k : Nat) (hk : k ≤ 0x48) :
      (fr.rsp - BitVec.ofNat 64 k).toNat = fr.rsp.toNat - k := by
    have hkn : k < 2 ^ 64 := by omega
    rw [BitVec.toNat_sub_of_le (by
      change (BitVec.ofNat 64 k).toNat ≤ fr.rsp.toNat
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hkn]
      omega), BitVec.toNat_ofNat, Nat.mod_eq_of_lt hkn]
  let spill := Runtime.span (fr.rsp - 0x48) 24
  let output := Runtime.span fr.rdi 64
  let regions := [spill, output]
  let fullRegions := [fr.region, output]
  have hs72 : (fr.rsp - (0x48 : BitVec 64)).toNat = fr.rsp.toNat - 0x48 :=
    hsub 0x48 (by decide)
  have hspills : (fr.rsp - 0x48).toNat = fr.rsp.toNat - 0x48 := hsub 0x48 (by decide)
  have hspill (off : BitVec 64) (ho : off.toNat + 8 ≤ 24) :
      InRegions regions (fr.rsp - 0x48 + off) 8 := by
    have he : (fr.rsp - 0x48 + off).toNat = fr.rsp.toNat - 0x48 + off.toNat := by
      rw [BitVec.toNat_add_of_lt (by rw [hspills]; omega), hspills]
    refine ⟨spill, by simp [regions], ?_⟩
    simp only [spill, Runtime.span, InRegion, he, hspills]
    omega
  have hout (off : BitVec 64) (ho : off.toNat + 8 ≤ 64) :
      InRegions regions (fr.rdi + off) 8 := by
    have hb := hio.2.1.readable.low
    have he : (fr.rdi + off).toNat = fr.rdi.toNat + off.toNat :=
      BitVec.toNat_add_of_lt (by omega)
    refine ⟨output, by simp [regions], ?_⟩
    simp only [output, Runtime.span, InRegion, he]
    omega
  have f0 := RamWriteFrame.refl (inputSavedMemory fr) regions
  have f1 : RamWriteFrame (inputSavedMemory fr) m1 regions := by
    apply f0.memStore _
    rw [hsp]
    exact hspill 8 (by decide)
  have f2 : RamWriteFrame (inputSavedMemory fr) m2 regions := by
    apply f1.memStore _
    rw [hsp]
    exact hspill 16 (by decide)
  have f3 : RamWriteFrame (inputSavedMemory fr) m3 regions := by
    apply f2.memStore _
    rw [hsp]
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hspill 0 (by decide)
  have f4 : RamWriteFrame (inputSavedMemory fr) m4 regions := by
    apply f3.memStore _
    rw [h7]
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hout 0 (by decide)
  have f5 : RamWriteFrame (inputSavedMemory fr) m5 regions := by
    apply f4.memStore _
    rw [h7]
    exact hout 8 (by decide)
  have f6 : RamWriteFrame (inputSavedMemory fr) m6 regions := by
    apply f5.memStore _
    rw [h7]
    exact hout 16 (by decide)
  have f7 : RamWriteFrame (inputSavedMemory fr) m7 regions := by
    apply f6.memStore _
    rw [h7]
    exact hout 24 (by decide)
  have f8 : RamWriteFrame (inputSavedMemory fr) m8 regions := by
    apply f7.memStore _
    rw [h7]
    exact hout 32 (by decide)
  have f9 : RamWriteFrame (inputSavedMemory fr) m9 regions := by
    apply f8.memStore _
    rw [h7]
    exact hout 40 (by decide)
  have f10 : RamWriteFrame (inputSavedMemory fr) m10 regions := by
    apply f9.memStore _
    rw [h7]
    exact hout 48 (by decide)
  have f11 : RamWriteFrame (inputSavedMemory fr) m11 regions := by
    apply f10.memStore _
    rw [h7]
    exact hout 56 (by decide)

  have hwithin : RegionsWithin regions fullRegions := by
    intro r hr
    simp only [regions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · refine ⟨fr.region, by simp [fullRegions], ?_, ?_⟩
      all_goals simp only [spill, Runtime.span, Activation.region, hspills]; omega
    · exact ⟨output, by simp [fullRegions],
        Nat.le_refl _, Nat.le_refl _⟩
  have hsaved : RamWriteFrame fr.original (inputSavedMemory fr) fullRegions := by
    apply (RamWriteFrame.refl fr.original fullRegions).trans
      (inputSavedMemory_frame fr (by omega))
    intro r hr
    simp only [List.mem_singleton] at hr
    subst r
    exact ⟨fr.region, by simp [fullRegions],
      Nat.le_refl _, Nat.le_refl _⟩
  have full0 := hsaved
  have full1 := hsaved.trans f1 hwithin
  have full2 := hsaved.trans f2 hwithin
  have full3 := hsaved.trans f3 hwithin
  have full4 := hsaved.trans f4 hwithin
  have full5 := hsaved.trans f5 hwithin
  have full6 := hsaved.trans f6 hwithin
  have full7 := hsaved.trans f7 hwithin
  have full8 := hsaved.trans f8 hwithin
  have full9 := hsaved.trans f9 hwithin
  have full10 := hsaved.trans f10 hwithin
  have full11 := hsaved.trans f11 hwithin


  have haddr (off : BitVec 64) (ho : off.toNat ≤ 80) :
      (fr.rsp - 0x48 + off).toNat = fr.rsp.toNat - 0x48 + off.toNat := by
    rw [BitVec.toNat_add_of_lt (by rw [hspills]; omega), hspills]
  have stackPart (m : Ram) (hf : RamWriteFrame fr.original m fullRegions)
      (off : BitVec 64) (ho : off.toNat + 8 ≤ 24) :
      Writable code m (fr.rsp - 0x48 + off) 8 := by
    apply (hstack.1.of_frame hf).sub
    · rw [haddr off (by omega), hs72]
      omega
    · rw [haddr off (by omega), hs72]
      omega
  have outputPart (m : Ram) (hf : RamWriteFrame fr.original m fullRegions)
      (off : BitVec 64) (ho : off.toNat + 8 ≤ 64) :
      Writable code m (fr.rdi + off) 8 := by
    exact (hio.2.1.of_frame hf).of_offsets rfl (addr_self _) (by
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.sub_zero] using ho)
  have guardStack (m : Ram) (hf : RamWriteFrame fr.original m fullRegions)
      (off pc : BitVec 64) (size : Nat) (ho : off.toNat + 8 ≤ 24)
      (hp : 0x10a690 ≤ pc.toNat) (hend : pc.toNat + size ≤ 0x10aa99) :
      StoreOk code m (fr.rsp - 0x48 + off) 8 pc size := by
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      input_store_guard hcode pc.toNat size hp hend (stackPart m hf off ho)
  have guardOutput (m : Ram) (hf : RamWriteFrame fr.original m fullRegions)
      (off pc : BitVec 64) (size : Nat) (ho : off.toNat + 8 ≤ 64)
      (hp : 0x10a690 ≤ pc.toNat) (hend : pc.toNat + size ≤ 0x10aa99) :
      StoreOk code m (fr.rdi + off) 8 pc size := by
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      input_store_guard hcode pc.toNat size hp hend (outputPart m hf off ho)
  have loadInput (m : Ram) (hf : RamWriteFrame fr.original m fullRegions)
      (off : BitVec 64) (ho : off.toNat < 64) : LoadOk m (fr.rdx + off) 1 := by
    exact LoadOk.of_offsets (hio.1.of_frame hf) rfl (addr_self _) (by
      simp only [BitVec.ofNat_eq_ofNat, BitVec.sub_zero]
      omega)
  have li0 := loadInput (inputSavedMemory fr) full0
  have li1 := loadInput m1 full1
  have li2 := loadInput m2 full2
  have li3 := loadInput m3 full3
  have li0z : LoadOk (inputSavedMemory fr) fr.rdx 1 := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using li0 0 (by decide)
  have gs0 := guardStack (inputSavedMemory fr) full0
  have gs1 := guardStack m1 full1
  have gs2 (pc : BitVec 64) (size : Nat)
      (hp : 0x10a690 ≤ pc.toNat) (hend : pc.toNat + size ≤ 0x10aa99) :
      StoreOk code m2 (fr.rsp - 0x48) 8 pc size := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using guardStack m2 full2 0 pc size (by decide) hp hend
  have go3 (pc : BitVec 64) (size : Nat)
      (hp : 0x10a690 ≤ pc.toNat) (hend : pc.toNat + size ≤ 0x10aa99) :
      StoreOk code m3 fr.rdi 8 pc size := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using guardOutput m3 full3 0 pc size (by decide) hp hend
  have go4 := guardOutput m4 full4
  have go5 := guardOutput m5 full5
  have go6 := guardOutput m6 full6
  have go7 := guardOutput m7 full7
  have go8 := guardOutput m8 full8
  have go9 := guardOutput m9 full9
  have go10 := guardOutput m10 full10

  have loadStack (m : Ram) (hf : RamWriteFrame fr.original m fullRegions)
      (off : BitVec 64) (ho : 8 ≤ off.toNat ∧ off.toNat ≤ 0x48) :
      LoadOk m (fr.rsp - off) 8 := by
    apply LoadOk.of_offsets (hstack.1.readable.of_frame hf) (addr_sub _ _) (addr_sub _ _)
    have he : ((0 - off) - (0 - 0x48) : BitVec 64) = 0x48 - off :=
      sub_sub_sub_left 0 off 0x48
    rw [he, BitVec.toNat_sub_of_le (by change off.toNat ≤ 72; exact ho.2)]
    change 72 - off.toNat + 8 ≤ 72
    omega
  have ls3 := loadStack m3 full3
  have ls11 := loadStack m11 full11
  have hsepOut : fr.rdi.toNat + 64 ≤ fr.low.toNat ∨ fr.rsp.toNat + 8 ≤ fr.rdi.toNat := by
    have hd := hio.2.2.2.1 (max fr.low.toNat fr.rdi.toNat)
    simp only [Runtime.callStack, Runtime.span, MemoryRegion.Contains] at hd
    omega
  have hrOutside : Outside regions fr.rsp 8 := by
    refine ⟨by omega, ?_⟩
    intro r hr
    simp only [regions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simp only [spill, Runtime.span, hspills]
      omega
    · simp only [output, Runtime.span]
      omega
  have hrSaved : memLoad (inputSavedMemory fr) fr.rsp 64 = memLoad fr.original fr.rsp 64 := by
    simpa only [inputSavedValue, Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.sub_zero] using
      inputSavedMemory_memLoad fr ⟨0, by decide⟩
  have hr11 : memLoad m11 fr.rsp 64 = fr.ret := by
    rw [f11.memLoad_eq hrOutside, hrSaved, hstack.2.2.1]
  have lr11 : LoadOk m11 fr.rsp 8 :=
    ⟨(hstack.2.1.of_frame full11).low, (hstack.2.1.of_frame full11).present⟩
  have hn8 : fr.rsp - 0x48 + (8 : BitVec 64) = fr.rsp - 64 :=
    (sub_add_lit fr.rsp 0x48 8 (-64) (by decide +kernel)).trans
      (add_eq_sub_of_neg_eq fr.rsp (-64) 64 rfl)
  have hn16 : fr.rsp - 0x48 + (16 : BitVec 64) = fr.rsp - 56 :=
    (sub_add_lit fr.rsp 0x48 16 (-56) (by decide +kernel)).trans
      (add_eq_sub_of_neg_eq fr.rsp (-56) 56 rfl)
  have hn24 : fr.rsp - 0x48 + (24 : BitVec 64) = fr.rsp - 48 :=
    (sub_add_lit fr.rsp 0x48 24 (-48) (by decide +kernel)).trans
      (add_eq_sub_of_neg_eq fr.rsp (-48) 48 rfl)
  have hn32 : fr.rsp - 0x48 + (32 : BitVec 64) = fr.rsp - 40 :=
    (sub_add_lit fr.rsp 0x48 32 (-40) (by decide +kernel)).trans
      (add_eq_sub_of_neg_eq fr.rsp (-40) 40 rfl)
  have hn40 : fr.rsp - 0x48 + (40 : BitVec 64) = fr.rsp - 32 :=
    (sub_add_lit fr.rsp 0x48 40 (-32) (by decide +kernel)).trans
      (add_eq_sub_of_neg_eq fr.rsp (-32) 32 rfl)
  have hn48 : fr.rsp - 0x48 + (48 : BitVec 64) = fr.rsp - 24 :=
    (sub_add_lit fr.rsp 0x48 48 (-24) (by decide +kernel)).trans
      (add_eq_sub_of_neg_eq fr.rsp (-24) 24 rfl)
  have hn56 : fr.rsp - 0x48 + (56 : BitVec 64) = fr.rsp - 16 :=
    (sub_add_lit fr.rsp 0x48 56 (-16) (by decide +kernel)).trans
      (add_eq_sub_of_neg_eq fr.rsp (-16) 16 rfl)
  have hn64 : fr.rsp - 0x48 + (64 : BitVec 64) = fr.rsp - 8 :=
    (sub_add_lit fr.rsp 0x48 64 (-8) (by decide +kernel)).trans
      (add_eq_sub_of_neg_eq fr.rsp (-8) 8 rfl)
  have hn72 : fr.rsp - 0x48 + (72 : BitVec 64) = fr.rsp :=
    BitVec.sub_add_cancel fr.rsp 0x48
  have hn80 : fr.rsp - 0x48 + (80 : BitVec 64) = fr.rsp + 8 :=
    sub_add_lit fr.rsp 0x48 80 8 (by decide +kernel)

  simp (config := { maxSteps := 1000000, zetaDelta := false }) (disch := decide +kernel) only [↓inputReturned_stop, li0, li1, li2, li3, li0z,
    gs0, gs1, gs2, go3, go4, go5, go6, go7, go8, go9, go10, ↓reduceIte] at he
  simp only [↓inputReturned_stop, hn8, hn16, hn24, hn32, hn40, hn48, hn56, hn64, hn72] at he
  simp (config := { maxSteps := 1000000, zetaDelta := false }) (disch := decide +kernel) only [↓inputReturned_stop, ls3, ls11, lr11,
    hr11, hstack.2.2.2.1, and_self, ↓reduceIte] at he
  have slotOutside (j : Fin 7) :
      Outside regions (fr.rsp - BitVec.ofNat 64 (8 * j.val)) 8 := by
    have hj := j.isLt
    have ha := hsub (8 * j.val) (by omega)
    refine ⟨by rw [ha]; omega, ?_⟩
    intro r hr
    simp only [regions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simp only [spill, Runtime.span, hspills, ha]
      omega
    · simp only [output, Runtime.span, ha]
      omega
  have savedSlot (j : Fin 7) :
      memLoad m11 (fr.rsp - BitVec.ofNat 64 (8 * j.val)) 64 = inputSavedValue fr j := by
    rw [f11.memLoad_eq (slotOutside j), inputSavedMemory_memLoad]
  have hs3 : memLoad m11 (fr.rsp - 48) 64 = fr.rbx := by
    simpa only [inputSavedValue, Nat.reduceMul, BitVec.ofNat_eq_ofNat] using
      savedSlot (⟨6, by decide⟩ : Fin 7)
  have hs5 : memLoad m11 (fr.rsp - 8) 64 = fr.rbp := by
    simpa only [inputSavedValue, Nat.reduceMul, BitVec.ofNat_eq_ofNat] using
      savedSlot (⟨1, by decide⟩ : Fin 7)
  have hs12 : memLoad m11 (fr.rsp - 40) 64 = fr.r12 := by
    simpa only [inputSavedValue, Nat.reduceMul, BitVec.ofNat_eq_ofNat] using
      savedSlot (⟨5, by decide⟩ : Fin 7)
  have hs13 : memLoad m11 (fr.rsp - 32) 64 = fr.r13 := by
    simpa only [inputSavedValue, Nat.reduceMul, BitVec.ofNat_eq_ofNat] using
      savedSlot (⟨4, by decide⟩ : Fin 7)
  have hs14 : memLoad m11 (fr.rsp - 24) 64 = fr.r14 := by
    simpa only [inputSavedValue, Nat.reduceMul, BitVec.ofNat_eq_ofNat] using
      savedSlot (⟨3, by decide⟩ : Fin 7)
  have hs15 : memLoad m11 (fr.rsp - 16) 64 = fr.r15 := by
    simpa only [inputSavedValue, Nat.reduceMul, BitVec.ofNat_eq_ofNat] using
      savedSlot (⟨2, by decide⟩ : Fin 7)
  have hsepIn : fr.rdx.toNat + 64 ≤ fr.low.toNat ∨ fr.rsp.toNat + 8 ≤ fr.rdx.toNat := by
    have hd := hio.2.2.1 (max fr.low.toNat fr.rdx.toNat)
    simp only [Runtime.callStack, Runtime.span, MemoryRegion.Contains] at hd
    omega
  have hsepIO : fr.rdi.toNat + 64 ≤ fr.rdx.toNat ∨ fr.rdx.toNat + 64 ≤ fr.rdi.toNat := by
    have hd := hio.2.2.2.2 (max fr.rdi.toNat fr.rdx.toNat)
    simp only [Runtime.span, MemoryRegion.Contains] at hd
    omega
  have byteOutside (off : BitVec 64) (ho : off.toNat < 64) :
      Outside fullRegions (fr.rdx + off) 1 := by
    have hb := hio.1.low
    have ha : (fr.rdx + off).toNat = fr.rdx.toNat + off.toNat :=
      BitVec.toNat_add_of_lt (by omega)
    refine ⟨by rw [ha]; omega, ?_⟩
    intro r hr
    simp only [fullRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · simp only [Activation.region, ha]
      omega
    · simp only [output, Runtime.span, ha]
      omega
  have bytes0 (off : BitVec 64) (ho : off.toNat < 64) :
      memLoad (inputSavedMemory fr) (args[2].get 64 + off) 8 =
        memLoad fr.original (fr.rdx + off) 8 := by
    rw [h2]
    exact full0.memLoad_eq (byteOutside off ho)
  have bytes1 (off : BitVec 64) (ho : off.toNat < 64) :
      memLoad m1 (args[2].get 64 + off) 8 = memLoad fr.original (fr.rdx + off) 8 := by
    rw [h2]
    exact full1.memLoad_eq (byteOutside off ho)
  have bytes2 (off : BitVec 64) (ho : off.toNat < 64) :
      memLoad m2 (args[2].get 64 + off) 8 = memLoad fr.original (fr.rdx + off) 8 := by
    rw [h2]
    exact full2.memLoad_eq (byteOutside off ho)
  have bytes3 (off : BitVec 64) (ho : off.toNat < 64) :
      memLoad m3 (args[2].get 64 + off) 8 = memLoad fr.original (fr.rdx + off) 8 := by
    rw [h2]
    exact full3.memLoad_eq (byteOutside off ho)
  have hdataFn := inputBody_data args (inputSavedMemory fr) fr.original fr.rdx
  extract_lets pack0 n1 pack1 n2 pack2 n3 pack3 pack4 pack5 pack6 pack7
    n4 n5 n6 n7 n8 n9 n10 n11 at hdataFn
  have hm1 : m1 = n1 := by rfl
  have hm2 : m2 = n2 := by rfl
  have hm3 : m3 = n3 := by rfl
  have hm4 : m4 = n4 := by
    refine congr (congrArg (fun (m : Ram) (v : BitVec 64) ↦ memStore m (args[7].get 64) v) hm3) ?_ <;>
      simp only [hm1, hm2, hm3] <;> rfl
  have hm5 : m5 = n5 := by
    refine congr (congrArg (fun (m : Ram) (v : BitVec 64) ↦ memStore m (args[7].get 64 + 8) v) hm4) ?_ <;>
      simp only [hm1, hm2, hm3] <;> rfl
  have hm6 : m6 = n6 := by
    refine congr (congrArg (fun (m : Ram) (v : BitVec 64) ↦ memStore m (args[7].get 64 + 16) v) hm5) ?_ <;>
      simp only [hm1, hm2, hm3] <;> rfl
  have hm7 : m7 = n7 := by
    refine congr (congrArg (fun (m : Ram) (v : BitVec 64) ↦ memStore m (args[7].get 64 + 24) v) hm6) ?_ <;>
      simp only [hm1, hm2, hm3] <;> rfl
  have hm8 : m8 = n8 := by
    refine congr (congrArg (fun (m : Ram) (v : BitVec 64) ↦ memStore m (args[7].get 64 + 32) v) hm7) ?_ <;>
      simp only [hm1, hm2, hm3] <;> rfl
  have hm9 : m9 = n9 := by
    refine congr (congrArg (fun (m : Ram) (v : BitVec 64) ↦ memStore m (args[7].get 64 + 40) v) hm8) ?_ <;>
      simp only [hm1, hm2, hm3] <;> rfl
  have hm10 : m10 = n10 := by
    refine congr (congrArg (fun (m : Ram) (v : BitVec 64) ↦ memStore m (args[7].get 64 + 48) v) hm9) ?_ <;>
      simp only [hm1, hm2, hm3] <;> rfl
  have hm11 : m11 = n11 := by
    refine congr (congrArg (fun (m : Ram) (v : BitVec 64) ↦ memStore m (args[7].get 64 + 56) v) hm10) ?_ <;>
      simp only [hm1, hm2, hm3] <;> rfl
  have b1 (off : BitVec 64) (ho : off.toNat < 64) :
      memLoad n1 (args[2].get 64 + off) 8 = memLoad fr.original (fr.rdx + off) 8 := by
    exact (congrArg (fun m : Ram ↦ memLoad m (args[2].get 64 + off) 8) hm1.symm).trans
      (bytes1 off ho)
  have b2 (off : BitVec 64) (ho : off.toNat < 64) :
      memLoad n2 (args[2].get 64 + off) 8 = memLoad fr.original (fr.rdx + off) 8 := by
    exact (congrArg (fun m : Ram ↦ memLoad m (args[2].get 64 + off) 8) hm2.symm).trans
      (bytes2 off ho)
  have b3 (off : BitVec 64) (ho : off.toNat < 64) :
      memLoad n3 (args[2].get 64 + off) 8 = memLoad fr.original (fr.rdx + off) 8 := by
    exact (congrArg (fun m : Ram ↦ memLoad m (args[2].get 64 + off) 8) hm3.symm).trans
      (bytes3 off ho)
  have hnData := hdataFn bytes0 b1 b2 b3
  have hdata : m11 = inputStoredPlanes m3 (args[7].get 64)
      (bitslice (memoryBlocks fr.original fr.rdx)) := by
    exact hm11.trans (hnData.trans (congrArg
      (fun m ↦ inputStoredPlanes m (args[7].get 64)
        (bitslice (memoryBlocks fr.original fr.rdx))) hm3.symm))
  rw [h7, bitslice_eq_encode] at hdata
  refine ⟨_, he, ?_, ?_, full11, ?_, ?_⟩
  · simp only [hsp, hn72, hr11]
  · refine ⟨?_, hdf, ?_, ?_, ?_, ?_, ?_, ?_, hfp.1, hfp.2.1, hfp.2.2, trivial⟩
    · change (⟨64, args[4].get 64 + 80⟩ : Value) = ⟨64, fr.rsp + 8⟩
      rw [hsp, hn80]
    · change (⟨64, memLoad m11 (args[4].get 64 + 24) 64⟩ : Value) = ⟨64, fr.rbx⟩
      rw [hsp, hn24, hs3]
    · change (⟨64, memLoad m11 (args[4].get 64 + 64) 64⟩ : Value) = ⟨64, fr.rbp⟩
      rw [hsp, hn64, hs5]
    · change (⟨64, memLoad m11 (args[4].get 64 + 32) 64⟩ : Value) = ⟨64, fr.r12⟩
      rw [hsp, hn32, hs12]
    · change (⟨64, memLoad m11 (args[4].get 64 + 40) 64⟩ : Value) = ⟨64, fr.r13⟩
      rw [hsp, hn40, hs13]
    · change (⟨64, memLoad m11 (args[4].get 64 + 48) 64⟩ : Value) = ⟨64, fr.r14⟩
      rw [hsp, hn48, hs14]
    · change (⟨64, memLoad m11 (args[4].get 64 + 56) 64⟩ : Value) = ⟨64, fr.r15⟩
      rw [hsp, hn56, hs15]
  · exact of_decide_eq_true rfl
  · intro p
    change memLoad m11 (fr.rdi + BitVec.ofNat 64 (8 * p.val)) 64 = _
    rw [hdata]
    exact inputStoredPlanes_memLoad _ _ _ p

theorem input_call (code : CodeMap) (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) :
    Runtime.CallContract LIR.lifted code .l10a690 LIR.Fn10a690.frameInfo
      (fun fr ↦ [Runtime.span fr.rdi 64])
      (fun fr mem ↦ fr.rsi = 8 ∧ Readable mem fr.rdx 64 ∧
        Writable code mem fr.rdi 64 ∧
        (Runtime.callStack fr).Disjoint (Runtime.span fr.rdi 64) ∧
        (Runtime.callStack fr).Disjoint (Runtime.span fr.rdx 64) ∧
        (Runtime.span fr.rdi 64).Disjoint (Runtime.span fr.rdx 64))
      (fun fr mem ↦ ∀ p : Fin 8,
        memLoad mem (fr.rdi + BitVec.ofNat 64 (8 * p.val)) 64 =
          encode (memoryBlocks fr.original fr.rdx) p) := by
  intro fr loc hl hm hentry _htyped hp
  rcases loc with ⟨label, args, mem⟩
  cases hl
  cases hm
  change Atom.All code args fr.original (LIR.Fn10a690.frameAt .l10a690 fr) at hentry
  simp only [LIR.Fn10a690.frameAt, LIR.Fn10a690.frameAtG7,
    Atom.All, Atom.Holds] at hentry
  rcases hentry with ⟨hsp, hdf, _hcx, hdx, hbx, hbp, hsi, hdi, _h8, _h9,
    h12, h13, h14, h15, h39, h50, h51, hreadret, hmemret, hretLow, hwstack, hroom, _halign, _htrue⟩
  rcases hp with ⟨hlen, hread, hwrite, hStackOut, hStackIn, hOutIn⟩
  have get_eq (r : Fin Reg.count) (v : BitVec 64) (h : args[r] = ⟨64, v⟩) :
      args[r].get 64 = v := by
    rw [h]
    exact BitVec.setWidth_eq v
  have hsave : ∀ r ∈ ([3, 5, 12, 13, 14, 15] : List (Fin Reg.count)),
      args[r].get 64 = fr.entryReg r.val := by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · change args[3].get 64 = fr.rbx
      exact get_eq _ _ hbx
    · change args[5].get 64 = fr.rbp
      exact get_eq _ _ hbp
    · change args[12].get 64 = fr.r12
      exact get_eq _ _ h12
    · change args[13].get 64 = fr.r13
      exact get_eq _ _ h13
    · change args[14].get 64 = fr.r14
      exact get_eq _ _ h14
    · change args[15].get 64 = fr.r15
      exact get_eq _ _ h15
  have hlen8 : args[6].get 64 = 8 := (get_eq _ _ hsi).trans hlen
  obtain ⟨bodyArgs, hstart, hbodySp, hbodyDx, hbodyDi, hbodyDf, hbody39, hbody50, hbody51⟩ :=
    inputEntry_runBlock code hcode args fr (get_eq _ _ hsp) hsave hlen8 hwstack
  have bodySp : bodyArgs[4].get 64 = fr.rsp - 0x48 := by
    rw [hbodySp]
    exact BitVec.setWidth_eq _
  have bodyDx : bodyArgs[2].get 64 = fr.rdx := by
    rw [hbodyDx]
    exact get_eq _ _ hdx
  have bodyDi : bodyArgs[7].get 64 = fr.rdi := by
    rw [hbodyDi]
    exact get_eq _ _ hdi
  obtain ⟨out, hbody, htag, hdone, hframe, hwidth, hdata⟩ :=
    inputBody_runBlock code hcode bodyArgs fr ⟨bodySp, bodyDx, bodyDi⟩ (hbodyDf.trans hdf)
      ⟨hbody39.trans h39, hbody50.trans h50, hbody51.trans h51⟩
      ⟨hwstack, hreadret, hmemret, hretLow, hroom⟩
      ⟨hread, hwrite, hStackIn, hStackOut, hOutIn⟩
  refine ⟨out, ?_, htag, hdone, hwidth, hframe, hdata⟩
  refine Program.Exec.next
    (congrArg (fun t ↦ t.next (dialect code) []) hstart) ?_
  exact Program.Exec.done (congrArg (fun t ↦ t.next (dialect code) []) hbody)


end AesGcm.Proofs.Machine.AES64

namespace AesGcm.Proofs.Machine.AES64

open X86 X86.Machine X86Proofs X86Proofs.Refine
open AesGcm.Proofs.Machine.Fixslice

theorem memoryBlocks_eq_fromStandard {mem : Ram} {ptr : BitVec 64}
    {blocks : Vector Standards.NIST.AES.Block 4}
    (h : AesGcm.Proofs.Machine.Runtime.BlocksIn mem ptr blocks) :
    memoryBlocks mem ptr = fromStandard (fun b ↦ blocks[b.val]) := by
  funext b j
  have hb := congrArg (fun o : Option UInt8 ↦ (o.getD 0).toBitVec) (h b j)
  simpa only [memoryBlocks, memoryBlock, fromStandard, Fin.getElem_fin,
    BitVec.add_assoc, ← BitVec.ofNat_add, memByte, PhysicalMemory.read, Option.getD_some] using hb

theorem blocksIn_of_memoryBlocks_eq {mem : Ram} {ptr : BitVec 64}
    {blocks : Vector Standards.NIST.AES.Block 4}
    (hr : Readable mem ptr 64)
    (h : memoryBlocks mem ptr = fromStandard (fun b ↦ blocks[b.val])) :
    AesGcm.Proofs.Machine.Runtime.BlocksIn mem ptr blocks := by
  intro b j
  have hp := hr.present (16 * b.val + j.val) (by omega)
  cases hm : mem[ptr + BitVec.ofNat 64 (16 * b.val + j.val)]? with
  | none => simp only [hm, Option.isSome_none, Bool.false_eq_true] at hp
  | some byte =>
    have hb := congrFun (congrFun h b) j
    have he : byte.toBitVec = blocks[b.val][j.val].toBitVec := by
      simpa only [memoryBlocks, memoryBlock, fromStandard, Fin.getElem_fin,
        BitVec.add_assoc, ← BitVec.ofNat_add, memByte, PhysicalMemory.read, hm,
        Option.getD_some] using hb
    simpa only [Fin.getElem_fin] using congrArg some (UInt8.eq_of_toBitVec_eq he)

end AesGcm.Proofs.Machine.AES64
