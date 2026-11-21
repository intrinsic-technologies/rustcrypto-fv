import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.OneCopy
import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.Modulus
import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.Constants

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.ExponentInitialize

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field.Montgomery.Schoolbook (memLoad_memStore_rangeApart)

def windowMemory (s : RamState) (memory : Ram) : Ram :=
  constantsMemory s (modulusMemory s
    (memStore (oneCopyMemory s memory) (exponentFrameBase s+120) (16#32)))

def setupMemory (s : RamState) (memory : Ram) : Ram :=
  memStore (windowMemory s memory) (exponentFrameBase s+704) (3#64)

theorem setupMemory_modulus0 (s : RamState) (memory : Ram) :
    memLoad (setupMemory s memory) (exponentFrameBase s+136#64) 64=0xffffffffffffffff := by
  simp only [setupMemory,windowMemory,constantsMemory,modulusMemory,oneCopyMemory,
    List.foldl_cons,List.foldl_nil,Nat.reduceAdd,BitVec.ofNat_eq_ofNat]
  repeat first
    | rw [memLoad_memStore_rangeApart _ _ _ _ 64
        (RangeApart.offsets (exponentFrameBase s) (by omega) (by omega) (by omega))]
    | rw [memLoad_memStore _ _ (by decide) (by decide) _]

theorem setupMemory_modulus1 (s : RamState) (memory : Ram) :
    memLoad (setupMemory s memory) (exponentFrameBase s+128#64) 64=0xffffffff := by
  simp only [setupMemory,windowMemory,constantsMemory,modulusMemory,oneCopyMemory,
    List.foldl_cons,List.foldl_nil,Nat.reduceAdd,BitVec.ofNat_eq_ofNat]
  repeat first
    | rw [memLoad_memStore_rangeApart _ _ _ _ 64
        (RangeApart.offsets (exponentFrameBase s) (by omega) (by omega) (by omega))]
    | rw [memLoad_memStore _ _ (by decide) (by decide) _]

theorem setupMemory_modulus2 (s : RamState) (memory : Ram) :
    memLoad (setupMemory s memory) (exponentFrameBase s+152#64) 64=0 := by
  simp only [setupMemory,windowMemory,constantsMemory,modulusMemory,oneCopyMemory,
    List.foldl_cons,List.foldl_nil,Nat.reduceAdd,BitVec.ofNat_eq_ofNat]
  repeat first
    | rw [memLoad_memStore_rangeApart _ _ _ _ 64
        (RangeApart.offsets (exponentFrameBase s) (by omega) (by omega) (by omega))]
    | rw [memLoad_memStore _ _ (by decide) (by decide) _]

theorem setupMemory_modulus3 (s : RamState) (memory : Ram) :
    memLoad (setupMemory s memory) (exponentFrameBase s+144#64) 64=0xffffffff00000001 := by
  simp only [setupMemory,windowMemory,constantsMemory,modulusMemory,oneCopyMemory,
    List.foldl_cons,List.foldl_nil,Nat.reduceAdd,BitVec.ofNat_eq_ofNat]
  repeat first
    | rw [memLoad_memStore_rangeApart _ _ _ _ 64
        (RangeApart.offsets (exponentFrameBase s) (by omega) (by omega) (by omega))]
    | rw [memLoad_memStore _ _ (by decide) (by decide) _]

theorem setupMemory_firstWindow (s : RamState) (memory : Ram) :
    memLoad (setupMemory s memory) (exponentFrameBase s+680#64) 64=15 := by
  simp only [setupMemory,windowMemory,constantsMemory,modulusMemory,oneCopyMemory,
    List.foldl_cons,List.foldl_nil,Nat.reduceAdd,BitVec.ofNat_eq_ofNat]
  repeat first
    | rw [memLoad_memStore_rangeApart _ _ _ _ 64
        (RangeApart.offsets (exponentFrameBase s) (by omega) (by omega) (by omega))]
    | rw [memLoad_memStore _ _ (by decide) (by decide) _]

theorem setupMemory_parameter (s : RamState) (memory : Ram) :
    memLoad (setupMemory s memory) (exponentFrameBase s+696#64) 64=s.regValue .rsi+32 := by
  simp only [setupMemory,windowMemory,constantsMemory,modulusMemory,oneCopyMemory,
    List.foldl_cons,List.foldl_nil,Nat.reduceAdd,BitVec.ofNat_eq_ofNat]
  repeat first
    | rw [memLoad_memStore_rangeApart _ _ _ _ 64
        (RangeApart.offsets (exponentFrameBase s) (by omega) (by omega) (by omega))]
    | rw [memLoad_memStore _ _ (by decide) (by decide) _]

theorem setupMemory_firstWord (s : RamState) (memory : Ram) :
    memLoad (setupMemory s memory) (exponentFrameBase s+688#64) 64=3 := by
  simp only [setupMemory,windowMemory,constantsMemory,modulusMemory,oneCopyMemory,
    List.foldl_cons,List.foldl_nil,Nat.reduceAdd,BitVec.ofNat_eq_ofNat]
  repeat first
    | rw [memLoad_memStore_rangeApart _ _ _ _ 64
        (RangeApart.offsets (exponentFrameBase s) (by omega) (by omega) (by omega))]
    | rw [memLoad_memStore _ _ (by decide) (by decide) _]

theorem setupMemory_inverse (s : RamState) (memory : Ram) :
    memLoad (setupMemory s memory) (exponentFrameBase s+736#64) 64=0xffffffffffffffff := by
  simp only [setupMemory,windowMemory,constantsMemory,modulusMemory,oneCopyMemory,
    List.foldl_cons,List.foldl_nil,Nat.reduceAdd,BitVec.ofNat_eq_ofNat]
  repeat first
    | rw [memLoad_memStore_rangeApart _ _ _ _ 64
        (RangeApart.offsets (exponentFrameBase s) (by omega) (by omega) (by omega))]
    | rw [memLoad_memStore _ _ (by decide) (by decide) _]

theorem setupMemory_mask (s : RamState) (memory : Ram) :
    memLoad (setupMemory s memory) (exponentFrameBase s+728#64) 64=3 := by
  simp only [setupMemory,windowMemory,constantsMemory,modulusMemory,oneCopyMemory,
    List.foldl_cons,List.foldl_nil,Nat.reduceAdd,BitVec.ofNat_eq_ofNat]
  repeat first
    | rw [memLoad_memStore_rangeApart _ _ _ _ 64
        (RangeApart.offsets (exponentFrameBase s) (by omega) (by omega) (by omega))]
    | rw [memLoad_memStore _ _ (by decide) (by decide) _]

theorem setupMemory_word (s : RamState) (memory : Ram) :
    memLoad (setupMemory s memory) (exponentFrameBase s+704#64) 64=3 := by
  simp only [setupMemory,windowMemory,constantsMemory,modulusMemory,oneCopyMemory,
    List.foldl_cons,List.foldl_nil,Nat.reduceAdd,BitVec.ofNat_eq_ofNat]
  repeat first
    | rw [memLoad_memStore_rangeApart _ _ _ _ 64
        (RangeApart.offsets (exponentFrameBase s) (by omega) (by omega) (by omega))]
    | rw [memLoad_memStore _ _ (by decide) (by decide) _]

theorem windowMemory_window (s : RamState) (memory : Ram) :
    memLoad (windowMemory s memory) (exponentFrameBase s+120#64) 32=16 := by
  simp only [windowMemory,constantsMemory,modulusMemory,oneCopyMemory,
    List.foldl_cons,List.foldl_nil,Nat.reduceAdd,BitVec.ofNat_eq_ofNat]
  repeat first
    | rw [memLoad_memStore_rangeApart _ _ _ _ 32
        (RangeApart.offsets (exponentFrameBase s) (by omega) (by omega) (by omega))]
    | rw [memLoad_memStore _ _ (by decide) (by decide) _]

theorem setupMemory_window (s : RamState) (memory : Ram) :
    memLoad (setupMemory s memory) (exponentFrameBase s+120#64) 32=16 := by
  simp only [setupMemory,windowMemory,constantsMemory,modulusMemory,oneCopyMemory,
    List.foldl_cons,List.foldl_nil,Nat.reduceAdd,BitVec.ofNat_eq_ofNat]
  repeat first
    | rw [memLoad_memStore_rangeApart _ _ _ _ 32
        (RangeApart.offsets (exponentFrameBase s) (by omega) (by omega) (by omega))]
    | rw [memLoad_memStore _ _ (by decide) (by decide) _]

theorem setupMemory_output (s : RamState) (memory : Ram) :
    memLoad (setupMemory s memory) (exponentFrameBase s+672#64) 64=
      memLoad memory (exponentFrameBase s+672#64) 64 := by
  simp only [setupMemory,windowMemory,constantsMemory,modulusMemory,oneCopyMemory,
    List.foldl_cons,List.foldl_nil,Nat.reduceAdd,BitVec.ofNat_eq_ofNat]
  repeat first
    | rw [memLoad_memStore_rangeApart _ _ _ _ 64
        (RangeApart.offsets (exponentFrameBase s) (by omega) (by omega) (by omega))]
    | rw [memLoad_memStore _ _ (by decide) (by decide) _]

theorem setupMemory_negativeInverse (s : RamState) (memory : Ram) :
    memLoad (setupMemory s memory) (exponentFrameBase s+712#64) 64=
      memLoad memory (exponentFrameBase s+712#64) 64 := by
  simp only [setupMemory,windowMemory,constantsMemory,modulusMemory,oneCopyMemory,
    List.foldl_cons,List.foldl_nil,Nat.reduceAdd,BitVec.ofNat_eq_ofNat]
  repeat first
    | rw [memLoad_memStore_rangeApart _ _ _ _ 64
        (RangeApart.offsets (exponentFrameBase s) (by omega) (by omega) (by omega))]
    | rw [memLoad_memStore _ _ (by decide) (by decide) _]

theorem setupMemory_one (s : RamState) (memory : Ram) {j : Nat} (hj : j<4) :
    memLoad (setupMemory s memory) (exponentFrameBase s+BitVec.ofNat 64 (48+8*j)) 64=
      memLoad s.external (s.regValue .rsi+BitVec.ofNat 64 (64+8*j)) 64 := by
  have cases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
  rcases cases with rfl | rfl | rfl | rfl
  all_goals
    simp only [setupMemory,windowMemory,constantsMemory,modulusMemory,oneCopyMemory,
      List.foldl_cons,List.foldl_nil,Nat.reduceAdd,Nat.reduceMul,BitVec.ofNat_eq_ofNat]
    repeat first
      | rw [memLoad_memStore_rangeApart _ _ _ _ 64
          (RangeApart.offsets (exponentFrameBase s) (by omega) (by omega) (by omega))]
      | rw [memLoad_memStore _ _ (by decide) (by decide) _]

theorem lower_store_byte (s : RamState) (memory : Ram) {a off n : Nat} (v : BitVec n)
    (ha : a+n/8≤824) (lo : 824≤off) (hi : off<1368) :
    (memStore memory (exponentFrameBase s+BitVec.ofNat 64 a) v)[exponentFrameBase s+BitVec.ofNat 64 off]?=
      memory[exponentFrameBase s+BitVec.ofNat 64 off]? := by
  apply memStore_getElem?_of_ne
  intro j hj
  have h : RangeApart (exponentFrameBase s+BitVec.ofNat 64 a) (n/8)
      (exponentFrameBase s+BitVec.ofNat 64 off) 1 :=
    RangeApart.offsets (exponentFrameBase s) (by omega) (by omega) (by omega)
  simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_zero] using h j hj 0 (by decide)

theorem setupMemory_byte (s : RamState) (memory : Ram) {off : Nat}
    (lo : 824≤off) (hi : off<1368) :
    (setupMemory s memory)[exponentFrameBase s+BitVec.ofNat 64 off]?=
      memory[exponentFrameBase s+BitVec.ofNat 64 off]? := by
  simp only [setupMemory,windowMemory,constantsMemory,modulusMemory,oneCopyMemory,
    List.foldl_cons,List.foldl_nil,Nat.reduceAdd,BitVec.ofNat_eq_ofNat]
  repeat rw [lower_store_byte s _ _ (by omega) lo hi]


end P256.Proofs.Sec1.SquareRoot.ExponentInitialize
