import AesGcm.Proofs.Machine.Runtime.Contracts
import AesGcm.Proofs.Machine.AES64.Input
import AesGcm.Proofs.Machine.LIR.Program
import AesGcm.Proofs.Machine.Runtime.Guards
import AesGcm.Proofs.Copied.X86Proofs.Lift.Generated.Values
import AesGcm.Proofs.Machine.Fixslice.Memory
import AesGcm.Proofs.Machine.Fixslice.Conversion
import AesGcm.Proofs.Copied.X86Proofs.Refine.Frame
import AesGcm.Proofs.Copied.X86Proofs.Refine.Lemma.Store

namespace AesGcm.Proofs.Machine.AES64

open AesGcm.Proofs.Machine.Fixslice AesGcm.Proofs.Machine.Runtime
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.Lift X86Proofs.Refine

def outputStoredBytes (m : Ram) (dst : BitVec 64) (x : Planes) : Ram :=
  (List.range 64).foldl (fun m i ↦ memStore m (dst + BitVec.ofNat 64 i)
    (invBitslice x ⟨i / 16 % 4, by omega⟩ ⟨i % 16, by omega⟩)) m

theorem outputStoredBytes_getElem? (m : Ram) (dst : BitVec 64) (x : Planes) (i : Fin 64) :
    (outputStoredBytes m dst x)[dst + BitVec.ofNat 64 i.val]? =
      some (UInt8.ofBitVec (invBitslice x ⟨i.val / 16, by omega⟩ ⟨i.val % 16, by omega⟩)) := by
  let f := fun (m : Ram) (j : Nat) ↦ memStore m (dst + BitVec.ofNat 64 j)
    (invBitslice x ⟨j / 16 % 4, by omega⟩ ⟨j % 16, by omega⟩)
  let b := UInt8.ofBitVec (invBitslice x ⟨i.val / 16, by omega⟩ ⟨i.val % 16, by omega⟩)
  have step (m' : Ram) (j : Nat) (hj : j < 64) :
      (f m' j)[dst + BitVec.ofNat 64 i.val]? =
        if j = i.val then some b else m'[dst + BitVec.ofNat 64 i.val]? := by
    dsimp only [f]
    by_cases he : j = i.val
    · subst j
      rw [ite_eq_left rfl]
      have hm := memStore_getElem?_self m' (dst + BitVec.ofNat 64 i.val)
        (invBitslice x ⟨i.val / 16 % 4, by omega⟩ ⟨i.val % 16, by omega⟩)
        (by decide) 0 (by decide)
      simpa only [BitVec.add_zero, Nat.mod_eq_of_lt (show i.val / 16 < 4 by omega),
        storedByte, Nat.mul_zero, Nat.shiftRight_zero, UInt8.ofNat_bitVecToNat, b] using hm
    · rw [ite_eq_right he]
      apply memStore_getElem?_of_ne
      intro k hk haddr
      have hk0 : k = 0 := by omega
      subst k
      rw [BitVec.add_zero] at haddr
      exact he (add_ofNat_inj dst (by omega) (by omega) haddr)
  have hstores (n : Nat) (hn : n ≤ 64) :
      ((List.range n).foldl f m)[dst + BitVec.ofNat 64 i.val]? =
        if i.val < n then some b else m[dst + BitVec.ofNat 64 i.val]? := by
    induction n with
    | zero => simp only [List.range_zero, List.foldl_nil, Nat.not_lt_zero, ite_false]
    | succ n ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      rw [step _ n (by omega), ih (by omega)]
      by_cases he : n = i.val
      · rw [ite_eq_left he, ite_eq_left (show i.val < n + 1 by omega)]
      · rw [ite_eq_right he]
        by_cases hi : i.val < n
        · rw [ite_eq_left hi, ite_eq_left (show i.val < n + 1 by omega)]
        · rw [ite_eq_right hi, ite_eq_right (show ¬ i.val < n + 1 by omega)]
  exact (hstores 64 (by omega)).trans (ite_eq_left i.isLt)

theorem outputStoredBytes_frame {original m : Ram} {dst : BitVec 64}
    {regions : List MemoryRegion} (x : Planes) (hf : RamWriteFrame original m regions)
    (hin : InRegions regions dst 64) :
    RamWriteFrame original (outputStoredBytes m dst x) regions := by
  obtain ⟨r, hr, hlo, hhi, hwrap⟩ := hin
  have byte_in (j : Nat) (hj : j < 64) :
      InRegions regions (dst + BitVec.ofNat 64 j) 1 := by
    have he : (dst + BitVec.ofNat 64 j).toNat = dst.toNat + j := by
      rw [BitVec.toNat_add, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show j < 2 ^ 64 by omega), Nat.mod_eq_of_lt (by omega)]
    exact ⟨r, hr, by simp only [InRegion, he]; omega⟩
  let f := fun (m : Ram) (j : Nat) ↦ memStore m (dst + BitVec.ofNat 64 j)
    (invBitslice x ⟨j / 16 % 4, by omega⟩ ⟨j % 16, by omega⟩)
  have hstores (n : Nat) (hn : n ≤ 64) :
      RamWriteFrame original ((List.range n).foldl f m) regions := by
    induction n with
    | zero => exact hf
    | succ n ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      exact (ih (by omega)).memStore _ (byte_in n (by omega))
  exact hstores 64 (by omega)

theorem memoryBlocks_outputStoredBytes (m : Ram) (dst : BitVec 64) (x : Planes) :
    memoryBlocks (outputStoredBytes m dst x) dst = decode x := by
  rw [← invBitslice_eq_decode]
  funext b j
  have hi : 16 * b.val + j.val < 64 := by omega
  have hm := outputStoredBytes_getElem? m dst x ⟨16 * b.val + j.val, hi⟩
  have hb : (16 * b.val + j.val) / 16 = b.val := by omega
  have hj : (16 * b.val + j.val) % 16 = j.val := by omega
  simp only [hb, hj] at hm
  simp only [memoryBlocks, memoryBlock, BitVec.add_assoc, ← BitVec.ofNat_add,
    memByte, PhysicalMemory.read, hm, Option.getD_some, UInt8.toBitVec_ofBitVec]

theorem outputStoredBytes_memLoad {m : Ram} {dst a : BitVec 64} (x : Planes) (k : Nat)
    (hsep : RangeApart dst 64 a (k / 8)) :
    memLoad (outputStoredBytes m dst x) a k = memLoad m a k := by
  have hfold (n : Nat) (hn : n ≤ 64) :
      memLoad ((List.range n).foldl (fun m i ↦ memStore m (dst + BitVec.ofNat 64 i)
        (invBitslice x ⟨i / 16 % 4, by omega⟩ ⟨i % 16, by omega⟩)) m) a k =
        memLoad m a k := by
    induction n with
    | zero => rfl
    | succ n ih =>
      rw [List.range_succ, List.foldl_append]
      simp only [List.foldl_cons, List.foldl_nil]
      apply Eq.trans (memLoad_memStore_of_rangeApart _ _ _ _ k ?_) (ih (by omega))
      intro i hi j hj he
      apply hsep (n + i) (by omega) j hj
      rw [BitVec.ofNat_add, ← BitVec.add_assoc]
      exact he
  exact hfold 64 (by omega)

end AesGcm.Proofs.Machine.AES64

namespace AesGcm.Proofs.Machine.LIR.Fn10a210

open X86Proofs

def frameInfo : Refine.FrameInfo where
  entry := 0x10a210
  frameBytes := 0x38
  stackBytes := some 0xc0
  slots := [(3, 0x30), (5, 0x8), (12, 0x28), (13, 0x20), (14, 0x18), (15, 0x10)]
  preserved := [3, 5, 12, 13, 14, 15]
  fpPreserved := [39, 50, 51]
  clobbers := [0, 1, 2, 6, 8, 9, 10, 11]
  callSlots := [(0x201210, 0x103880), (0x201230, 0x101230)]

end AesGcm.Proofs.Machine.LIR.Fn10a210

namespace AesGcm.Proofs.Machine.AES64

open AesGcm.Proofs.Machine.Fixslice AesGcm.Proofs.Machine.Runtime
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift
  X86Proofs.Refine AesGcm.Proofs.Machine.LIR

open AesGcm.Proofs.Machine.Fixslice AesGcm.Proofs.Machine.Runtime
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift
  X86Proofs.Refine

def outputSavedMemory (fr : Activation) (rax : BitVec 64) : Ram :=
  memStore (inputSavedMemory fr) (fr.rsp - 56) rax

theorem outputSavedMemory_memLoad (fr : Activation) (rax : BitVec 64) (j : Fin 7) :
    memLoad (outputSavedMemory fr rax) (fr.rsp - BitVec.ofNat 64 (8 * j.val)) 64 =
      inputSavedValue fr j := by
  have he : (7 : Fin 10) ≠ (⟨j.val, by omega⟩ : Fin 10) := by
    intro h
    have hv := congrArg Fin.val h
    change 7 = j.val at hv
    have := j.isLt
    omega
  have h := inputStackLoad_store (inputSavedMemory fr) fr.rsp (7 : Fin 10)
    ⟨j.val, by omega⟩ rax
  simp only [he, ite_false] at h
  exact h.trans (inputSavedMemory_memLoad fr j)

theorem outputSavedMemory_frame (fr : Activation) (rax : BitVec 64)
    (hroom : fr.low.toNat + 56 ≤ fr.rsp.toNat) :
    RamWriteFrame fr.original (outputSavedMemory fr rax) [fr.region] := by
  have hf := inputSavedMemory_frame fr (by omega)
  apply hf.memStore rax
  have hle : (56 : BitVec 64) ≤ fr.rsp := by
    change (56 : BitVec 64).toNat ≤ fr.rsp.toNat
    change 56 ≤ fr.rsp.toNat
    omega
  have he : (fr.rsp - 56).toNat = fr.rsp.toNat - 56 := by
    rw [BitVec.toNat_sub_of_le hle]
    rfl
  refine ⟨fr.region, by simp, ?_⟩
  simp only [InRegion, Activation.region, he]
  have := fr.rsp.isLt
  omega

end AesGcm.Proofs.Machine.AES64

namespace AesGcm.Proofs.Machine.AES64

open AesGcm.Proofs.Machine.Fixslice AesGcm.Proofs.Machine.Runtime
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.Lift
  X86Proofs.Refine AesGcm.Proofs.Machine.LIR

theorem output_low32_shift_byte (x : BitVec 64) (s : Nat) (hs : s + 8 ≤ 32) :
    (((x.setWidth 32 >>> s).setWidth 64).setWidth 8) = (x >>> s).setWidth 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight]
  have hsi : s + i < 32 := by omega
  have hi64 : i < 64 := by omega
  simp only [hi, hi64, hsi, decide_true, Bool.true_and]

theorem output_high8_byte (x : BitVec 64) :
    x.extractLsb' 8 8 = writeReordered x 0 1 := by
  exact BitVec.setWidth_ushiftRight_eq_extractLsb.symm

theorem output_low8_byte (x : BitVec 64) :
    x.setWidth 8 = writeReordered x 0 0 := by rfl



theorem output_register_words (x : Planes) :
    let t00 := ((x 0 >>> (1 : Nat)) ^^^ x 1) &&& (0x5555555555555555 : BitVec 64)
    let w00 := (t00 + t00) ^^^ x 0
    let w01 := x 1 ^^^ t00
    let t02 := ((x 2 >>> (1 : Nat)) ^^^ x 3) &&& (0x5555555555555555 : BitVec 64)
    let w02 := (t02 + t02) ^^^ x 2
    let w03 := x 3 ^^^ t02
    let t04 := ((x 4 >>> (1 : Nat)) ^^^ x 5) &&& (0x5555555555555555 : BitVec 64)
    let w04 := (t04 + t04) ^^^ x 4
    let w05 := x 5 ^^^ t04
    let t06 := ((x 6 >>> (1 : Nat)) ^^^ x 7) &&& (0x5555555555555555 : BitVec 64)
    let w06 := (t06 + t06) ^^^ x 6
    let w07 := x 7 ^^^ t06
    let t10 := ((w00 >>> (2 : Nat)) ^^^ w02) &&& (0x3333333333333333 : BitVec 64)
    let w10 := (t10 <<< (2 : Nat)) ^^^ w00
    let w12 := w02 ^^^ t10
    let t11 := ((w01 >>> (2 : Nat)) ^^^ w03) &&& (0x3333333333333333 : BitVec 64)
    let w11 := (t11 <<< (2 : Nat)) ^^^ w01
    let w13 := w03 ^^^ t11
    let t14 := ((w04 >>> (2 : Nat)) ^^^ w06) &&& (0x3333333333333333 : BitVec 64)
    let w14 := (t14 <<< (2 : Nat)) ^^^ w04
    let w16 := w06 ^^^ t14
    let t15 := ((w05 >>> (2 : Nat)) ^^^ w07) &&& (0x3333333333333333 : BitVec 64)
    let w15 := (t15 <<< (2 : Nat)) ^^^ w05
    let w17 := w07 ^^^ t15
    let t20 := ((w10 >>> (4 : Nat)) ^^^ w14) &&& (0x0f0f0f0f0f0f0f0f : BitVec 64)
    let w20 := (t20 <<< (4 : Nat)) ^^^ w10
    let w24 := w14 ^^^ t20
    let t21 := ((w11 >>> (4 : Nat)) ^^^ w15) &&& (0x0f0f0f0f0f0f0f0f : BitVec 64)
    let w21 := (t21 <<< (4 : Nat)) ^^^ w11
    let w25 := w15 ^^^ t21
    let t22 := ((w12 >>> (4 : Nat)) ^^^ w16) &&& (0x0f0f0f0f0f0f0f0f : BitVec 64)
    let w22 := (t22 <<< (4 : Nat)) ^^^ w12
    let w26 := w16 ^^^ t22
    let t23 := ((w13 >>> (4 : Nat)) ^^^ w17) &&& (0x0f0f0f0f0f0f0f0f : BitVec 64)
    let w23 := (t23 <<< (4 : Nat)) ^^^ w13
    let w27 := w17 ^^^ t23
    w20 = bitsliceSwaps x 0 ∧
    w21 = bitsliceSwaps x 1 ∧
    w22 = bitsliceSwaps x 2 ∧
    w23 = bitsliceSwaps x 3 ∧
    w24 = bitsliceSwaps x 4 ∧
    w25 = bitsliceSwaps x 5 ∧
    w26 = bitsliceSwaps x 6 ∧
    w27 = bitsliceSwaps x 7 := by
  rw [← assemblyInputWords_eq]
  exact ⟨rfl, rfl, rfl, rfl, BitVec.xor_comm _ _, BitVec.xor_comm _ _,
    BitVec.xor_comm _ _, BitVec.xor_comm _ _⟩

theorem output_extraction_offset (x : Planes) (i : Fin 64) :
    outputExtraction x ⟨i.val / 16, by omega⟩ ⟨i.val % 16, by omega⟩ =
      (x ⟨4 * (i.val / 4 % 2) + i.val / 16, by omega⟩ >>>
        (16 * (i.val % 4) + 8 * (i.val / 8 % 2))).setWidth 8 := by
  have h : ∀ i : Fin 64,
      4 * (i.val % 16 / 4 % 2) + i.val / 16 =
        4 * (i.val / 4 % 2) + i.val / 16 ∧
      16 * (i.val % 16 % 4) + 8 * (i.val % 16 / 8) =
        16 * (i.val % 4) + 8 * (i.val / 8 % 2) := by decide +kernel
  simp only [outputExtraction, writeReordered]
  rw [(h i).2]
  congr 3
  exact Fin.ext (h i).1

end AesGcm.Proofs.Machine.AES64

namespace AesGcm.Proofs.Machine.AES64

open AesGcm.Proofs.Machine.Fixslice AesGcm.Proofs.Machine.Runtime
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift
  X86Proofs.Refine AesGcm.Proofs.Machine.LIR

open X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift
open AesGcm.Proofs.Machine.LIR

theorem_by outputEntry_eval (code : CodeMap) (args : Values Value Reg.count) (mem : Ram) :
    program.runBlock (dialect code) ⟨.l10a210, args, mem⟩ = _ := by
  cfg_eval
  cfg_name_stores
  rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
theorem_by outputBody_eval (code : CodeMap) (args : Values Value Reg.count) (mem : Ram) :
    program.runBlock (dialect code) ⟨.l10a26a, args, mem⟩ = _ := by
  cfg_eval [LIR.b_l10a26a, LIR.b_l10a26a_1, LIR.b_l10a26a_2, LIR.b_l10a26a_3, LIR.b_l10a26a_4, LIR.b_l10a26a_5, LIR.b_l10a26a_6, LIR.b_l10a26a_7, LIR.b_l10a26a_8, LIR.b_l10a26a_9, LIR.b_l10a26a_10, LIR.b_l10a26a_11, LIR.b_l10a26a_12]
  cfg_name_stores
  rfl


private theorem output_lengthChecks_runBlock (code : CodeMap)
    (args : Values Value Reg.count) (mem : Ram) (l target : Label)
    (hlabel : (l, target) ∈ [(.l10a224, .l10a22e), (.l10a22e, .l10a238),
      (.l10a238, .l10a242), (.l10a242, .l10a24c), (.l10a24c, .l10a256),
      (.l10a256, .l10a260), (.l10a260, .l10a26a)])
    (hlen : (args[2]).get 64 = 8)
    (hTypes : AesGcm.Proofs.Machine.Runtime.GPRsTyped args) :
    ∃ out : Values Value Reg.count,
      program.runBlock (dialect code) ⟨l, args, mem⟩ = .jump ⟨target, out, mem⟩ ∧
      out[2] = args[2] ∧ out[4] = args[4] ∧ out[5] = args[5] ∧
      out[6] = args[6] ∧ out[7] = args[7] ∧ out[22] = args[22] ∧
      out[39] = args[39] ∧ out[50] = args[50] ∧ out[51] = args[51] ∧
      AesGcm.Proofs.Machine.Runtime.GPRsTyped out := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hlabel
  rcases hlabel with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
    ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> cfg_eval
  all_goals simp only [hlen]
  all_goals refine ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  all_goals
    intro r
    have hr : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨
        r = 8 ∨ r = 9 ∨ r = 10 ∨ r = 11 ∨ r = 12 ∨ r = 13 ∨ r = 14 ∨ r = 15 := by
      have := r.isLt
      omega
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | rfl | exact hTypes 0 | exact hTypes 1 | exact hTypes 2 | exact hTypes 3 | exact hTypes 4 | exact hTypes 5 | exact hTypes 6 | exact hTypes 7 | exact hTypes 8 | exact hTypes 9 | exact hTypes 10 | exact hTypes 11 | exact hTypes 12 | exact hTypes 13 | exact hTypes 14 | exact hTypes 15


end AesGcm.Proofs.Machine.AES64

namespace AesGcm.Proofs.Machine.AES64

open AesGcm.Proofs.Machine.Fixslice AesGcm.Proofs.Machine.Runtime
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift
  X86Proofs.Refine AesGcm.Proofs.Machine.LIR

open X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift
  X86Proofs.Refine
open AesGcm.Proofs.Machine.LIR

private theorem output_entry_runBlock (code : CodeMap)
    (args : Values Value Reg.count) (mem : Ram)
    (hcode : ∀ x ∈ fnCode, x ∈ code)
    (hstack : Writable code mem ((args[4]).get 64 - 192) 192)
    (hlen : (args[2]).get 64 = 8)
    (hTypes : AesGcm.Proofs.Machine.Runtime.GPRsTyped args) :
    let rsp := (args[4]).get 64
    let m1 := memStore mem (rsp - 8) ((args[5]).get 64)
    let m2 := memStore m1 (rsp - 16) ((args[15]).get 64)
    let m3 := memStore m2 (rsp - 24) ((args[14]).get 64)
    let m4 := memStore m3 (rsp - 32) ((args[13]).get 64)
    let m5 := memStore m4 (rsp - 40) ((args[12]).get 64)
    let m6 := memStore m5 (rsp - 48) ((args[3]).get 64)
    let m7 := memStore m6 (rsp - 56) ((args[0]).get 64)
    ∃ out : Values Value Reg.count,
      program.runBlock (dialect code) ⟨.l10a210, args, mem⟩ =
        .jump ⟨.l10a224, out, m7⟩ ∧
      out[4] = ⟨64, rsp - 56⟩ ∧ out[2] = args[2] ∧ out[6] = args[6] ∧
      out[7] = args[7] ∧ out[22] = args[22] ∧
      out[39] = args[39] ∧ out[50] = args[50] ∧ out[51] = args[51] ∧
      AesGcm.Proofs.Machine.Runtime.GPRsTyped out := by
  dsimp only
  let rsp := (args[4]).get 64
  have guard {m : Ram} (hw : Writable code m (rsp - 192) 192)
      (k off : Nat) (bytes : List UInt8)
      (hk : ((192 : BitVec 64) - BitVec.ofNat 64 k).toNat + 8 ≤ 192)
      (hb : (bytes_l10a210.drop off).take bytes.length = bytes) :
      StoreOk code m (rsp - BitVec.ofNat 64 k) 8
        (0x10a210 + BitVec.ofNat 64 off) bytes.length := by
    apply storeOk_of_codeRange
      (hw.of_offsets (addr_sub _ _) (addr_sub _ _) ?_)
    · intro x hx
      exact hcode x (code_l10a210 x (codeRange_mem_of_drop off hb x hx))
    · simpa only [sub_sub_sub_left] using hk
  have w1 := hstack.memStore (rsp - 8) ((args[5]).get 64)
  have w2 := w1.memStore (rsp - 16) ((args[15]).get 64)
  have w3 := w2.memStore (rsp - 24) ((args[14]).get 64)
  have w4 := w3.memStore (rsp - 32) ((args[13]).get 64)
  have w5 := w4.memStore (rsp - 40) ((args[12]).get 64)
  have w6 := w5.memStore (rsp - 48) ((args[3]).get 64)
  have h0 := guard hstack 8 0 [0x55] (by decide) (by decide)
  have h1 := guard w1 16 1 [0x41, 0x57] (by decide) (by decide)
  have h2 := guard w2 24 3 [0x41, 0x56] (by decide) (by decide)
  have h3 := guard w3 32 5 [0x41, 0x55] (by decide) (by decide)
  have h4 := guard w4 40 7 [0x41, 0x54] (by decide) (by decide)
  have h5 := guard w5 48 9 [0x53] (by decide) (by decide)
  have h6 := guard w6 56 10 [0x50] (by decide) (by decide)
  simp only [BitVec.reduceAdd, List.length_cons, List.length_nil, Nat.reduceAdd] at h0 h1 h2 h3 h4 h5 h6
  cfg_eval
  dsimp only [rsp] at h0 h1 h2 h3 h4 h5 h6
  simp only [BitVec.ofNat_eq_ofNat] at h0 h1 h2 h3 h4 h5 h6 ⊢
  simp only [h0, h1, h2, h3, h4, h5, h6, ↓reduceIte]
  simp only [hlen]
  refine ⟨_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  intro r
  have hr : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨
      r = 8 ∨ r = 9 ∨ r = 10 ∨ r = 11 ∨ r = 12 ∨ r = 13 ∨ r = 14 ∨ r = 15 := by
    have := r.isLt
    omega
  rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | rfl | exact hTypes 0 | exact hTypes 1 | exact hTypes 2 | exact hTypes 3 | exact hTypes 4 | exact hTypes 5 | exact hTypes 6 | exact hTypes 7 | exact hTypes 8 | exact hTypes 9 | exact hTypes 10 | exact hTypes 11 | exact hTypes 12 | exact hTypes 13 | exact hTypes 14 | exact hTypes 15


end AesGcm.Proofs.Machine.AES64

namespace AesGcm.Proofs.Machine.AES64

open AesGcm.Proofs.Machine.Fixslice AesGcm.Proofs.Machine.Runtime
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift
  X86Proofs.Refine AesGcm.Proofs.Machine.LIR

open X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift
  X86Proofs.Refine
open AesGcm.Proofs.Machine.LIR

private theorem outputStoreGuard {code : CodeMap} {m : Ram} {a : BitVec 64}
    (hcode : ∀ x ∈ fnCode, x ∈ code) (hw : Writable code m a 64)
    (m' : Ram) (hr : Readable m' a 64) (i : Nat) (hi : i < 64) (p : BitVec 64) (len : Nat)
    (hp : (p - 0x10a26a).toNat + len ≤ bytes_l10a26a.length) :
    StoreOk code m' (a + BitVec.ofNat 64 i) 1 p len := by
  have hw' : Writable code m' a 64 := ⟨hr, hw.tables, hw.notCode⟩
  have hin : (BitVec.ofNat 64 i - 0).toNat + 1 ≤ 64 := by
    change ((BitVec.ofNat 64 i) - BitVec.ofNat 64 0).toNat + 1 ≤ 64
    rw [BitVec.sub_zero (BitVec.ofNat 64 i), BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show i < 2^64 by omega)]
    omega
  have hs := hw'.of_offsets (rfl : a + BitVec.ofNat 64 i = a + BitVec.ofNat 64 i)
    (addr_self a) hin
  apply storeOk_of_writable hs
  intro j hj k hk he
  let off := (p - 0x10a26a).toNat
  have hoff : off + k < bytes_l10a26a.length := by omega
  have hc := hcode _ (code_l10a26a _ (mem_codeRange 0x10a26a bytes_l10a26a (off + k) hoff))
  apply hs.notCode _ hc j hj
  have hp' : (0x10a26a : BitVec 64) + BitVec.ofNat 64 off = p := by
    simp only [off, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rw [BitVec.add_comm, BitVec.sub_add_cancel]
  have hx : (0x10a26a : BitVec 64) + BitVec.ofNat 64 (off + k) = p + BitVec.ofNat 64 k := by
    rw [BitVec.ofNat_add, ← BitVec.add_assoc, hp']
  exact hx.trans he.symm


end AesGcm.Proofs.Machine.AES64

namespace AesGcm.Proofs.Machine.AES64

open AesGcm.Proofs.Machine.Fixslice AesGcm.Proofs.Machine.Runtime
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift
  X86Proofs.Refine AesGcm.Proofs.Machine.LIR
open X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.LIR
set_option maxHeartbeats 1200000 in
set_option maxRecDepth 8192 in
theorem outputBody_runBlock (code : CodeMap) (args : Values Value Reg.count) (mem : Ram)
    (hc : ∀ x ∈ fnCode, x ∈ code)
    (hTypes : AesGcm.Proofs.Machine.Runtime.GPRsTyped args)
    (hi : Readable mem ((args[6]).get 64) 64)
    (hw : Writable code mem ((args[7]).get 64) 64)
    (hs : Readable mem ((args[4]).get 64) 64)
    (hsep : RangeApart ((args[7]).get 64) 64 ((args[4]).get 64) 64)
    (hret : (memLoad mem ((args[4]).get 64 + 56) 64).toNat < 2^32) :
    ∃ o, program.runBlock (dialect code) ⟨.l10a26a, args, mem⟩ = .returned o ∧
      o.store = outputStoredBytes mem ((args[7]).get 64)
        (fun p ↦ memLoad mem ((args[6]).get 64 + BitVec.ofNat 64 (8 * p.val)) 64) ∧
      o.tag = some ⟨64, memLoad o.store ((args[4]).get 64 + 56) 64⟩ ∧
      o.values[4] = ⟨64, (args[4]).get 64 + 64⟩ ∧
      o.values[22] = args[22] ∧
      o.values[3] = ⟨64, memLoad o.store ((args[4]).get 64 + 8) 64⟩ ∧
      o.values[12] = ⟨64, memLoad o.store ((args[4]).get 64 + 16) 64⟩ ∧
      o.values[13] = ⟨64, memLoad o.store ((args[4]).get 64 + 24) 64⟩ ∧
      o.values[14] = ⟨64, memLoad o.store ((args[4]).get 64 + 32) 64⟩ ∧
      o.values[15] = ⟨64, memLoad o.store ((args[4]).get 64 + 40) 64⟩ ∧
      o.values[5] = ⟨64, memLoad o.store ((args[4]).get 64 + 48) 64⟩ ∧
      o.values[39] = args[39] ∧ o.values[50] = args[50] ∧ o.values[51] = args[51] ∧
      AesGcm.Proofs.Machine.Runtime.GPRsTyped o.values := by
  let dst := (args[7]).get 64
  let src := (args[6]).get 64
  let sp := (args[4]).get 64
  let x : Planes := fun p ↦ memLoad mem (src + BitVec.ofNat 64 (8 * p.val)) 64
  have hr0 : Readable mem dst 64 := hw.readable
  have hz (m' : Ram) (hr : Readable m' dst 64) (p : BitVec 64) (n : Nat)
      (hp : (p - 0x10a26a).toNat + n ≤ bytes_l10a26a.length) :
      StoreOk code m' dst 1 p n := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using
      outputStoreGuard hc hw m' hr 0 (by decide) p n hp
  have hap {a : BitVec 64} (ha : (a - dst).toNat < 64) :
      RangeApart a 1 (sp + 56) 8 := by
    let off := (a - dst).toNat
    have haddr : dst + BitVec.ofNat 64 off = a := by
      simp only [off, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      rw [BitVec.add_comm, BitVec.sub_add_cancel]
    intro i hibar j hj he
    apply hsep (off + i) (by omega) (56 + j) (by omega)
    have hleft : dst + BitVec.ofNat 64 (off + i) = a + BitVec.ofNat 64 i := by
      rw [BitVec.ofNat_add, ← BitVec.add_assoc, haddr]
    have hright : sp + BitVec.ofNat 64 (56 + j) = (sp + 56) + BitVec.ofNat 64 j := by
      rw [BitVec.ofNat_add, BitVec.add_assoc]
      rfl
    exact hleft.trans (he.trans hright.symm)
  rw [outputBody_eval]
  extract_lets m1 m2 m3 m4 m5 m6 m7 m8 m9 m10 m11 m12 m13 m14 m15 m16 m17 m18 m19 m20 m21 m22 m23 m24 m25 m26 m27 m28 m29 m30 m31 m32 m33 m34 m35 m36 m37 m38 m39 m40 m41 m42 m43 m44 m45 m46 m47 m48 m49 m50 m51 m52 m53 m54 m55 m56 m57 m58 m59 m60 m61 m62 m63 m64
  have hwds := output_register_words x
  dsimp only [x, Fin.instOfNat, Fin.ofNat] at hwds
  simp only [BitVec.ofNat_eq_ofNat] at hwds
  rcases hwds with ⟨word0, word1, word2, word3, word4, word5, word6, word7⟩
  dsimp only [src, Fin.instOfNat, Fin.ofNat] at word0 word1 word2 word3 word4 word5 word6 word7
  have index0 : BitVec.ofNat 64 (8 * (0 : Fin 8).val) = 0 := by rfl
  have index1 : BitVec.ofNat 64 (8 * (1 : Fin 8).val) = 8 := by rfl
  have index2 : BitVec.ofNat 64 (8 * (2 : Fin 8).val) = 16 := by rfl
  have index3 : BitVec.ofNat 64 (8 * (3 : Fin 8).val) = 24 := by rfl
  have index4 : BitVec.ofNat 64 (8 * (4 : Fin 8).val) = 32 := by rfl
  have index5 : BitVec.ofNat 64 (8 * (5 : Fin 8).val) = 40 := by rfl
  have index6 : BitVec.ofNat 64 (8 * (6 : Fin 8).val) = 48 := by rfl
  have index7 : BitVec.ofNat 64 (8 * (7 : Fin 8).val) = 56 := by rfl
  simp only [index0, index1, index2, index3, index4, index5, index6, index7] at word0 word1 word2 word3 word4 word5 word6 word7
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at word0 word1 word2 word3 word4 word5 word6 word7
  have low32 (w : BitVec 64) (n : Nat) (hn : n + 8 ≤ 32) :
      ((w.setWidth 32 >>> n).setWidth 8) = (w >>> n).setWidth 8 := by
    simpa only [BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 64 by decide)] using
      output_low32_shift_byte w n hn
  have hmodel : m64 = outputStoredBytes mem dst x := by
    dsimp only [m64, m63, m62, m61, m60, m59, m58, m57, m56, m55, m54, m53, m52, m51, m50, m49, m48, m47, m46, m45, m44, m43, m42, m41, m40, m39, m38, m37, m36, m35, m34, m33, m32, m31, m30, m29, m28, m27, m26, m25, m24, m23, m22, m21, m20, m19, m18, m17, m16, m15, m14, m13, m12, m11, m10, m9, m8, m7, m6, m5, m4, m3, m2, m1]
    simp only [BitVec.ofNat_eq_ofNat]
    rw [word0, word1, word2, word3, word4, word5, word6, word7]
    simp (disch := decide +kernel) only [low32, ← BitVec.setWidth_ushiftRight_eq_extractLsb]
    simp only [outputStoredBytes, invBitslice, outputExtraction, writeReordered,
      List.range_succ, List.range_zero, List.foldl_append, List.foldl_cons, List.foldl_nil,
      Nat.reduceDiv, Nat.reduceMod, Nat.reduceMul, Nat.reduceAdd,
      BitVec.ushiftRight_zero, BitVec.add_zero]
    rfl

  have hr1 : Readable m1 dst 64 := hw.readable.memStore _ _
  have hs1 : Readable m1 sp 64 := hs.memStore _ _
  have hr2 : Readable m2 dst 64 := hr1.memStore _ _
  have hs2 : Readable m2 sp 64 := hs1.memStore _ _
  have hr3 : Readable m3 dst 64 := hr2.memStore _ _
  have hs3 : Readable m3 sp 64 := hs2.memStore _ _
  have hr4 : Readable m4 dst 64 := hr3.memStore _ _
  have hs4 : Readable m4 sp 64 := hs3.memStore _ _
  have hr5 : Readable m5 dst 64 := hr4.memStore _ _
  have hs5 : Readable m5 sp 64 := hs4.memStore _ _
  have hr6 : Readable m6 dst 64 := hr5.memStore _ _
  have hs6 : Readable m6 sp 64 := hs5.memStore _ _
  have hr7 : Readable m7 dst 64 := hr6.memStore _ _
  have hs7 : Readable m7 sp 64 := hs6.memStore _ _
  have hr8 : Readable m8 dst 64 := hr7.memStore _ _
  have hs8 : Readable m8 sp 64 := hs7.memStore _ _
  have hr9 : Readable m9 dst 64 := hr8.memStore _ _
  have hs9 : Readable m9 sp 64 := hs8.memStore _ _
  have hr10 : Readable m10 dst 64 := hr9.memStore _ _
  have hs10 : Readable m10 sp 64 := hs9.memStore _ _
  have hr11 : Readable m11 dst 64 := hr10.memStore _ _
  have hs11 : Readable m11 sp 64 := hs10.memStore _ _
  have hr12 : Readable m12 dst 64 := hr11.memStore _ _
  have hs12 : Readable m12 sp 64 := hs11.memStore _ _
  have hr13 : Readable m13 dst 64 := hr12.memStore _ _
  have hs13 : Readable m13 sp 64 := hs12.memStore _ _
  have hr14 : Readable m14 dst 64 := hr13.memStore _ _
  have hs14 : Readable m14 sp 64 := hs13.memStore _ _
  have hr15 : Readable m15 dst 64 := hr14.memStore _ _
  have hs15 : Readable m15 sp 64 := hs14.memStore _ _
  have hr16 : Readable m16 dst 64 := hr15.memStore _ _
  have hs16 : Readable m16 sp 64 := hs15.memStore _ _
  have hr17 : Readable m17 dst 64 := hr16.memStore _ _
  have hs17 : Readable m17 sp 64 := hs16.memStore _ _
  have hr18 : Readable m18 dst 64 := hr17.memStore _ _
  have hs18 : Readable m18 sp 64 := hs17.memStore _ _
  have hr19 : Readable m19 dst 64 := hr18.memStore _ _
  have hs19 : Readable m19 sp 64 := hs18.memStore _ _
  have hr20 : Readable m20 dst 64 := hr19.memStore _ _
  have hs20 : Readable m20 sp 64 := hs19.memStore _ _
  have hr21 : Readable m21 dst 64 := hr20.memStore _ _
  have hs21 : Readable m21 sp 64 := hs20.memStore _ _
  have hr22 : Readable m22 dst 64 := hr21.memStore _ _
  have hs22 : Readable m22 sp 64 := hs21.memStore _ _
  have hr23 : Readable m23 dst 64 := hr22.memStore _ _
  have hs23 : Readable m23 sp 64 := hs22.memStore _ _
  have hr24 : Readable m24 dst 64 := hr23.memStore _ _
  have hs24 : Readable m24 sp 64 := hs23.memStore _ _
  have hr25 : Readable m25 dst 64 := hr24.memStore _ _
  have hs25 : Readable m25 sp 64 := hs24.memStore _ _
  have hr26 : Readable m26 dst 64 := hr25.memStore _ _
  have hs26 : Readable m26 sp 64 := hs25.memStore _ _
  have hr27 : Readable m27 dst 64 := hr26.memStore _ _
  have hs27 : Readable m27 sp 64 := hs26.memStore _ _
  have hr28 : Readable m28 dst 64 := hr27.memStore _ _
  have hs28 : Readable m28 sp 64 := hs27.memStore _ _
  have hr29 : Readable m29 dst 64 := hr28.memStore _ _
  have hs29 : Readable m29 sp 64 := hs28.memStore _ _
  have hr30 : Readable m30 dst 64 := hr29.memStore _ _
  have hs30 : Readable m30 sp 64 := hs29.memStore _ _
  have hr31 : Readable m31 dst 64 := hr30.memStore _ _
  have hs31 : Readable m31 sp 64 := hs30.memStore _ _
  have hr32 : Readable m32 dst 64 := hr31.memStore _ _
  have hs32 : Readable m32 sp 64 := hs31.memStore _ _
  have hr33 : Readable m33 dst 64 := hr32.memStore _ _
  have hs33 : Readable m33 sp 64 := hs32.memStore _ _
  have hr34 : Readable m34 dst 64 := hr33.memStore _ _
  have hs34 : Readable m34 sp 64 := hs33.memStore _ _
  have hr35 : Readable m35 dst 64 := hr34.memStore _ _
  have hs35 : Readable m35 sp 64 := hs34.memStore _ _
  have hr36 : Readable m36 dst 64 := hr35.memStore _ _
  have hs36 : Readable m36 sp 64 := hs35.memStore _ _
  have hr37 : Readable m37 dst 64 := hr36.memStore _ _
  have hs37 : Readable m37 sp 64 := hs36.memStore _ _
  have hr38 : Readable m38 dst 64 := hr37.memStore _ _
  have hs38 : Readable m38 sp 64 := hs37.memStore _ _
  have hr39 : Readable m39 dst 64 := hr38.memStore _ _
  have hs39 : Readable m39 sp 64 := hs38.memStore _ _
  have hr40 : Readable m40 dst 64 := hr39.memStore _ _
  have hs40 : Readable m40 sp 64 := hs39.memStore _ _
  have hr41 : Readable m41 dst 64 := hr40.memStore _ _
  have hs41 : Readable m41 sp 64 := hs40.memStore _ _
  have hr42 : Readable m42 dst 64 := hr41.memStore _ _
  have hs42 : Readable m42 sp 64 := hs41.memStore _ _
  have hr43 : Readable m43 dst 64 := hr42.memStore _ _
  have hs43 : Readable m43 sp 64 := hs42.memStore _ _
  have hr44 : Readable m44 dst 64 := hr43.memStore _ _
  have hs44 : Readable m44 sp 64 := hs43.memStore _ _
  have hr45 : Readable m45 dst 64 := hr44.memStore _ _
  have hs45 : Readable m45 sp 64 := hs44.memStore _ _
  have hr46 : Readable m46 dst 64 := hr45.memStore _ _
  have hs46 : Readable m46 sp 64 := hs45.memStore _ _
  have hr47 : Readable m47 dst 64 := hr46.memStore _ _
  have hs47 : Readable m47 sp 64 := hs46.memStore _ _
  have hr48 : Readable m48 dst 64 := hr47.memStore _ _
  have hs48 : Readable m48 sp 64 := hs47.memStore _ _
  have hr49 : Readable m49 dst 64 := hr48.memStore _ _
  have hs49 : Readable m49 sp 64 := hs48.memStore _ _
  have hr50 : Readable m50 dst 64 := hr49.memStore _ _
  have hs50 : Readable m50 sp 64 := hs49.memStore _ _
  have hr51 : Readable m51 dst 64 := hr50.memStore _ _
  have hs51 : Readable m51 sp 64 := hs50.memStore _ _
  have hr52 : Readable m52 dst 64 := hr51.memStore _ _
  have hs52 : Readable m52 sp 64 := hs51.memStore _ _
  have hr53 : Readable m53 dst 64 := hr52.memStore _ _
  have hs53 : Readable m53 sp 64 := hs52.memStore _ _
  have hr54 : Readable m54 dst 64 := hr53.memStore _ _
  have hs54 : Readable m54 sp 64 := hs53.memStore _ _
  have hr55 : Readable m55 dst 64 := hr54.memStore _ _
  have hs55 : Readable m55 sp 64 := hs54.memStore _ _
  have hr56 : Readable m56 dst 64 := hr55.memStore _ _
  have hs56 : Readable m56 sp 64 := hs55.memStore _ _
  have hr57 : Readable m57 dst 64 := hr56.memStore _ _
  have hs57 : Readable m57 sp 64 := hs56.memStore _ _
  have hr58 : Readable m58 dst 64 := hr57.memStore _ _
  have hs58 : Readable m58 sp 64 := hs57.memStore _ _
  have hr59 : Readable m59 dst 64 := hr58.memStore _ _
  have hs59 : Readable m59 sp 64 := hs58.memStore _ _
  have hr60 : Readable m60 dst 64 := hr59.memStore _ _
  have hs60 : Readable m60 sp 64 := hs59.memStore _ _
  have hr61 : Readable m61 dst 64 := hr60.memStore _ _
  have hs61 : Readable m61 sp 64 := hs60.memStore _ _
  have hr62 : Readable m62 dst 64 := hr61.memStore _ _
  have hs62 : Readable m62 sp 64 := hs61.memStore _ _
  have hr63 : Readable m63 dst 64 := hr62.memStore _ _
  have hs63 : Readable m63 sp 64 := hs62.memStore _ _
  have hr64 : Readable m64 dst 64 := hr63.memStore _ _
  have hs64 : Readable m64 sp 64 := hs63.memStore _ _
  have ht1 : memLoad m1 (sp + 56) 64 = memLoad mem (sp + 56) 64 := by
    apply Eq.trans (b := memLoad mem (sp + 56) 64)
    · apply memLoad_memStore_of_rangeApart
      apply hap
      dsimp only [dst]
      simp only [BitVec.sub_self, BitVec.reduceToNat] <;> decide +kernel
    · rfl
  have ht2 : memLoad m2 (sp + 56) 64 = memLoad mem (sp + 56) 64 := by
    apply Eq.trans (b := memLoad m1 (sp + 56) 64)
    · apply memLoad_memStore_of_rangeApart
      apply hap
      dsimp only [dst]
      simp only [BitVec.ofNat_eq_ofNat, add_sub_self_right, BitVec.reduceToNat] <;> decide +kernel
    · exact ht1
  have ht3 : memLoad m3 (sp + 56) 64 = memLoad mem (sp + 56) 64 := by
    apply Eq.trans (b := memLoad m2 (sp + 56) 64)
    · apply memLoad_memStore_of_rangeApart
      apply hap
      dsimp only [dst]
      simp only [BitVec.ofNat_eq_ofNat, add_sub_self_right, BitVec.reduceToNat] <;> decide +kernel
    · exact ht2
  have ht4 : memLoad m4 (sp + 56) 64 = memLoad mem (sp + 56) 64 := by
    apply Eq.trans (b := memLoad m3 (sp + 56) 64)
    · apply memLoad_memStore_of_rangeApart
      apply hap
      dsimp only [dst]
      simp only [BitVec.ofNat_eq_ofNat, add_sub_self_right, BitVec.reduceToNat] <;> decide +kernel
    · exact ht3
  have ht5 : memLoad m5 (sp + 56) 64 = memLoad mem (sp + 56) 64 := by
    apply Eq.trans (b := memLoad m4 (sp + 56) 64)
    · apply memLoad_memStore_of_rangeApart
      apply hap
      dsimp only [dst]
      simp only [BitVec.ofNat_eq_ofNat, add_sub_self_right, BitVec.reduceToNat] <;> decide +kernel
    · exact ht4
  have ht6 : memLoad m6 (sp + 56) 64 = memLoad mem (sp + 56) 64 := by
    apply Eq.trans (b := memLoad m5 (sp + 56) 64)
    · apply memLoad_memStore_of_rangeApart
      apply hap
      dsimp only [dst]
      simp only [BitVec.ofNat_eq_ofNat, add_sub_self_right, BitVec.reduceToNat] <;> decide +kernel
    · exact ht5
  have ht7 : memLoad m7 (sp + 56) 64 = memLoad mem (sp + 56) 64 := by
    apply Eq.trans (b := memLoad m6 (sp + 56) 64)
    · apply memLoad_memStore_of_rangeApart
      apply hap
      dsimp only [dst]
      simp only [BitVec.ofNat_eq_ofNat, add_sub_self_right, BitVec.reduceToNat] <;> decide +kernel
    · exact ht6
  have ht8 : memLoad m8 (sp + 56) 64 = memLoad mem (sp + 56) 64 := by
    apply Eq.trans (b := memLoad m7 (sp + 56) 64)
    · apply memLoad_memStore_of_rangeApart
      apply hap
      dsimp only [dst]
      simp only [BitVec.ofNat_eq_ofNat, add_sub_self_right, BitVec.reduceToNat] <;> decide +kernel
    · exact ht7
  have ht9 : memLoad m9 (sp + 56) 64 = memLoad mem (sp + 56) 64 := by
    apply Eq.trans (b := memLoad m8 (sp + 56) 64)
    · apply memLoad_memStore_of_rangeApart
      apply hap
      dsimp only [dst]
      simp only [BitVec.ofNat_eq_ofNat, add_sub_self_right, BitVec.reduceToNat] <;> decide +kernel
    · exact ht8
  have ht10 : memLoad m10 (sp + 56) 64 = memLoad mem (sp + 56) 64 := by
    apply Eq.trans (b := memLoad m9 (sp + 56) 64)
    · apply memLoad_memStore_of_rangeApart
      apply hap
      dsimp only [dst]
      simp only [BitVec.ofNat_eq_ofNat, add_sub_self_right, BitVec.reduceToNat] <;> decide +kernel
    · exact ht9
  have ht11 : memLoad m11 (sp + 56) 64 = memLoad mem (sp + 56) 64 := by
    apply Eq.trans (b := memLoad m10 (sp + 56) 64)
    · apply memLoad_memStore_of_rangeApart
      apply hap
      dsimp only [dst]
      simp only [BitVec.ofNat_eq_ofNat, add_sub_self_right, BitVec.reduceToNat] <;> decide +kernel
    · exact ht10
  have ht12 : memLoad m12 (sp + 56) 64 = memLoad mem (sp + 56) 64 := by
    apply Eq.trans (b := memLoad m11 (sp + 56) 64)
    · apply memLoad_memStore_of_rangeApart
      apply hap
      dsimp only [dst]
      simp only [BitVec.ofNat_eq_ofNat, add_sub_self_right, BitVec.reduceToNat] <;> decide +kernel
    · exact ht11
  have ht13 : memLoad m13 (sp + 56) 64 = memLoad mem (sp + 56) 64 := by
    apply Eq.trans (b := memLoad m12 (sp + 56) 64)
    · apply memLoad_memStore_of_rangeApart
      apply hap
      dsimp only [dst]
      simp only [BitVec.ofNat_eq_ofNat, add_sub_self_right, BitVec.reduceToNat] <;> decide +kernel
    · exact ht12
  have ht14 : memLoad m14 (sp + 56) 64 = memLoad mem (sp + 56) 64 := by
    apply Eq.trans (b := memLoad m13 (sp + 56) 64)
    · apply memLoad_memStore_of_rangeApart
      apply hap
      dsimp only [dst]
      simp only [BitVec.ofNat_eq_ofNat, add_sub_self_right, BitVec.reduceToNat] <;> decide +kernel
    · exact ht13
  have ht15 : memLoad m15 (sp + 56) 64 = memLoad mem (sp + 56) 64 := by
    apply Eq.trans (b := memLoad m14 (sp + 56) 64)
    · apply memLoad_memStore_of_rangeApart
      apply hap
      dsimp only [dst]
      simp only [BitVec.ofNat_eq_ofNat, add_sub_self_right, BitVec.reduceToNat] <;> decide +kernel
    · exact ht14
  have ht16 : memLoad m16 (sp + 56) 64 = memLoad mem (sp + 56) 64 := by
    apply Eq.trans (b := memLoad m15 (sp + 56) 64)
    · apply memLoad_memStore_of_rangeApart
      apply hap
      dsimp only [dst]
      simp only [BitVec.ofNat_eq_ofNat, add_sub_self_right, BitVec.reduceToNat] <;> decide +kernel
    · exact ht15
  have ht17 : memLoad m17 (sp + 56) 64 = memLoad mem (sp + 56) 64 := by
    apply Eq.trans (b := memLoad m16 (sp + 56) 64)
    · apply memLoad_memStore_of_rangeApart
      apply hap
      dsimp only [dst]
      simp only [BitVec.ofNat_eq_ofNat, add_sub_self_right, BitVec.reduceToNat] <;> decide +kernel
    · exact ht16
  have ht18 : memLoad m18 (sp + 56) 64 = memLoad mem (sp + 56) 64 := by
    apply Eq.trans (b := memLoad m17 (sp + 56) 64)
    · apply memLoad_memStore_of_rangeApart
      apply hap
      dsimp only [dst]
      simp only [BitVec.ofNat_eq_ofNat, add_sub_self_right, BitVec.reduceToNat] <;> decide +kernel
    · exact ht17
  have ht19 : memLoad m19 (sp + 56) 64 = memLoad mem (sp + 56) 64 := by
    apply Eq.trans (b := memLoad m18 (sp + 56) 64)
    · apply memLoad_memStore_of_rangeApart
      apply hap
      dsimp only [dst]
      simp only [BitVec.ofNat_eq_ofNat, add_sub_self_right, BitVec.reduceToNat] <;> decide +kernel
    · exact ht18
  have ht20 : memLoad m20 (sp + 56) 64 = memLoad mem (sp + 56) 64 := by
    apply Eq.trans (b := memLoad m19 (sp + 56) 64)
    · apply memLoad_memStore_of_rangeApart
      apply hap
      dsimp only [dst]
      simp only [BitVec.ofNat_eq_ofNat, add_sub_self_right, BitVec.reduceToNat] <;> decide +kernel
    · exact ht19
  have ht21 : memLoad m21 (sp + 56) 64 = memLoad mem (sp + 56) 64 := by
    apply Eq.trans (b := memLoad m20 (sp + 56) 64)
    · apply memLoad_memStore_of_rangeApart
      apply hap
      dsimp only [dst]
      simp only [BitVec.ofNat_eq_ofNat, add_sub_self_right, BitVec.reduceToNat] <;> decide +kernel
    · exact ht20
  have ht22 : memLoad m22 (sp + 56) 64 = memLoad mem (sp + 56) 64 := by
    apply Eq.trans (b := memLoad m21 (sp + 56) 64)
    · apply memLoad_memStore_of_rangeApart
      apply hap
      dsimp only [dst]
      simp only [BitVec.ofNat_eq_ofNat, add_sub_self_right, BitVec.reduceToNat] <;> decide +kernel
    · exact ht21
  have ht23 : memLoad m23 (sp + 56) 64 = memLoad mem (sp + 56) 64 := by
    apply Eq.trans (b := memLoad m22 (sp + 56) 64)
    · apply memLoad_memStore_of_rangeApart
      apply hap
      dsimp only [dst]
      simp only [BitVec.ofNat_eq_ofNat, add_sub_self_right, BitVec.reduceToNat] <;> decide +kernel
    · exact ht22
  have ht24 : memLoad m24 (sp + 56) 64 = memLoad mem (sp + 56) 64 := by
    apply Eq.trans (b := memLoad m23 (sp + 56) 64)
    · apply memLoad_memStore_of_rangeApart
      apply hap
      dsimp only [dst]
      simp only [BitVec.ofNat_eq_ofNat, add_sub_self_right, BitVec.reduceToNat] <;> decide +kernel
    · exact ht23
  have ht25 : memLoad m25 (sp + 56) 64 = memLoad mem (sp + 56) 64 := by
    apply Eq.trans (b := memLoad m24 (sp + 56) 64)
    · apply memLoad_memStore_of_rangeApart
      apply hap
      dsimp only [dst]
      simp only [BitVec.ofNat_eq_ofNat, add_sub_self_right, BitVec.reduceToNat] <;> decide +kernel
    · exact ht24
  have ht26 : memLoad m26 (sp + 56) 64 = memLoad mem (sp + 56) 64 := by
    apply Eq.trans (b := memLoad m25 (sp + 56) 64)
    · apply memLoad_memStore_of_rangeApart
      apply hap
      dsimp only [dst]
      simp only [BitVec.ofNat_eq_ofNat, add_sub_self_right, BitVec.reduceToNat] <;> decide +kernel
    · exact ht25
  have ht27 : memLoad m27 (sp + 56) 64 = memLoad mem (sp + 56) 64 := by
    apply Eq.trans (b := memLoad m26 (sp + 56) 64)
    · apply memLoad_memStore_of_rangeApart
      apply hap
      dsimp only [dst]
      simp only [BitVec.ofNat_eq_ofNat, add_sub_self_right, BitVec.reduceToNat] <;> decide +kernel
    · exact ht26
  have ht28 : memLoad m28 (sp + 56) 64 = memLoad mem (sp + 56) 64 := by
    apply Eq.trans (b := memLoad m27 (sp + 56) 64)
    · apply memLoad_memStore_of_rangeApart
      apply hap
      dsimp only [dst]
      simp only [BitVec.ofNat_eq_ofNat, add_sub_self_right, BitVec.reduceToNat] <;> decide +kernel
    · exact ht27
  have ht29 : memLoad m29 (sp + 56) 64 = memLoad mem (sp + 56) 64 := by
    apply Eq.trans (b := memLoad m28 (sp + 56) 64)
    · apply memLoad_memStore_of_rangeApart
      apply hap
      dsimp only [dst]
      simp only [BitVec.ofNat_eq_ofNat, add_sub_self_right, BitVec.reduceToNat] <;> decide +kernel
    · exact ht28
  have ht30 : memLoad m30 (sp + 56) 64 = memLoad mem (sp + 56) 64 := by
    apply Eq.trans (b := memLoad m29 (sp + 56) 64)
    · apply memLoad_memStore_of_rangeApart
      apply hap
      dsimp only [dst]
      simp only [BitVec.ofNat_eq_ofNat, add_sub_self_right, BitVec.reduceToNat] <;> decide +kernel
    · exact ht29
  have ht31 : memLoad m31 (sp + 56) 64 = memLoad mem (sp + 56) 64 := by
    apply Eq.trans (b := memLoad m30 (sp + 56) 64)
    · apply memLoad_memStore_of_rangeApart
      apply hap
      dsimp only [dst]
      simp only [BitVec.ofNat_eq_ofNat, add_sub_self_right, BitVec.reduceToNat] <;> decide +kernel
    · exact ht30
  have ht32 : memLoad m32 (sp + 56) 64 = memLoad mem (sp + 56) 64 := by
    apply Eq.trans (b := memLoad m31 (sp + 56) 64)
    · apply memLoad_memStore_of_rangeApart
      apply hap
      dsimp only [dst]
      simp only [BitVec.ofNat_eq_ofNat, add_sub_self_right, BitVec.reduceToNat] <;> decide +kernel
    · exact ht31
  have ht33 : memLoad m33 (sp + 56) 64 = memLoad mem (sp + 56) 64 := by
    apply Eq.trans (b := memLoad m32 (sp + 56) 64)
    · apply memLoad_memStore_of_rangeApart
      apply hap
      dsimp only [dst]
      simp only [BitVec.ofNat_eq_ofNat, add_sub_self_right, BitVec.reduceToNat] <;> decide +kernel
    · exact ht32
  have ht34 : memLoad m34 (sp + 56) 64 = memLoad mem (sp + 56) 64 := by
    apply Eq.trans (b := memLoad m33 (sp + 56) 64)
    · apply memLoad_memStore_of_rangeApart
      apply hap
      dsimp only [dst]
      simp only [BitVec.ofNat_eq_ofNat, add_sub_self_right, BitVec.reduceToNat] <;> decide +kernel
    · exact ht33
  have ht35 : memLoad m35 (sp + 56) 64 = memLoad mem (sp + 56) 64 := by
    apply Eq.trans (b := memLoad m34 (sp + 56) 64)
    · apply memLoad_memStore_of_rangeApart
      apply hap
      dsimp only [dst]
      simp only [BitVec.ofNat_eq_ofNat, add_sub_self_right, BitVec.reduceToNat] <;> decide +kernel
    · exact ht34
  have ht36 : memLoad m36 (sp + 56) 64 = memLoad mem (sp + 56) 64 := by
    apply Eq.trans (b := memLoad m35 (sp + 56) 64)
    · apply memLoad_memStore_of_rangeApart
      apply hap
      dsimp only [dst]
      simp only [BitVec.ofNat_eq_ofNat, add_sub_self_right, BitVec.reduceToNat] <;> decide +kernel
    · exact ht35
  have ht37 : memLoad m37 (sp + 56) 64 = memLoad mem (sp + 56) 64 := by
    apply Eq.trans (b := memLoad m36 (sp + 56) 64)
    · apply memLoad_memStore_of_rangeApart
      apply hap
      dsimp only [dst]
      simp only [BitVec.ofNat_eq_ofNat, add_sub_self_right, BitVec.reduceToNat] <;> decide +kernel
    · exact ht36
  have ht38 : memLoad m38 (sp + 56) 64 = memLoad mem (sp + 56) 64 := by
    apply Eq.trans (b := memLoad m37 (sp + 56) 64)
    · apply memLoad_memStore_of_rangeApart
      apply hap
      dsimp only [dst]
      simp only [BitVec.ofNat_eq_ofNat, add_sub_self_right, BitVec.reduceToNat] <;> decide +kernel
    · exact ht37
  have ht39 : memLoad m39 (sp + 56) 64 = memLoad mem (sp + 56) 64 := by
    apply Eq.trans (b := memLoad m38 (sp + 56) 64)
    · apply memLoad_memStore_of_rangeApart
      apply hap
      dsimp only [dst]
      simp only [BitVec.ofNat_eq_ofNat, add_sub_self_right, BitVec.reduceToNat] <;> decide +kernel
    · exact ht38
  have ht40 : memLoad m40 (sp + 56) 64 = memLoad mem (sp + 56) 64 := by
    apply Eq.trans (b := memLoad m39 (sp + 56) 64)
    · apply memLoad_memStore_of_rangeApart
      apply hap
      dsimp only [dst]
      simp only [BitVec.ofNat_eq_ofNat, add_sub_self_right, BitVec.reduceToNat] <;> decide +kernel
    · exact ht39
  have ht41 : memLoad m41 (sp + 56) 64 = memLoad mem (sp + 56) 64 := by
    apply Eq.trans (b := memLoad m40 (sp + 56) 64)
    · apply memLoad_memStore_of_rangeApart
      apply hap
      dsimp only [dst]
      simp only [BitVec.ofNat_eq_ofNat, add_sub_self_right, BitVec.reduceToNat] <;> decide +kernel
    · exact ht40
  have ht42 : memLoad m42 (sp + 56) 64 = memLoad mem (sp + 56) 64 := by
    apply Eq.trans (b := memLoad m41 (sp + 56) 64)
    · apply memLoad_memStore_of_rangeApart
      apply hap
      dsimp only [dst]
      simp only [BitVec.ofNat_eq_ofNat, add_sub_self_right, BitVec.reduceToNat] <;> decide +kernel
    · exact ht41
  have ht43 : memLoad m43 (sp + 56) 64 = memLoad mem (sp + 56) 64 := by
    apply Eq.trans (b := memLoad m42 (sp + 56) 64)
    · apply memLoad_memStore_of_rangeApart
      apply hap
      dsimp only [dst]
      simp only [BitVec.ofNat_eq_ofNat, add_sub_self_right, BitVec.reduceToNat] <;> decide +kernel
    · exact ht42
  have ht44 : memLoad m44 (sp + 56) 64 = memLoad mem (sp + 56) 64 := by
    apply Eq.trans (b := memLoad m43 (sp + 56) 64)
    · apply memLoad_memStore_of_rangeApart
      apply hap
      dsimp only [dst]
      simp only [BitVec.ofNat_eq_ofNat, add_sub_self_right, BitVec.reduceToNat] <;> decide +kernel
    · exact ht43
  have ht45 : memLoad m45 (sp + 56) 64 = memLoad mem (sp + 56) 64 := by
    apply Eq.trans (b := memLoad m44 (sp + 56) 64)
    · apply memLoad_memStore_of_rangeApart
      apply hap
      dsimp only [dst]
      simp only [BitVec.ofNat_eq_ofNat, add_sub_self_right, BitVec.reduceToNat] <;> decide +kernel
    · exact ht44
  have ht46 : memLoad m46 (sp + 56) 64 = memLoad mem (sp + 56) 64 := by
    apply Eq.trans (b := memLoad m45 (sp + 56) 64)
    · apply memLoad_memStore_of_rangeApart
      apply hap
      dsimp only [dst]
      simp only [BitVec.ofNat_eq_ofNat, add_sub_self_right, BitVec.reduceToNat] <;> decide +kernel
    · exact ht45
  have ht47 : memLoad m47 (sp + 56) 64 = memLoad mem (sp + 56) 64 := by
    apply Eq.trans (b := memLoad m46 (sp + 56) 64)
    · apply memLoad_memStore_of_rangeApart
      apply hap
      dsimp only [dst]
      simp only [BitVec.ofNat_eq_ofNat, add_sub_self_right, BitVec.reduceToNat] <;> decide +kernel
    · exact ht46
  have ht48 : memLoad m48 (sp + 56) 64 = memLoad mem (sp + 56) 64 := by
    apply Eq.trans (b := memLoad m47 (sp + 56) 64)
    · apply memLoad_memStore_of_rangeApart
      apply hap
      dsimp only [dst]
      simp only [BitVec.ofNat_eq_ofNat, add_sub_self_right, BitVec.reduceToNat] <;> decide +kernel
    · exact ht47
  have ht49 : memLoad m49 (sp + 56) 64 = memLoad mem (sp + 56) 64 := by
    apply Eq.trans (b := memLoad m48 (sp + 56) 64)
    · apply memLoad_memStore_of_rangeApart
      apply hap
      dsimp only [dst]
      simp only [BitVec.ofNat_eq_ofNat, add_sub_self_right, BitVec.reduceToNat] <;> decide +kernel
    · exact ht48
  have ht50 : memLoad m50 (sp + 56) 64 = memLoad mem (sp + 56) 64 := by
    apply Eq.trans (b := memLoad m49 (sp + 56) 64)
    · apply memLoad_memStore_of_rangeApart
      apply hap
      dsimp only [dst]
      simp only [BitVec.ofNat_eq_ofNat, add_sub_self_right, BitVec.reduceToNat] <;> decide +kernel
    · exact ht49
  have ht51 : memLoad m51 (sp + 56) 64 = memLoad mem (sp + 56) 64 := by
    apply Eq.trans (b := memLoad m50 (sp + 56) 64)
    · apply memLoad_memStore_of_rangeApart
      apply hap
      dsimp only [dst]
      simp only [BitVec.ofNat_eq_ofNat, add_sub_self_right, BitVec.reduceToNat] <;> decide +kernel
    · exact ht50
  have ht52 : memLoad m52 (sp + 56) 64 = memLoad mem (sp + 56) 64 := by
    apply Eq.trans (b := memLoad m51 (sp + 56) 64)
    · apply memLoad_memStore_of_rangeApart
      apply hap
      dsimp only [dst]
      simp only [BitVec.ofNat_eq_ofNat, add_sub_self_right, BitVec.reduceToNat] <;> decide +kernel
    · exact ht51
  have ht53 : memLoad m53 (sp + 56) 64 = memLoad mem (sp + 56) 64 := by
    apply Eq.trans (b := memLoad m52 (sp + 56) 64)
    · apply memLoad_memStore_of_rangeApart
      apply hap
      dsimp only [dst]
      simp only [BitVec.ofNat_eq_ofNat, add_sub_self_right, BitVec.reduceToNat] <;> decide +kernel
    · exact ht52
  have ht54 : memLoad m54 (sp + 56) 64 = memLoad mem (sp + 56) 64 := by
    apply Eq.trans (b := memLoad m53 (sp + 56) 64)
    · apply memLoad_memStore_of_rangeApart
      apply hap
      dsimp only [dst]
      simp only [BitVec.ofNat_eq_ofNat, add_sub_self_right, BitVec.reduceToNat] <;> decide +kernel
    · exact ht53
  have ht55 : memLoad m55 (sp + 56) 64 = memLoad mem (sp + 56) 64 := by
    apply Eq.trans (b := memLoad m54 (sp + 56) 64)
    · apply memLoad_memStore_of_rangeApart
      apply hap
      dsimp only [dst]
      simp only [BitVec.ofNat_eq_ofNat, add_sub_self_right, BitVec.reduceToNat] <;> decide +kernel
    · exact ht54
  have ht56 : memLoad m56 (sp + 56) 64 = memLoad mem (sp + 56) 64 := by
    apply Eq.trans (b := memLoad m55 (sp + 56) 64)
    · apply memLoad_memStore_of_rangeApart
      apply hap
      dsimp only [dst]
      simp only [BitVec.ofNat_eq_ofNat, add_sub_self_right, BitVec.reduceToNat] <;> decide +kernel
    · exact ht55
  have ht57 : memLoad m57 (sp + 56) 64 = memLoad mem (sp + 56) 64 := by
    apply Eq.trans (b := memLoad m56 (sp + 56) 64)
    · apply memLoad_memStore_of_rangeApart
      apply hap
      dsimp only [dst]
      simp only [BitVec.ofNat_eq_ofNat, add_sub_self_right, BitVec.reduceToNat] <;> decide +kernel
    · exact ht56
  have ht58 : memLoad m58 (sp + 56) 64 = memLoad mem (sp + 56) 64 := by
    apply Eq.trans (b := memLoad m57 (sp + 56) 64)
    · apply memLoad_memStore_of_rangeApart
      apply hap
      dsimp only [dst]
      simp only [BitVec.ofNat_eq_ofNat, add_sub_self_right, BitVec.reduceToNat] <;> decide +kernel
    · exact ht57
  have ht59 : memLoad m59 (sp + 56) 64 = memLoad mem (sp + 56) 64 := by
    apply Eq.trans (b := memLoad m58 (sp + 56) 64)
    · apply memLoad_memStore_of_rangeApart
      apply hap
      dsimp only [dst]
      simp only [BitVec.ofNat_eq_ofNat, add_sub_self_right, BitVec.reduceToNat] <;> decide +kernel
    · exact ht58
  have ht60 : memLoad m60 (sp + 56) 64 = memLoad mem (sp + 56) 64 := by
    apply Eq.trans (b := memLoad m59 (sp + 56) 64)
    · apply memLoad_memStore_of_rangeApart
      apply hap
      dsimp only [dst]
      simp only [BitVec.ofNat_eq_ofNat, add_sub_self_right, BitVec.reduceToNat] <;> decide +kernel
    · exact ht59
  have ht61 : memLoad m61 (sp + 56) 64 = memLoad mem (sp + 56) 64 := by
    apply Eq.trans (b := memLoad m60 (sp + 56) 64)
    · apply memLoad_memStore_of_rangeApart
      apply hap
      dsimp only [dst]
      simp only [BitVec.ofNat_eq_ofNat, add_sub_self_right, BitVec.reduceToNat] <;> decide +kernel
    · exact ht60
  have ht62 : memLoad m62 (sp + 56) 64 = memLoad mem (sp + 56) 64 := by
    apply Eq.trans (b := memLoad m61 (sp + 56) 64)
    · apply memLoad_memStore_of_rangeApart
      apply hap
      dsimp only [dst]
      simp only [BitVec.ofNat_eq_ofNat, add_sub_self_right, BitVec.reduceToNat] <;> decide +kernel
    · exact ht61
  have ht63 : memLoad m63 (sp + 56) 64 = memLoad mem (sp + 56) 64 := by
    apply Eq.trans (b := memLoad m62 (sp + 56) 64)
    · apply memLoad_memStore_of_rangeApart
      apply hap
      dsimp only [dst]
      simp only [BitVec.ofNat_eq_ofNat, add_sub_self_right, BitVec.reduceToNat] <;> decide +kernel
    · exact ht62
  have ht64 : memLoad m64 (sp + 56) 64 = memLoad mem (sp + 56) 64 := by
    apply Eq.trans (b := memLoad m63 (sp + 56) 64)
    · apply memLoad_memStore_of_rangeApart
      apply hap
      dsimp only [dst]
      simp only [BitVec.ofNat_eq_ofNat, add_sub_self_right, BitVec.reduceToNat] <;> decide +kernel
    · exact ht63
  have hfinalret : (memLoad m64 (sp + 56) 64).toNat < 2^32 := by
    rw [ht64]
    exact hret
  simp (config := {maxDischargeDepth := 128, maxSteps := 10000000})
    (disch := (try simp only [BitVec.ofNat_eq_ofNat]); first
      | (apply outputStoreGuard hc hw <;> first
          | assumption
          | decide +kernel)
      | (apply hz <;> first
          | assumption
          | decide +kernel)
      | (apply LoadOk.of_offsets (b := src) (x := src) (len := 64) ?_ rfl
            (addr_self src) <;> first
          | assumption
          | decide +kernel)
      | (apply LoadOk.of_offsets (b := src) (x := src) (len := 64) ?_ (addr_self src)
            (addr_self src) <;> first
          | assumption
          | decide +kernel)
      | (apply LoadOk.of_offsets (b := sp) (x := sp) (len := 64) ?_ rfl
            (addr_self sp) <;> first
          | assumption
          | decide +kernel)
      | (refine And.intro ?_ ?_ <;> first
          | (apply LoadOk.of_offsets (b := sp) (x := sp) (len := 64) ?_ rfl
                (addr_self sp) <;> first
              | assumption
              | decide +kernel)
          | (simpa only [sp, BitVec.ofNat_eq_ofNat] using hfinalret))) only [ite_eq_left]
  refine ⟨_, rfl, hmodel, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  · rfl
  · intro r
    have hr : r = 0 ∨ r = 1 ∨ r = 2 ∨ r = 3 ∨ r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨
        r = 8 ∨ r = 9 ∨ r = 10 ∨ r = 11 ∨ r = 12 ∨ r = 13 ∨ r = 14 ∨ r = 15 := by
      have := r.isLt
      omega
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first | rfl | exact hTypes 7 | exact hTypes 11

end AesGcm.Proofs.Machine.AES64

namespace AesGcm.Proofs.Machine.AES64

open AesGcm.Proofs.Machine.Fixslice AesGcm.Proofs.Machine.Runtime
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift
  X86Proofs.Refine AesGcm.Proofs.Machine.LIR
open AesGcm.Proofs.Machine.Fixslice AesGcm.Proofs.Machine.Runtime
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift
  X86Proofs.Refine AesGcm.Proofs.Machine.Runtime AesGcm.Proofs.Machine.LIR

theorem output_exactAtoms_facts (code : CodeMap) (fr : Activation)
    (args : Values Value Reg.count)
    (h : Atom.All code args fr.original (Fn10a210.frameInfo.entryAtoms fr)) :
    args[4] = ⟨64, fr.rsp⟩ ∧ args[22] = ⟨1, 0⟩ ∧
    args[2] = ⟨64, fr.rdx⟩ ∧ args[3] = ⟨64, fr.rbx⟩ ∧
    args[5] = ⟨64, fr.rbp⟩ ∧ args[6] = ⟨64, fr.rsi⟩ ∧ args[7] = ⟨64, fr.rdi⟩ ∧
    args[12] = ⟨64, fr.r12⟩ ∧ args[13] = ⟨64, fr.r13⟩ ∧
    args[14] = ⟨64, fr.r14⟩ ∧ args[15] = ⟨64, fr.r15⟩ ∧
    args[39] = ⟨32, fr.mxcsr⟩ ∧ args[50] = ⟨16, fr.ftw⟩ ∧ args[51] = ⟨16, fr.fcw⟩ ∧
    Readable fr.original fr.rsp 8 ∧ memLoad fr.original fr.rsp 64 = fr.ret ∧
    fr.ret.toNat < 2^32 ∧ Writable code fr.original (fr.rsp - 192) 192 ∧
    fr.low.toNat + 192 ≤ fr.rsp.toNat := by
  simp only [Fn10a210.frameInfo, FrameInfo.entryAtoms, FrameInfo.entryFrame,
    FrameInfo.frameAtoms, FrameInfo.entryRegs, FrameInfo.stackAtoms, FrameInfo.window,
    FrameInfo.callSlotAtoms, Activation.below, Activation.entryReg, Activation.entryValue, List.map_cons,
    List.map_nil, List.nil_append, List.cons_append, List.append_nil, Option.getD_some,
    Nat.reduceEqDiff, ↓reduceIte, Atom.All, Atom.gpr, Atom.Holds,
    ] at h
  rcases h with ⟨hsp, hdf, h1, h2, h3, h5, h6, h7, h8, h9, h12, h13, h14, h15, h39, h50, h51,
    hr, hrt, hrlo, hs, hm, ha⟩
  exact ⟨hsp, hdf, h2, h3, h5, h6, h7, h12, h13, h14, h15, h39, h50, h51, hr, hrt, hrlo, hs, hm⟩

end AesGcm.Proofs.Machine.AES64

namespace AesGcm.Proofs.Machine.AES64

open AesGcm.Proofs.Machine.Fixslice AesGcm.Proofs.Machine.Runtime
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift
  X86Proofs.Refine AesGcm.Proofs.Machine.LIR
open AesGcm.Proofs.Machine.Fixslice AesGcm.Proofs.Machine.Runtime
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine AesGcm.Proofs.Machine.Runtime
theorem output_call_memory (code : CodeMap) (fr : Activation) (rax : BitVec 64)
    (hroom : fr.low.toNat + 192 ≤ fr.rsp.toNat)
    (hstack : Writable code fr.original (fr.rsp - 192) 192)
    (hreturn : Readable fr.original fr.rsp 8)
    (hret : memLoad fr.original fr.rsp 64 = fr.ret)
    (hi : Readable fr.original fr.rsi 64)
    (hw : Writable code fr.original fr.rdi 64)
    (hso : (callStack fr).Disjoint (span fr.rdi 64))
    (hsi : (callStack fr).Disjoint (span fr.rsi 64))
    (hoi : (span fr.rdi 64).Disjoint (span fr.rsi 64)) :
    let mem := outputSavedMemory fr rax
    Readable mem fr.rsi 64 ∧ Writable code mem fr.rdi 64 ∧
      Readable mem (fr.rsp - 56) 64 ∧
      RangeApart fr.rdi 64 (fr.rsp - 56) 64 ∧
      RangeApart (fr.rsp - 56) 64 fr.rsi 64 ∧
      RangeApart fr.rdi 64 fr.rsi 64 ∧
      (∀ p : Fin 8, memLoad mem (fr.rsi + BitVec.ofNat 64 (8 * p.val)) 64 =
        memLoad fr.original (fr.rsi + BitVec.ofNat 64 (8 * p.val)) 64) ∧
      memLoad mem fr.rsp 64 = fr.ret ∧
      RamWriteFrame fr.original mem [fr.region] := by
  dsimp only
  have hf := outputSavedMemory_frame fr rax (by omega)
  have hrsp : 192 ≤ fr.rsp.toNat := by omega
  have rsp_sub (k : Nat) (hk : k ≤ 192) :
      (fr.rsp - BitVec.ofNat 64 k).toNat = fr.rsp.toNat - k := by
    have hle : BitVec.ofNat 64 k ≤ fr.rsp := by
      change (BitVec.ofNat 64 k).toNat ≤ fr.rsp.toNat
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega)]
      omega
    rw [BitVec.toNat_sub_of_le hle, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show k < 2^64 by omega)]
  have hs56 := rsp_sub 56 (by omega)
  have hs192 := rsp_sub 192 (by omega)
  change (fr.rsp - 56).toNat = fr.rsp.toNat - 56 at hs56
  change (fr.rsp - 192).toNat = fr.rsp.toNat - 192 at hs192
  have separated (a : BitVec 64) (hsep : (callStack fr).Disjoint (span a 64)) :
      (fr.rsp.toNat + 8 ≤ a.toNat ∨ a.toNat + 64 ≤ fr.low.toNat) := by
    apply Classical.byContradiction
    intro h
    have h1 : fr.low.toNat < a.toNat + 64 := by omega
    have h2 : a.toNat < fr.rsp.toNat + 8 := by omega
    have hc := hsep (max fr.low.toNat a.toNat)
    simp only [MemoryRegion.Contains, callStack, span] at hc
    exact hc (by omega) (by omega)
  have hspO := separated fr.rdi hso
  have hspI := separated fr.rsi hsi
  have hsorig : Readable fr.original (fr.rsp - 56) 64 := by
    refine ⟨by have := hreturn.low; omega, ?_⟩
    intro i hibar
    by_cases hb : i < 56
    · have haddr : fr.rsp - 56 + BitVec.ofNat 64 i =
          fr.rsp - 192 + BitVec.ofNat 64 (136 + i) := by
        rw [BitVec.ofNat_add]
        bv_omega
      rw [haddr]
      exact hstack.readable.present (136 + i) (by omega)
    · have haddr : fr.rsp - 56 + BitVec.ofNat 64 i =
          fr.rsp + BitVec.ofNat 64 (i - 56) := by
        have hi' : i = 56 + (i - 56) := by omega
        conv => lhs; rw [hi', BitVec.ofNat_add]
        bv_omega
      rw [haddr]
      exact hreturn.present (i - 56) (by omega)
  have hso' : RangeApart fr.rdi 64 (fr.rsp - 56) 64 := by
    apply RangeApart.of_toNat
    · have := hw.readable.low; omega
    · have := hreturn.low; omega
    · omega
  have hsi' : RangeApart (fr.rsp - 56) 64 fr.rsi 64 := by
    apply RangeApart.of_toNat
    · have := hreturn.low; omega
    · have := hi.low; omega
    · omega
  have hoi' : RangeApart fr.rdi 64 fr.rsi 64 := by
    apply RangeApart.of_toNat
    · have := hw.readable.low; omega
    · have := hi.low; omega
    · apply Classical.byContradiction
      intro h
      have hc := hoi (max fr.rdi.toNat fr.rsi.toNat)
      simp only [MemoryRegion.Contains, span] at hc
      exact hc (by omega) (by omega)
  have hplanes (p : Fin 8) :
      memLoad (outputSavedMemory fr rax) (fr.rsi + BitVec.ofNat 64 (8 * p.val)) 64 =
        memLoad fr.original (fr.rsi + BitVec.ofNat 64 (8 * p.val)) 64 := by
    apply hf.memLoad_eq
    have haddr : (fr.rsi + BitVec.ofNat 64 (8 * p.val)).toNat =
        fr.rsi.toNat + 8 * p.val := by
      have := hi.low
      rw [BitVec.toNat_add, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (show 8 * p.val < 2^64 by omega), Nat.mod_eq_of_lt (by omega)]
    refine ⟨by have := hi.low; omega, ?_⟩
    intro r hr
    have he : r = fr.region := List.mem_singleton.mp hr
    subst r
    simp only [Activation.region]
    omega
  have hret' : memLoad (outputSavedMemory fr rax) fr.rsp 64 = fr.ret := by
    rw [hf.memLoad_eq, hret]
    refine ⟨by have := hreturn.low; omega, ?_⟩
    intro r hr
    have he : r = fr.region := List.mem_singleton.mp hr
    subst r
    simp only [Activation.region]
    omega
  exact ⟨hi.of_frame hf, hw.of_frame hf, hsorig.of_frame hf,
    hso', hsi', hoi', hplanes, hret', hf⟩

end AesGcm.Proofs.Machine.AES64

namespace AesGcm.Proofs.Machine.AES64

open AesGcm.Proofs.Machine.Fixslice AesGcm.Proofs.Machine.Runtime
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift
  X86Proofs.Refine AesGcm.Proofs.Machine.LIR
open AesGcm.Proofs.Machine.Fixslice AesGcm.Proofs.Machine.Runtime
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift
  X86Proofs.Refine AesGcm.Proofs.Machine.Runtime AesGcm.Proofs.Machine.LIR

theorem output_call_post (code : CodeMap) (fr : Activation) (rax : BitVec 64)
    (x : Planes) (o : Output Value Ram Reg.count)
    (hroom : fr.low.toNat + 192 ≤ fr.rsp.toNat)
    (hlow : fr.rdi.toNat + 64 ≤ 2^32)
    (hsep : RangeApart fr.rdi 64 (fr.rsp - 56) 64)
    (hret : memLoad fr.original fr.rsp 64 = fr.ret)
    (hm : o.store = outputStoredBytes (outputSavedMemory fr rax) fr.rdi x)
    (htag : o.tag = some ⟨64, memLoad o.store ((fr.rsp - 56) + 56) 64⟩)
    (hsp : o.values[4] = ⟨64, (fr.rsp - 56) + 64⟩)
    (hdf : o.values[22] = ⟨1, 0⟩)
    (h3 : o.values[3] = ⟨64, memLoad o.store ((fr.rsp - 56) + 8) 64⟩)
    (h12 : o.values[12] = ⟨64, memLoad o.store ((fr.rsp - 56) + 16) 64⟩)
    (h13 : o.values[13] = ⟨64, memLoad o.store ((fr.rsp - 56) + 24) 64⟩)
    (h14 : o.values[14] = ⟨64, memLoad o.store ((fr.rsp - 56) + 32) 64⟩)
    (h15 : o.values[15] = ⟨64, memLoad o.store ((fr.rsp - 56) + 40) 64⟩)
    (h5 : o.values[5] = ⟨64, memLoad o.store ((fr.rsp - 56) + 48) 64⟩)
    (h39 : o.values[39] = ⟨32, fr.mxcsr⟩)
    (h50 : o.values[50] = ⟨16, fr.ftw⟩)
    (h51 : o.values[51] = ⟨16, fr.fcw⟩) :
    o.tag = some ⟨64, fr.ret⟩ ∧
      Atom.All code o.values o.store (Fn10a210.frameInfo.doneAtoms fr) ∧
      RamWriteFrame fr.original o.store [fr.region, span fr.rdi 64] ∧
      memoryBlocks o.store fr.rdi = decode x := by
  have saved (j : Fin 7) :
      memLoad o.store (fr.rsp - BitVec.ofNat 64 (8 * j.val)) 64 = inputSavedValue fr j := by
    rw [hm, outputStoredBytes_memLoad x 64, outputSavedMemory_memLoad]
    have hj : 8 * j.val ≤ 56 := by omega
    have ha : fr.rsp - BitVec.ofNat 64 (8 * j.val) =
        (fr.rsp - 56) + BitVec.ofNat 64 (56 - 8 * j.val) := by
      apply (BitVec.add_left_inj (BitVec.ofNat 64 (8 * j.val))).mp
      rw [BitVec.sub_add_cancel, BitVec.add_assoc, ← BitVec.ofNat_add,
        Nat.sub_add_cancel hj]
      bv_omega
    rw [ha]
    exact RangeApart.right_sub hsep (by omega)
  have sl0 : memLoad o.store ((fr.rsp - 56) + 56) 64 = fr.ret := by
    rw [BitVec.sub_add_cancel]
    have h0 := saved (0 : Fin 7)
    have ha : fr.rsp - BitVec.ofNat 64 (8 * (0 : Fin 7).val) = fr.rsp := by
      change fr.rsp - 0 = fr.rsp
      exact BitVec.sub_zero _
    simpa only [ha, inputSavedValue] using h0.trans hret
  have sl3 : memLoad o.store ((fr.rsp - 56) + 8) 64 = fr.rbx := by
    have ha : (fr.rsp - 56) + 8 = fr.rsp - BitVec.ofNat 64 (8 * (6 : Fin 7).val) := by
      change (fr.rsp - 56) + 8 = fr.rsp - 48
      bv_omega
    rw [ha]
    exact saved 6
  have sl12 : memLoad o.store ((fr.rsp - 56) + 16) 64 = fr.r12 := by
    have ha : (fr.rsp - 56) + 16 = fr.rsp - BitVec.ofNat 64 (8 * (5 : Fin 7).val) := by
      change (fr.rsp - 56) + 16 = fr.rsp - 40
      bv_omega
    rw [ha]
    exact saved 5
  have sl13 : memLoad o.store ((fr.rsp - 56) + 24) 64 = fr.r13 := by
    have ha : (fr.rsp - 56) + 24 = fr.rsp - BitVec.ofNat 64 (8 * (4 : Fin 7).val) := by
      change (fr.rsp - 56) + 24 = fr.rsp - 32
      bv_omega
    rw [ha]
    exact saved 4
  have sl14 : memLoad o.store ((fr.rsp - 56) + 32) 64 = fr.r14 := by
    have ha : (fr.rsp - 56) + 32 = fr.rsp - BitVec.ofNat 64 (8 * (3 : Fin 7).val) := by
      change (fr.rsp - 56) + 32 = fr.rsp - 24
      bv_omega
    rw [ha]
    exact saved 3
  have sl15 : memLoad o.store ((fr.rsp - 56) + 40) 64 = fr.r15 := by
    have ha : (fr.rsp - 56) + 40 = fr.rsp - BitVec.ofNat 64 (8 * (2 : Fin 7).val) := by
      change (fr.rsp - 56) + 40 = fr.rsp - 16
      bv_omega
    rw [ha]
    exact saved 2
  have sl5 : memLoad o.store ((fr.rsp - 56) + 48) 64 = fr.rbp := by
    have ha : (fr.rsp - 56) + 48 = fr.rsp - BitVec.ofNat 64 (8 * (1 : Fin 7).val) := by
      change (fr.rsp - 56) + 48 = fr.rsp - 8
      bv_omega
    rw [ha]
    exact saved 1
  have rsp_done : (fr.rsp - 56) + 64 = fr.rsp + 8 := by bv_omega
  rw [sl0] at htag
  rw [rsp_done] at hsp
  rw [sl3] at h3
  rw [sl12] at h12
  rw [sl13] at h13
  rw [sl14] at h14
  rw [sl15] at h15
  rw [sl5] at h5
  have hs := outputSavedMemory_frame fr rax (by omega)
  have hs' : RamWriteFrame fr.original (outputSavedMemory fr rax)
      [fr.region, span fr.rdi 64] := by
    refine ⟨fun a ha ↦ hs.outside a ⟨ha.1, ?_⟩, hs.present⟩
    intro r hr
    exact ha.2 r (List.mem_cons.mpr (Or.inl (List.mem_singleton.mp hr)))
  have hout : InRegions [fr.region, span fr.rdi 64] fr.rdi 64 := by
    refine ⟨span fr.rdi 64, by simp, ?_⟩
    simp only [InRegion, span]
    omega
  refine ⟨htag, ?_, ?_, ?_⟩
  · simp only [Fn10a210.frameInfo, FrameInfo.doneAtoms, List.map_cons, List.map_nil,
      Atom.gpr, Activation.entryReg, Activation.entryValue]
    exact ⟨hsp, hdf, h3, h5, h12, h13, h14, h15, h39, h50, h51, trivial⟩
  · rw [hm]
    exact outputStoredBytes_frame x hs' hout
  · rw [hm, memoryBlocks_outputStoredBytes]

end AesGcm.Proofs.Machine.AES64


namespace AesGcm.Proofs.Machine.AES64

open AesGcm.Proofs.Machine.Fixslice AesGcm.Proofs.Machine.Runtime
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift
  X86Proofs.Refine AesGcm.Proofs.Machine.LIR
open AesGcm.Proofs.Machine.Fixslice AesGcm.Proofs.Machine.Runtime
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift
  X86Proofs.Refine AesGcm.Proofs.Machine.Runtime AesGcm.Proofs.Machine.LIR

set_option maxHeartbeats 1000000 in
theorem output_call (code : CodeMap) (hc : ∀ x ∈ fnCode, x ∈ code) :
    CallContract LIR.lifted code .l10a210 Fn10a210.frameInfo
      (fun fr ↦ [span fr.rdi 64])
      (fun fr mem ↦ fr.rdx = 8 ∧ Readable mem fr.rsi 64 ∧ Writable code mem fr.rdi 64 ∧
        (callStack fr).Disjoint (span fr.rdi 64) ∧
        (callStack fr).Disjoint (span fr.rsi 64) ∧
        (span fr.rdi 64).Disjoint (span fr.rsi 64))
      (fun fr mem ↦ memoryBlocks mem fr.rdi =
        decode (fun p ↦ memLoad fr.original (fr.rsi + BitVec.ofNat 64 (8 * p.val)) 64)) := by
  intro fr loc hl hm hatoms hTypes hpre
  rcases loc with ⟨label, args, mem⟩
  change label = .l10a210 at hl
  subst label
  change mem = fr.original at hm
  subst mem
  rcases hpre with ⟨hlen, hi, hw, hso, hsi, hoi⟩
  obtain ⟨hsarg, hdfarg, h2arg, h3arg, h5arg, h6arg, h7arg, h12arg, h13arg,
    h14arg, h15arg, h39arg, h50arg, h51arg, hreturn, hret, hretlow, hstack, hroom⟩ :=
      output_exactAtoms_facts code fr args hatoms
  have getrsp : (args[4]).get 64 = fr.rsp := by rw [hsarg]; rfl
  have getlen : (args[2]).get 64 = 8 := by rw [h2arg, hlen]; rfl
  obtain ⟨a0, he0, sp0, len0, src0, dst0, df0, fp039, fp050, fp051, ty0⟩ :=
    output_entry_runBlock code args fr.original hc (by simpa only [getrsp] using hstack)
      getlen hTypes
  simp only [getrsp] at sp0
  rw [h2arg] at len0
  rw [h6arg] at src0
  rw [h7arg] at dst0
  rw [hdfarg] at df0
  have get5 : (args[5]).get 64 = fr.rbp := by rw [h5arg]; rfl
  have get15 : (args[15]).get 64 = fr.r15 := by rw [h15arg]; rfl
  have get14 : (args[14]).get 64 = fr.r14 := by rw [h14arg]; rfl
  have get13 : (args[13]).get 64 = fr.r13 := by rw [h13arg]; rfl
  have get12 : (args[12]).get 64 = fr.r12 := by rw [h12arg]; rfl
  have get3 : (args[3]).get 64 = fr.rbx := by rw [h3arg]; rfl
  have he : program.runBlock (dialect code) ⟨.l10a210, args, fr.original⟩ =
      .jump ⟨.l10a224, a0, outputSavedMemory fr ((args[0]).get 64)⟩ := by
    simpa only [getrsp, get5, get15, get14, get13, get12, get3,
      outputSavedMemory, inputSavedMemory] using he0
  let m := outputSavedMemory fr ((args[0]).get 64)
  obtain ⟨hread, hwrite, hsread, hsep, _, _, hplanes, hsavedret, hframe⟩ :=
    output_call_memory code fr ((args[0]).get 64) hroom hstack hreturn hret hi hw hso hsi hoi
  change memLoad m fr.rsp 64 = fr.ret at hsavedret
  obtain ⟨a1, he1, l1, s1, _, i1, o1, d1, fp139, fp150, fp151, ty1⟩ :=
    output_lengthChecks_runBlock code a0 m .l10a224 .l10a22e
      (by simp) (by rw [len0, hlen]; rfl) ty0
  have len1 := l1.trans len0
  have sp1 := s1.trans sp0
  have src1 := i1.trans src0
  have dst1 := o1.trans dst0
  have df1 := d1.trans df0
  obtain ⟨a2, he2, l2, s2, _, i2, o2, d2, fp239, fp250, fp251, ty2⟩ :=
    output_lengthChecks_runBlock code a1 m .l10a22e .l10a238
      (by simp) (by rw [len1, hlen]; rfl) ty1
  have len2 := l2.trans len1
  have sp2 := s2.trans sp1
  have src2 := i2.trans src1
  have dst2 := o2.trans dst1
  have df2 := d2.trans df1
  obtain ⟨a3, he3, l3, s3, _, i3, o3, d3, fp339, fp350, fp351, ty3⟩ :=
    output_lengthChecks_runBlock code a2 m .l10a238 .l10a242
      (by simp) (by rw [len2, hlen]; rfl) ty2
  have len3 := l3.trans len2
  have sp3 := s3.trans sp2
  have src3 := i3.trans src2
  have dst3 := o3.trans dst2
  have df3 := d3.trans df2
  obtain ⟨a4, he4, l4, s4, _, i4, o4, d4, fp439, fp450, fp451, ty4⟩ :=
    output_lengthChecks_runBlock code a3 m .l10a242 .l10a24c
      (by simp) (by rw [len3, hlen]; rfl) ty3
  have len4 := l4.trans len3
  have sp4 := s4.trans sp3
  have src4 := i4.trans src3
  have dst4 := o4.trans dst3
  have df4 := d4.trans df3
  obtain ⟨a5, he5, l5, s5, _, i5, o5, d5, fp539, fp550, fp551, ty5⟩ :=
    output_lengthChecks_runBlock code a4 m .l10a24c .l10a256
      (by simp) (by rw [len4, hlen]; rfl) ty4
  have len5 := l5.trans len4
  have sp5 := s5.trans sp4
  have src5 := i5.trans src4
  have dst5 := o5.trans dst4
  have df5 := d5.trans df4
  obtain ⟨a6, he6, l6, s6, _, i6, o6, d6, fp639, fp650, fp651, ty6⟩ :=
    output_lengthChecks_runBlock code a5 m .l10a256 .l10a260
      (by simp) (by rw [len5, hlen]; rfl) ty5
  have len6 := l6.trans len5
  have sp6 := s6.trans sp5
  have src6 := i6.trans src5
  have dst6 := o6.trans dst5
  have df6 := d6.trans df5
  obtain ⟨a7, he7, l7, s7, _, i7, o7, d7, fp739, fp750, fp751, ty7⟩ :=
    output_lengthChecks_runBlock code a6 m .l10a260 .l10a26a
      (by simp) (by rw [len6, hlen]; rfl) ty6
  have len7 := l7.trans len6
  have sp7 := s7.trans sp6
  have src7 := i7.trans src6
  have dst7 := o7.trans dst6
  have df7 := d7.trans df6
  have getsrc7 : (a7[6]).get 64 = fr.rsi := by rw [src7]; rfl
  have getdst7 : (a7[7]).get 64 = fr.rdi := by rw [dst7]; rfl
  have getsp7 : (a7[4]).get 64 = fr.rsp - 56 := by rw [sp7]; rfl
  obtain ⟨o, hbody, hmodel, htag, hsp, hdf, h3, h12, h13, h14, h15, h5, h39, h50, h51, hty⟩ :=
    outputBody_runBlock code a7 m hc ty7
      (by simpa only [getsrc7] using hread)
      (by simpa only [getdst7] using hwrite)
      (by simpa only [getsp7] using hsread)
      (by simpa only [getdst7, getsp7] using hsep)
      (by simpa only [getsp7, BitVec.sub_add_cancel, hsavedret] using hretlow)
  simp only [getsrc7, getdst7, getsp7, df7] at hmodel htag hsp hdf h3 h12 h13 h14 h15 h5 h39 h50 h51
  simp only [fp739, fp639, fp539, fp439, fp339, fp239, fp139, fp039, h39arg] at h39
  simp only [fp750, fp650, fp550, fp450, fp350, fp250, fp150, fp050, h50arg] at h50
  simp only [fp751, fp651, fp551, fp451, fp351, fp251, fp151, fp051, h51arg] at h51
  have hx : (fun p : Fin 8 ↦ memLoad m (fr.rsi + BitVec.ofNat 64 (8 * p.val)) 64) =
      (fun p : Fin 8 ↦ memLoad fr.original (fr.rsi + BitVec.ofNat 64 (8 * p.val)) 64) :=
    funext hplanes
  rw [hx] at hmodel
  obtain ⟨htag', hdone, hframe', hpost⟩ :=
    output_call_post code fr ((args[0]).get 64) _ o hroom hw.readable.low hsep hret
      hmodel htag hsp hdf h3 h12 h13 h14 h15 h5 h39 h50 h51
  refine ⟨o, ?_, htag', hdone, hty, hframe', hpost⟩
  change program.Exec (dialect code) ⟨⟨.l10a210, args, fr.original⟩, []⟩ o
  apply Program.Exec.next
  · change (program.runBlock (dialect code) ⟨.l10a210, args, fr.original⟩).next
      (dialect code) [] = .next ⟨⟨.l10a224, a0, m⟩, []⟩
    rw [he]
    rfl
  apply Program.Exec.next
  · change (program.runBlock (dialect code) ⟨.l10a224, a0, m⟩).next
      (dialect code) [] = .next ⟨⟨.l10a22e, a1, m⟩, []⟩
    rw [he1]
    rfl
  apply Program.Exec.next
  · change (program.runBlock (dialect code) ⟨.l10a22e, a1, m⟩).next
      (dialect code) [] = .next ⟨⟨.l10a238, a2, m⟩, []⟩
    rw [he2]
    rfl
  apply Program.Exec.next
  · change (program.runBlock (dialect code) ⟨.l10a238, a2, m⟩).next
      (dialect code) [] = .next ⟨⟨.l10a242, a3, m⟩, []⟩
    rw [he3]
    rfl
  apply Program.Exec.next
  · change (program.runBlock (dialect code) ⟨.l10a242, a3, m⟩).next
      (dialect code) [] = .next ⟨⟨.l10a24c, a4, m⟩, []⟩
    rw [he4]
    rfl
  apply Program.Exec.next
  · change (program.runBlock (dialect code) ⟨.l10a24c, a4, m⟩).next
      (dialect code) [] = .next ⟨⟨.l10a256, a5, m⟩, []⟩
    rw [he5]
    rfl
  apply Program.Exec.next
  · change (program.runBlock (dialect code) ⟨.l10a256, a5, m⟩).next
      (dialect code) [] = .next ⟨⟨.l10a260, a6, m⟩, []⟩
    rw [he6]
    rfl
  apply Program.Exec.next
  · change (program.runBlock (dialect code) ⟨.l10a260, a6, m⟩).next
      (dialect code) [] = .next ⟨⟨.l10a26a, a7, m⟩, []⟩
    rw [he7]
    rfl
  apply Program.Exec.done
  change (program.runBlock (dialect code) ⟨.l10a26a, a7, m⟩).next
    (dialect code) [] = .done o
  rw [hbody]
  rfl

end AesGcm.Proofs.Machine.AES64
