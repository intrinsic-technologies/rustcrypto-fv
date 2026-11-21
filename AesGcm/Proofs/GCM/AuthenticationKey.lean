import AesGcm.Proofs.Machine.LIR.Program
import AesGcm.Proofs.Machine.GcmContext
import AesGcm.Proofs.Machine.Runtime.Tactics

namespace AesGcm.Proofs.Machine.GCM
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

def authenticationPackedHalf (b : Standards.NIST.AES.Block) (h : Fin 2) : BitVec 64 :=
  let byte (j : Fin 8) := b[8 * h.val + j.val]'(by omega) |>.toBitVec
  (byte 0 |>.setWidth 64) <<< (56 : Nat) |||
    (byte 1 |>.setWidth 64) <<< (48 : Nat) |||
    (byte 2 |>.setWidth 64) <<< (40 : Nat) |||
    (byte 3 |>.setWidth 64) <<< (32 : Nat) |||
    ((byte 4 |>.setWidth 32) <<< (24 : Nat)).setWidth 64 |||
    ((byte 5 |>.setWidth 32) <<< (16 : Nat)).setWidth 64 |||
    ((byte 6 |>.setWidth 32) <<< (8 : Nat)).setWidth 64 |||
    (byte 7 |>.setWidth 64)

theorem authenticationPackedHalf_eq (b : Standards.NIST.AES.Block) (h : Fin 2) :
    authenticationPackedHalf b h = GcmContext.blockWord b h := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  rw [GcmContext.getLsbD_blockWord b h ⟨i, hi⟩]
  simp only [authenticationPackedHalf, BitVec.getLsbD_or, BitVec.getLsbD_shiftLeft,
    BitVec.getLsbD_setWidth]
  have hb (j : Nat) (hj : 8 ≤ j) (k : Fin 16) : b[k.val].toBitVec.getLsbD j = false :=
    BitVec.getLsbD_of_ge _ _ hj
  have hd : i / 8 = 0 ∨ i / 8 = 1 ∨ i / 8 = 2 ∨ i / 8 = 3 ∨
      i / 8 = 4 ∨ i / 8 = 5 ∨ i / 8 = 6 ∨ i / 8 = 7 := by omega
  rcases hd with hd | hd | hd | hd | hd | hd | hd | hd
  all_goals simp only [Fin.val_zero, Fin.val_one, Fin.val_two]
  all_goals grind


def authenticationHighWord (byte : Fin 16 → BitVec 8) : BitVec 64 :=
  (((byte 6).setWidth 32 <<< (8 : Nat)).setWidth 64 |||
    (((byte 5).setWidth 32 <<< (16 : Nat)).setWidth 64 |||
      (((byte 4).setWidth 32 <<< (24 : Nat)).setWidth 64 |||
        ((byte 3).setWidth 64 <<< (32 : Nat) |||
          ((byte 2).setWidth 64 <<< (40 : Nat) |||
            (byte 1).setWidth 64 <<< (48 : Nat))))) |||
    (byte 7).setWidth 64) ||| (byte 0).setWidth 64 <<< (56 : Nat)

def authenticationLowWord (byte : Fin 16 → BitVec 8) : BitVec 64 :=
  (byte 9).setWidth 64 <<< (48 : Nat) ||| (byte 8).setWidth 64 <<< (56 : Nat) |||
    (byte 10).setWidth 64 <<< (40 : Nat) ||| (byte 11).setWidth 64 <<< (32 : Nat) |||
    (((byte 12).setWidth 32) <<< (24 : Nat)).setWidth 64 |||
    (((byte 13).setWidth 32) <<< (16 : Nat)).setWidth 64 ||| (byte 15).setWidth 64 |||
    (((byte 14).setWidth 32) <<< (8 : Nat)).setWidth 64

theorem authenticationHighWord_or_order (a b c d e f g h : BitVec 64) :
    (g ||| (f ||| (e ||| (d ||| (c ||| b)))) ||| h) ||| a =
      a ||| b ||| c ||| d ||| e ||| f ||| g ||| h := by ac_rfl

theorem authenticationLowWord_or_order (a b c d e f g h : BitVec 64) :
    b ||| a ||| c ||| d ||| e ||| f ||| h ||| g =
      a ||| b ||| c ||| d ||| e ||| f ||| g ||| h := by ac_rfl

theorem authenticationHighWord_eq (b : Standards.NIST.AES.Block) :
    authenticationHighWord (Fixslice16.fromStandard b) = GcmContext.blockWord b 0 := by
  rw [← authenticationPackedHalf_eq]
  exact authenticationHighWord_or_order _ _ _ _ _ _ _ _

theorem authenticationLowWord_eq (b : Standards.NIST.AES.Block) :
    authenticationLowWord (Fixslice16.fromStandard b) = GcmContext.blockWord b 1 := by
  rw [← authenticationPackedHalf_eq]
  exact authenticationLowWord_or_order _ _ _ _ _ _ _ _

def authenticationCarry (byte : Fin 16 → BitVec 8) : BitVec 64 :=
  ((byte 0).setWidth 32 >>> (7 : Nat)).setWidth 64

def authenticationWords (byte : Fin 16 → BitVec 8) : BitVec 64 × BitVec 64 :=
  let c := authenticationCarry byte
  (c + (authenticationLowWord byte <<< (1 : Nat)),
    (c <<< (57 : Nat) ||| (c <<< (62 : Nat) |||
      0x8000000000000000#64 &&& ((byte 0).setWidth 64 <<< (56 : Nat)))) ^^^
        shldResult 1 (authenticationHighWord byte) ((byte 8).setWidth 64 <<< (56 : Nat)))

theorem authenticationCarry_eq (b : Standards.NIST.AES.Block) :
    authenticationCarry (Fixslice16.fromStandard b) = GcmContext.blockWord b 0 >>> (63 : Nat) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [authenticationCarry, Fixslice16.fromStandard, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight]
  by_cases hz : i = 0
  · subst i
    rw [GcmContext.getLsbD_blockWord b 0 ⟨63, by decide⟩]
    rfl
  · have hge : 64 ≤ 63 + i := by omega
    rw [BitVec.getLsbD_of_ge _ _ hge]
    simp only [Fin.val_zero]
    grind

theorem authenticationMask_eq (b : Standards.NIST.AES.Block) :
    0x8000000000000000#64 &&& ((Fixslice16.fromStandard b 0).setWidth 64 <<< (56 : Nat)) =
      authenticationCarry (Fixslice16.fromStandard b) <<< (63 : Nat) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [authenticationCarry, Fixslice16.fromStandard, Fin.val_zero,
    BitVec.getLsbD_and, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth,
    BitVec.getLsbD_ushiftRight]
  by_cases he : i = 63
  · subst i
    simp
  · have hm : (0x8000000000000000#64).getLsbD i = false := by
      rw [BitVec.getLsbD_ofNat]
      change (decide (i < 64) && (2 ^ 63).testBit i) = false
      simp only [Nat.testBit_two_pow, show ¬ 63 = i by omega, decide_false, Bool.and_false]
    simp only [hm, Bool.false_and, show i < 63 by omega, decide_true,
      Bool.not_true, Bool.and_false]

theorem authenticationTopLow_eq (b : Standards.NIST.AES.Block) :
    ((Fixslice16.fromStandard b 8).setWidth 64 <<< (56 : Nat)) >>> (63 : Nat) =
      GcmContext.blockWord b 1 >>> (63 : Nat) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, BitVec.getLsbD_setWidth]
  by_cases hz : i = 0
  · subst i
    rw [GcmContext.getLsbD_blockWord b 1 ⟨63, by decide⟩]
    rfl
  · rw [BitVec.getLsbD_of_ge _ _ (show 64 ≤ 63 + i by omega)]
    simp only [show ¬63 + i < 64 by omega, decide_false, Bool.false_and]


theorem carry_add_eq_or (lo hi : BitVec 64) :
    (hi >>> (63 : Nat)) + (lo <<< (1 : Nat)) =
      (lo <<< (1 : Nat)) ||| (hi >>> (63 : Nat)) := by
  rw [BitVec.add_eq_or_of_and_eq_zero]
  · exact BitVec.or_comm _ _
  · apply BitVec.eq_of_getLsbD_eq
    intro i hi'
    simp only [BitVec.getLsbD_and, BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft,
      BitVec.getLsbD_zero]
    by_cases hz : i = 0
    · subst i
      simp
    · rw [BitVec.getLsbD_of_ge _ _ (show 64 ≤ 63 + i by omega)]
      rfl

theorem carry_reduction_eq (hi : BitVec 64) :
    let c := hi >>> (63 : Nat)
    c <<< (57 : Nat) ||| (c <<< (62 : Nat) ||| c <<< (63 : Nat)) =
      c * 0xc200000000000000#64 := by
  dsimp only
  rw [GHASH.ushr63_eq_msb]
  cases hi.getLsbD 63 <;> decide +kernel

theorem authenticationAdjustment_eq (lo hi : BitVec 64) :
    let c := hi >>> (63 : Nat)
    (c + (lo <<< (1 : Nat)),
      (c <<< (57 : Nat) ||| (c <<< (62 : Nat) ||| c <<< (63 : Nat))) ^^^
        ((hi <<< (1 : Nat)) ||| (lo >>> (63 : Nat)))) = GHASH.polyvalKeyWords lo hi := by
  dsimp only
  rw [carry_add_eq_or, carry_reduction_eq]
  exact congrArg (fun x => ((lo <<< (1 : Nat)) ||| (hi >>> (63 : Nat)), x))
    (BitVec.xor_comm _ _)

theorem authenticationWords_eq (b : Standards.NIST.AES.Block) :
    authenticationWords (Fixslice16.fromStandard b) =
      GHASH.polyvalKeyWords (GcmContext.blockWord b 1) (GcmContext.blockWord b 0) := by
  simp only [authenticationWords, authenticationHighWord_eq, authenticationLowWord_eq]
  rw [authenticationMask_eq b, shldResult]
  simp only [Nat.reduceSub]
  rw [authenticationTopLow_eq b, authenticationCarry_eq b]
  exact authenticationAdjustment_eq _ _

def authenticationMemory (use256 : Bool) (mem : Ram) (sp : BitVec 64)
    (block : Standards.NIST.AES.Block) : Ram :=
  let k := GHASH.polyvalKeyWords (GcmContext.blockWord block 1) (GcmContext.blockWord block 0)
  memStore (memStore (memStore mem sp k.1) (sp + 8) k.2) (sp - 8)
    (if use256 then 0x10229c#64 else 0x10215c#64)

theorem authenticationMemory_eq (use256 : Bool) (mem : Ram) (sp : BitVec 64)
    (block : Standards.NIST.AES.Block)
    (hblock : Fixslice.memoryBlock mem sp = Fixslice16.fromStandard block) :
    let k := authenticationWords (fun j : Fin 16 => memLoad mem (sp + BitVec.ofNat 64 j.val) 8)
    memStore (memStore (memStore mem sp k.1) (sp + 8) k.2) (sp - 8)
      (if use256 then 0x10229c#64 else 0x10215c#64) =
        authenticationMemory use256 mem sp block := by
  have hbytes : (fun j : Fin 16 => memLoad mem (sp + BitVec.ofNat 64 j.val) 8) =
      Fixslice16.fromStandard block := by
    funext j
    rw [memLoad_8]
    exact congrFun hblock j
  dsimp only
  rw [hbytes, authenticationWords_eq]
  rfl

set_option maxHeartbeats 1600000 in
theorem authenticationKey_call (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) (args : Values Value Reg.count) (mem : Ram)
    (block : Standards.NIST.AES.Block)
    (hstack : Writable code mem (args[4].get 64 - 8) 24)
    (hr : Readable mem (args[4].get 64) 16)
    (hblock : Fixslice.memoryBlock mem (args[4].get 64) = Fixslice16.fromStandard block) :
    ∃ (callee : LIR.lifted.Location), ∃ continuation,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l1021ac else .l10206c), args, mem⟩ = .call callee continuation ∧
      callee.label = .l102b80 ∧
      continuation.target = (if use256 then .l10229c else .l10215c) ∧
      continuation.guard = some ⟨64, if use256 then 0x10229c else 0x10215c⟩ ∧
      callee.store = authenticationMemory use256 mem (args[4].get 64) block ∧
      callee.arguments[4]'(by change 4 < 53; decide) = ⟨64, args[4].get 64 - 8⟩ ∧
      callee.arguments[7]'(by change 7 < 53; decide) = ⟨64, args[3].get 64⟩ ∧
      callee.arguments[6]'(by change 6 < 53; decide) = ⟨64, args[4].get 64⟩ ∧
      (∀ r : Fin 53, r.val ∈ [3,5,12,13,14,15,22,39,50,51] → callee.arguments[r] = args[r]) ∧
      (GPRsTyped args → GPRsTyped callee.arguments) := by
  cases use256
  · have hhelperApart {m : Ram} {a : BitVec 64} {n : Nat}
        (h : Writable code m a n) : RangeApart a n 0x10206c 240 := by
      have hx := storeOk_of_codeRange h (fun x hx => hcode x (LIR.code_l10206c x hx))
      have hl : LIR.bytes_l10206c.length = 240 := by decide +kernel
      rw [hl] at hx
      exact hx.apart
    refine ⟨?_, ?_, ?exec, ?_, ?_, ?_, ?store, ?_, ?_, ?_, ?_, ?_⟩
    case exec =>
      change LIR.program.runBlock (dialect code) ⟨.l10206c, args, mem⟩ = _
      cfg_eval []
      runtime_guards call
      rfl
    case store =>
      have hmem := authenticationMemory_eq false mem (args[4].get 64) block hblock
      simp only [authenticationWords, authenticationCarry, authenticationHighWord,
        authenticationLowWord, Fin.val_zero, BitVec.add_zero] at hmem
      exact hmem
    all_goals first
      | rfl
      | (intro hTypes; runtime_typed)
      | (rintro ⟨r, hr⟩ hin; simp only [List.mem_cons, List.not_mem_nil, or_false] at hin;
          rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
  · have hhelperApart {m : Ram} {a : BitVec 64} {n : Nat}
        (h : Writable code m a n) : RangeApart a n 0x1021ac 240 := by
      have hx := storeOk_of_codeRange h (fun x hx => hcode x (LIR.code_l1021ac x hx))
      have hl : LIR.bytes_l1021ac.length = 240 := by decide +kernel
      rw [hl] at hx
      exact hx.apart
    refine ⟨?_, ?_, ?exec256, ?_, ?_, ?_, ?store256, ?_, ?_, ?_, ?_, ?_⟩
    case exec256 =>
      change LIR.program.runBlock (dialect code) ⟨.l1021ac, args, mem⟩ = _
      cfg_eval []
      runtime_guards call
      rfl
    case store256 =>
      have hmem := authenticationMemory_eq true mem (args[4].get 64) block hblock
      simp only [authenticationWords, authenticationCarry, authenticationHighWord,
        authenticationLowWord, Fin.val_zero, BitVec.add_zero] at hmem
      exact hmem
    all_goals first
      | rfl
      | (intro hTypes; runtime_typed)
      | (rintro ⟨r, hr⟩ hin; simp only [List.mem_cons, List.not_mem_nil, or_false] at hin;
          rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)

end AesGcm.Proofs.Machine.GCM
