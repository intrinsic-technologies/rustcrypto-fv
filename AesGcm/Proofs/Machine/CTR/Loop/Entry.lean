import AesGcm.Proofs.Machine.CTR.Loop.Algebra
import AesGcm.Proofs.Machine.CTR.Loop.RoundKey

namespace AesGcm.Proofs.Machine.CTR.Loop

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift
  X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime
open AesGcm.Proofs.Machine.Fixslice
open AesGcm.Proofs.Machine.AESCore
open AesGcm.Proofs.Machine.KeySchedule
open Standards.NIST.AES

theorem batch_cipher_entry
    (use256 : Bool) (code : CodeMap) (fr : Activation)
    (args : Values Value Reg.count) (mem : Ram)
    (key : Vector UInt8 ((AES16.variant use256).keyBytes))
    (blocks : Fixslice.Blocks) (sp : BitVec 64)
    (scheduleWords : Vector (BitVec 16) (keyWords use256))
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (hTypes : GPRsTyped args)
    (hsp : args[4].get 64 = sp)
    (hStack : Writable code mem (sp - 296) 528)
    (hStackTail : Writable code mem (sp + 72) 264)
    (hKeyRead : Readable mem (sp + 344) (if use256 then 960 else 704))
    (hKeys : WordsAt mem (sp + 344) 64 (scheduleWords.map Fixslice16.widenWord))
    (hBlocks : WordsAt mem (sp + 8) 64 (Vector.ofFn (Fixslice.encode blocks)))
    (hSchedule : ∀ i : Fin (keyWords use256), scheduleWords[i.val] =
      (narrowScheduleWords (AES16.variant use256) key)[i.val]'(by cases use256 <;> exact i.isLt))
    (hdf : args[22] = ⟨1, 0⟩)
    (hx87 : args[39] = ⟨32, (args[39]).get 32⟩ ∧
      args[50] = ⟨16, (args[50]).get 16⟩ ∧
      args[51] = ⟨16, (args[51]).get 16⟩)
    (halign : sp.toNat % 16 = 0)
    (hslot0Readable : Readable mem 0x201208 8)
    (hslot0Value : memLoad mem 0x201208 64 = 0x103f00)
    (hslot1Readable : Readable mem 0x201210 8)
    (hslot1Value : memLoad mem 0x201210 64 = 0x103880)
    (hslot2Readable : Readable mem 0x201230 8)
    (hslot2Value : memLoad mem 0x201230 64 = 0x101230)
    (hslotsApart : (if use256 then 0x2013b0 else 0x2013a0) ≤ sp.toNat ∨
      sp.toNat + 232 ≤ 0x201208) :
    ∃ loc : LIR.lifted.Location,
      (LIR.program.sem (dialect code)).Reaches
        ⟨⟨if use256 then .l108fa2 else .l107b12, args, mem⟩, []⟩ ⟨loc, []⟩ ∧
      CipherWorkingState use256 code fr args mem sp scheduleWords loc ∧
      CipherLoopState use256 key blocks fr sp 0 (by omega) loc := by
  let planes : Planes := Fixslice.encode blocks
  let firstRound : Fin ((AES16.variant use256).Nr + 1) := ⟨0, by omega⟩
  let firstKeys : Planes := KeySchedule.expectedKey (AES16.variant use256) key firstRound
  have hLow := hStack.readable.low
  have hBase : (sp - 296).toNat + 296 = sp.toNat := by bv_omega
  have h8 : (sp + 8).toNat = sp.toNat + 8 := by bv_omega
  have h64 : (sp + 64).toNat = sp.toNat + 64 := by bv_omega
  have h224 : (sp + 224).toNat = sp.toNat + 224 := by bv_omega
  have h344 : (sp + 344).toNat = sp.toNat + 344 := by bv_omega
  have hStack0 : Writable code mem (sp + 8) 64 := hStack.sub (by omega) (by omega)
  have ⟨hKeyRead0, hKeys0⟩ := round_key_slice use256 mem sp key scheduleWords
    hSchedule hKeyRead hKeys firstRound
  simp only [firstRound, Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.add_zero] at hKeyRead0 hKeys0
  obtain ⟨mid, hrun, hlabel, hindex, htail, hwords, hkeep, hmidTypes, hframe⟩ :=
    batch_key0 use256 code hcode args mem sp planes firstKeys
      hTypes hsp hStack0 hKeyRead0 hBlocks hKeys0
  have hstep : LIR.program.step (dialect code)
      ⟨⟨if use256 then .l108fa2 else .l107b12, args, mem⟩, []⟩ =
      .next ⟨mid, []⟩ := by
    rw [Program.step, hrun]
    rfl
  have hmidSp : mid.arguments[4]'(by change 4 < 53; decide) = ⟨64, sp⟩ := by
    have hspArg := hTypes.value 4
    change args[4] = ⟨64, args[4].get 64⟩ at hspArg
    rw [hsp] at hspArg
    exact (hkeep 4 (by decide)).trans hspArg
  have hOutsideAfter (a : BitVec 64) (n : Nat)
      (hlow : a.toNat + n ≤ 2 ^ 64) (hafter : sp.toNat + 64 ≤ a.toNat) :
      Outside [span (sp + 8) 56] a n := by
    refine ⟨hlow, fun r hr => Or.inr ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    change (sp + 8).toNat + 56 ≤ a.toNat
    omega
  have hOutsideSlot (a : BitVec 64) (hlo : 0x201208 ≤ a.toNat) (hhi : a.toNat ≤ 0x201230) :
      Outside [span (sp + 8) 56] a 8 := by
    refine ⟨by omega, fun r hr => ?_⟩
    obtain rfl := List.mem_singleton.mp hr
    change a.toNat + 8 ≤ (sp + 8).toNat ∨ (sp + 8).toNat + 56 ≤ a.toNat
    cases use256 <;> simp only [Bool.false_eq_true, ↓reduceIte] at hslotsApart <;> omega
  have hOutsideKeys : Outside [span (sp + 8) 56] (sp + 344) (64 / 8 * keyWords use256) := by
    have hKeyLow := hKeyRead.low
    apply hOutsideAfter
    · cases use256 <;> simp only [keyWords, Bool.false_eq_true, ↓reduceIte] at hKeyLow ⊢ <;> omega
    · omega
  have hkeep39 : mid.arguments[39]'(by change 39 < 53; decide) = args[39] :=
    hkeep 39 (by decide)
  have hkeep50 : mid.arguments[50]'(by change 50 < 53; decide) = args[50] :=
    hkeep 50 (by decide)
  have hkeep51 : mid.arguments[51]'(by change 51 < 53; decide) = args[51] :=
    hkeep 51 (by decide)
  have hwork : CipherWorkingState use256 code fr args mem sp scheduleWords mid :=
    { regFrame := fun r hr => hkeep r (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr ⊢
        exact Or.inr (Or.inr (Or.inr hr)))
      typed := hmidTypes
      df := (hkeep 22 (by decide)).trans hdf
      x87 := by rw [hkeep39, hkeep50, hkeep51]; exact hx87
      aligned := halign
      stackPointer := hmidSp
      countWord := hframe.memLoad_eq (hOutsideAfter (sp + 224) 8 (by omega) (by omega))
      stack := hStack.of_frame hframe
      stackTail := hStackTail.of_frame hframe
      keyRead := hKeyRead.of_frame hframe
      keys := hKeys.of_frame hframe (by decide) hOutsideKeys
      slot0Readable := hslot0Readable.of_frame hframe
      slot0Value := (hframe.memLoad_eq (hOutsideSlot _ (by decide) (by decide))).trans hslot0Value
      slot1Readable := hslot1Readable.of_frame hframe
      slot1Value := (hframe.memLoad_eq (hOutsideSlot _ (by decide) (by decide))).trans hslot1Value
      slot2Readable := hslot2Readable.of_frame hframe
      slot2Value := (hframe.memLoad_eq (hOutsideSlot _ (by decide) (by decide))).trans hslot2Value
      slotsApart := hslotsApart
      written := (RamWriteFrame.refl mem _).trans hframe (by
        intro r hr
        obtain rfl := List.mem_singleton.mp hr
        refine ⟨span (sp - 296) 512, List.mem_cons_self, ?_, ?_⟩ <;>
          simp only [span] <;> omega) }
  have hround : batchRoundState use256 key blocks 0 = xorPlanes planes firstKeys := by
    simpa only [batchRoundState, planes, firstKeys, firstRound, encodeStandard,
      fromStandard_toStandard] using
      (encryptInitial_expectedKey (AES16.variant use256) key (toStandard blocks)).symm
  have hdelayed : batchDelayedPlanes use256 key blocks 0 =
      (fun p : Fin 8 => if p.val = 7 then planes p else xorPlanes planes firstKeys p) := by
    simp only [batchDelayedPlanes, Nat.zero_min, hround]
    exact batchDelayed_xor planes firstKeys
  have hwordsLoop : WordsAt mid.store (sp + 8) 64
      (Vector.ofFn (batchDelayedPlanes use256 key blocks 0)) := by
    intro i hi
    rw [Vector.getElem_ofFn, hdelayed]
    by_cases hi7 : i < 7
    · simpa only [Vector.getElem_ofFn, ite_false, show i ≠ 7 by omega] using hwords i hi7
    · obtain rfl : i = 7 := by omega
      have haddr : wordAddr (sp + 8) 64 7 = sp + 64 := by
        simp only [wordAddr, Nat.reduceDiv, Nat.reduceMul, BitVec.add_assoc,
          BitVec.ofNat_eq_ofNat, BitVec.reduceAdd]
      rw [haddr, hframe.memLoad_eq (hOutsideAfter (sp + 64) 8 (by omega) (by omega)), ← haddr]
      exact hBlocks 7 (by decide)
  refine ⟨mid, Semantics.Reaches.single hstep, hwork, ?_⟩
  exact
    { label := hlabel
      index := by simpa only [Nat.mul_zero, Nat.zero_add, BitVec.ofNat_eq_ofNat] using
        (show mid.arguments[5]'(by change 5 < 53; decide) =
          ⟨64, BitVec.ofNat 64 (if use256 then 8 else 0)⟩ by cases use256 <;> exact hindex)
      words := hwordsLoop
      tail := htail.trans (congrFun hdelayed 7).symm }

end AesGcm.Proofs.Machine.CTR.Loop
