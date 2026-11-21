import AesGcm.Proofs.Machine.CTR.BatchKey0
import AesGcm.Proofs.Machine.CTR.BatchHeader
import AesGcm.Proofs.Machine.CTR.KeyLoop
import AesGcm.Proofs.Machine.CTR.BatchKey1
import AesGcm.Proofs.Machine.CTR.BatchInline0
import AesGcm.Proofs.Machine.CTR.BatchInline2
import AesGcm.Proofs.Machine.CTR.BatchKey3
import AesGcm.Proofs.Machine.CTR.BatchMixCall
import AesGcm.Proofs.Machine.CTR.BatchSboxCall
import AesGcm.Proofs.Machine.CTR.FinalRows
import AesGcm.Proofs.Machine.CTR.FinalKey
import AesGcm.Proofs.Machine.AESCore.Rounds
import AesGcm.Proofs.Machine.KeySchedule.Layout
import AesGcm.Proofs.AES16.Layout
import AesGcm.Proofs.Machine.Fixslice16.Widening

namespace AesGcm.Proofs.Machine.CTR

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift
  X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime
open AesGcm.Proofs.Machine.Fixslice
open AesGcm.Proofs.Machine.AESCore
open Standards.NIST.AES

def batchLastIteration (use256 : Bool) : Nat := if use256 then 3 else 2

def batchRoundState (use256 : Bool) (key : Vector UInt8 ((AES16.variant use256).keyBytes))
    (blocks : Fixslice.Blocks) (count : Nat) : Fixslice.Planes :=
  phaseEncode count
    (encryptRounds (cipherKeys (AES16.variant use256) key)
      count (toStandard blocks))

def batchDelayedPlanes (use256 : Bool)
    (key : Vector UInt8 ((AES16.variant use256).keyBytes))
    (blocks : Fixslice.Blocks) (count : Nat) : Fixslice.Planes :=
  let planes := batchRoundState use256 key blocks count
  let round : Fin ((AES16.variant use256).Nr + 1) :=
    ⟨min count (AES16.variant use256).Nr, by omega⟩
  let keys := KeySchedule.expectedKey (AES16.variant use256) key round
  fun p ↦ if p.val = 7 then planes p ^^^ keys p else planes p

structure CipherWorkingState (use256 : Bool) (code : CodeMap) (fr : Activation)
    (args : Values Value Reg.count) (mem : Ram)
    (sp : BitVec 64) (scheduleWords : Vector (BitVec 16) (keyWords use256))
    (loc : LIR.lifted.Location) : Prop where
  regFrame : ∀ r : Fin 53, r.val ∈ [22, 39, 50, 51] →
    loc.arguments[r.val]'r.isLt = args[r.val]'r.isLt
  typed : GPRsTyped loc.arguments
  df : loc.arguments[22]'(by change 22 < 53; decide) = ⟨1, 0⟩
  x87 : loc.arguments[39]'(by change 39 < 53; decide) =
      ⟨32, (loc.arguments[39]'(by change 39 < 53; decide)).get 32⟩ ∧
    loc.arguments[50]'(by change 50 < 53; decide) =
      ⟨16, (loc.arguments[50]'(by change 50 < 53; decide)).get 16⟩ ∧
    loc.arguments[51]'(by change 51 < 53; decide) =
      ⟨16, (loc.arguments[51]'(by change 51 < 53; decide)).get 16⟩
  aligned : sp.toNat % 16 = 0
  stackPointer : loc.arguments[4]'(by change 4 < 53; decide) = ⟨64, sp⟩
  countWord : memLoad loc.store (sp + 224) 64 = memLoad mem (sp + 224) 64
  stack : Writable code loc.store (sp - 296) 528
  stackTail : Writable code loc.store (sp + 72) 264
  keyRead : Readable loc.store (sp + 344) (if use256 then 960 else 704)
  keys : WordsAt loc.store (sp + 344) 64 (scheduleWords.map Fixslice16.widenWord)
  slot0Readable : Readable loc.store 0x201208 8
  slot0Value : memLoad loc.store 0x201208 64 = 0x103f00
  slot1Readable : Readable loc.store 0x201210 8
  slot1Value : memLoad loc.store 0x201210 64 = 0x103880
  slot2Readable : Readable loc.store 0x201230 8
  slot2Value : memLoad loc.store 0x201230 64 = 0x101230
  slotsApart : (if use256 then 0x2013b0 else 0x2013a0) ≤ sp.toNat ∨
    sp.toNat + 232 ≤ 0x201208
  written : RamWriteFrame mem loc.store
    [span (sp - 296) 512, span (sp + 224) 8]

structure CipherLoopState (use256 : Bool)
    (key : Vector UInt8 ((AES16.variant use256).keyBytes))
    (blocks : Fixslice.Blocks) (fr : Activation) (sp : BitVec 64)
    (j : Nat) (hj : 4 * j < (AES16.variant use256).Nr + 1)
    (loc : LIR.lifted.Location) : Prop where
  label : loc.label = (if use256 then .l109010 else .l107b80)
  index : loc.arguments[5]'(by change 5 < 53; decide) =
    ⟨64, BitVec.ofNat 64 (32 * j + (if use256 then 8 else 0))⟩
  words : WordsAt loc.store (sp + 8) 64
    (Vector.ofFn (batchDelayedPlanes use256 key blocks (4 * j)))
  tail : (loc.arguments[if use256 then 15 else 14]'(by
      change (if use256 then 15 else 14) < 53; cases use256 <;> decide)).get 64 =
    batchDelayedPlanes use256 key blocks (4 * j) 7

structure CipherFinalState (use256 : Bool)
    (key : Vector UInt8 ((AES16.variant use256).keyBytes))
    (blocks : Fixslice.Blocks) (fr : Activation) (sp : BitVec 64)
    (loc : LIR.lifted.Location) : Prop where
  label : loc.label = (if use256 then .l108600 else .l107170)
  words : WordsAt loc.store (sp + 8) 64
    (Vector.ofFn (batchRoundState use256 key blocks
      ((AES16.variant use256).Nr - 1)))
  regs : ∀ p : Fin 8,
    (loc.arguments[batchPlaneRegister p]'(by
      change (batchPlaneRegister p).val < 53; exact (batchPlaneRegister p).isLt)).get 64 =
      batchRoundState use256 key blocks ((AES16.variant use256).Nr - 1) p

theorem batch_cipher_rounds
    (use256 : Bool) (code : CodeMap) (fr : Activation)
    (args : Values Value Reg.count) (mem : Ram)
    (key : Vector UInt8 ((AES16.variant use256).keyBytes))
    (blocks : Fixslice.Blocks) (sp : BitVec 64)
    (keyWords : Vector (BitVec 16) (keyWords use256))
    (step : ∀ (j : Nat) (hj : 4 * j < (AES16.variant use256).Nr + 1),
      j ≤ batchLastIteration use256 →
      ∀ (loc : LIR.lifted.Location),
        CipherWorkingState use256 code fr args mem sp keyWords loc →
        CipherLoopState use256 key blocks fr sp j hj loc →
        ∃ next : LIR.lifted.Location,
          (LIR.program.sem (dialect code)).Reaches ⟨loc, []⟩ ⟨next, []⟩ ∧
          CipherWorkingState use256 code fr args mem sp keyWords next ∧
          ((j = batchLastIteration use256 ∧ CipherFinalState use256 key blocks fr sp next) ∨
            (j < batchLastIteration use256 ∧
              ∃ hnext : 4 * (j + 1) < (AES16.variant use256).Nr + 1,
                CipherLoopState use256 key blocks fr sp (j + 1) hnext next)))
    (loc : LIR.lifted.Location)
    (hwork : CipherWorkingState use256 code fr args mem sp keyWords loc)
    (hloop : CipherLoopState use256 key blocks fr sp 0 (by omega) loc) :
    ∃ last : LIR.lifted.Location,
      (LIR.program.sem (dialect code)).Reaches ⟨loc, []⟩ ⟨last, []⟩ ∧
      CipherWorkingState use256 code fr args mem sp keyWords last ∧
      CipherFinalState use256 key blocks fr sp last := by
  have walk : ∀ (fuel j : Nat) (hj : 4 * j < (AES16.variant use256).Nr + 1),
      j ≤ batchLastIteration use256 → j + fuel = batchLastIteration use256 →
      ∀ (loc : LIR.lifted.Location),
        CipherWorkingState use256 code fr args mem sp keyWords loc →
        CipherLoopState use256 key blocks fr sp j hj loc →
        ∃ last : LIR.lifted.Location,
          (LIR.program.sem (dialect code)).Reaches ⟨loc, []⟩ ⟨last, []⟩ ∧
          CipherWorkingState use256 code fr args mem sp keyWords last ∧
          CipherFinalState use256 key blocks fr sp last := by
    intro fuel
    induction fuel with
    | zero =>
      intro j hj hb he loc hw hl
      obtain ⟨next, hr, hn, hs⟩ := step j hj hb loc hw hl
      rcases hs with ⟨_, hf⟩ | ⟨hlt, _⟩
      · exact ⟨next, hr, hn, hf⟩
      · omega
    | succ fuel ih =>
      intro j hj hb he loc hw hl
      obtain ⟨next, hr, hn, hs⟩ := step j hj hb loc hw hl
      rcases hs with ⟨heq, _⟩ | ⟨hlt, hnext, hs⟩
      · omega
      · obtain ⟨last, hrest, hwlast, hlast⟩ :=
          ih (j + 1) hnext (by omega) (by omega) next hn hs
        exact ⟨last, hr.trans hrest, hwlast, hlast⟩
  exact walk (batchLastIteration use256) 0 (by omega) (Nat.zero_le _) (Nat.zero_add _)
    loc hwork hloop

end AesGcm.Proofs.Machine.CTR
