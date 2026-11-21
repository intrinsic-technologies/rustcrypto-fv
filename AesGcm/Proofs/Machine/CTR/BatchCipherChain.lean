import AesGcm.Proofs.Machine.CTR.Loop.Entry
import AesGcm.Proofs.Machine.CTR.Loop.Iteration
import AesGcm.Proofs.Machine.CTR.Loop.Finish

namespace AesGcm.Proofs.Machine.CTR

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift
  X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime
open AesGcm.Proofs.Machine.Fixslice
open AesGcm.Proofs.Machine.AESCore
open AesGcm.Proofs.Machine.KeySchedule
open Standards.NIST.AES

def batchCipherStart (use256 : Bool) : LIR.Label :=
  if use256 then .l108fa2 else .l107b12

def batchCipherResume (use256 : Bool) : LIR.Label :=
  if use256 then .l1087a5 else .l107315

set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
theorem batch_cipher_call
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
    (hSchedule : ∀ i : Fin (keyWords use256),
      scheduleWords[i.val] = (narrowScheduleWords (AES16.variant use256) key)[i.val]'(by cases use256 <;> exact i.isLt))
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
    ∃ next : LIR.lifted.Location,
      (LIR.program.sem (dialect code)).Reaches
        ⟨⟨batchCipherStart use256, args, mem⟩, []⟩ ⟨next, []⟩ ∧
      next.label = batchCipherResume use256 ∧
      Fixslice.memoryBlocks next.store (sp + 152) =
        Fixslice.fromStandard (fun b =>
          Standards.NIST.AES.cipher (AES16.variant use256) key
            (Fixslice.toStandard blocks b)) ∧
      next.arguments[4]'(by change 4 < 53; decide) = ⟨64, sp⟩ ∧
      next.arguments[5]'(by change 5 < 53; decide) =
        ⟨64, memLoad next.store (sp + 224) 64 <<< 6⟩ ∧
      memLoad next.store (sp + 224) 64 = memLoad mem (sp + 224) 64 ∧
      GPRsTyped next.arguments ∧
      (∀ r : Fin 53, r.val ∈ [22,39,50,51] →
        next.arguments[r.val]'r.isLt = args[r.val]'r.isLt) ∧
      RamWriteFrame mem next.store
        [span (sp - 296) 512, span (sp + 224) 8] := by
  obtain ⟨loc0, hEntry, hWork0, hLoop0⟩ :=
    Loop.batch_cipher_entry use256 code fr args mem key blocks sp scheduleWords
      hcode hTypes hsp hStack hStackTail hKeyRead hKeys hBlocks hSchedule hdf hx87
      halign hslot0Readable hslot0Value hslot1Readable hslot1Value hslot2Readable
      hslot2Value hslotsApart
  have hStep := fun (j : Nat) (hj : 4 * j < (AES16.variant use256).Nr + 1)
      (hjlast : j ≤ batchLastIteration use256) (loc : LIR.lifted.Location)
      (hwork : CipherWorkingState use256 code fr args mem sp scheduleWords loc)
      (hloop : CipherLoopState use256 key blocks fr sp j hj loc) =>
    Loop.batch_cipher_step use256 code fr args mem key blocks sp scheduleWords hcode hSchedule
      hBlocks j hj hjlast loc hwork hloop
  obtain ⟨locf, hRounds, hWorkF, hFinal⟩ :=
    batch_cipher_rounds use256 code fr args mem key blocks sp scheduleWords hStep loc0 hWork0 hLoop0
  let count : BitVec 64 := memLoad mem (sp + 224) 64
  obtain ⟨next, hFinish, hNextLabel, hKeystream, hNext4, hNext5, hNextCount,
      hNextTypes, hNextRegs, hFrame⟩ :=
    Loop.batch_cipher_finish use256 code fr args mem key blocks sp scheduleWords hcode hSchedule
      count locf hWorkF hFinal hWorkF.countWord
  exact ⟨next, hEntry.trans (hRounds.trans hFinish), hNextLabel, hKeystream,
    hNext4, hNext5, hNextCount, hNextTypes, hNextRegs, hFrame⟩

end AesGcm.Proofs.Machine.CTR
