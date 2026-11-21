import AesGcm.Proofs.Machine.CTR.Outer.Frame
import AesGcm.Proofs.Machine.CTR.BatchInput
import AesGcm.Proofs.Machine.CTR.BatchCipherChain
import AesGcm.Proofs.Machine.CTR.BatchCipher
import AesGcm.Proofs.Machine.CTR.Outer.Advance
namespace AesGcm.Proofs.Machine.CTR
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime
open AesGcm.Proofs.Machine.KeySchedule
open Standards.NIST.GCM AesGcm.Spec.GCM
def outerBatchHead (use256 : Bool) : LIR.Label := if use256 then .l108e98 else .l107a08
def outerBatchExit (use256 : Bool) : LIR.Label := if use256 then .l109509 else .l10805f
set_option maxHeartbeats 800000 in
theorem batch_step (use256 : Bool) (code : CodeMap) (fr : Activation)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (key : Vector UInt8 ((AES16.variant use256).keyBytes)) (input : ByteArray)
    (batches c blockCount : Nat) (hsize : input.size = 16 * blockCount)
    (hbatches : batches = blockCount / 4) (schedule counter source destination : BitVec 64)
    (loc : LIR.lifted.Location)
    (hInv : OuterInvariant use256 code fr key input batches c schedule counter source destination loc)
    (hBatch : c + 1 ≤ batches) :
    ∃ next : LIR.lifted.Location,
      (LIR.program.sem (dialect code)).Reaches ⟨loc, []⟩ ⟨next, []⟩ ∧
      ((c + 1 < batches ∧ OuterInvariant use256 code fr key input batches (c + 1) schedule counter source destination next) ∨
       (c + 1 = batches ∧ OuterExit use256 code fr key input blockCount schedule counter source destination next)) := by
  let sp := outerStackPointer fr use256
  let off := BitVec.ofNat 64 (64 * c)
  have state := hInv.toOuterState
  obtain ⟨lo, hi, top, _⟩ := hInv.batch_stack_bounds
  change fr.low.toNat + 296 ≤ sp.toNat at lo
  change sp.toNat + 1800 ≤ fr.rsp.toNat at hi
  have sc := hInv.batch_stack_apart counter 20 (by decide) (by simp)
  have size : 64 * (c + 1) ≤ input.size := by omega
  have srcApart := hInv.batch_stack_apart source input.size (by omega) (by simp)
  have dstApart := hInv.batch_stack_apart destination input.size (by omega) (by simp)
  have addr (a : BitVec 64) (n : Nat) (hn : a.toNat + n ≤ 2^32) :
      (a + BitVec.ofNat 64 n).toNat = a.toNat + n := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := n) (by omega),
      Nat.mod_eq_of_lt (by omega)]
  have plus (n : Nat) (hn : n ≤ 1800) :
      (sp + BitVec.ofNat 64 n).toNat = sp.toNat + n := addr sp n (by omega)
  have sub80 : (sp - 80).toNat = sp.toNat - 80 := BitVec.toNat_sub_of_le (by change 80 ≤ sp.toNat; omega)
  have sub296 : (sp - 296).toNat = sp.toNat - 296 := BitVec.toNat_sub_of_le (by change 296 ≤ sp.toNat; omega)
  have ctrLow := state.counter_write.readable.low
  have srcLow := state.source_read.low
  have dstLow := state.destination_write.readable.low
  have ctr16 : (counter + 16).toNat = counter.toNat + 16 := addr counter 16 (by omega)
  have srcOff : (source + off).toNat = source.toNat + 64 * c := addr source _ (by omega)
  have dstOff : (destination + off).toNat = destination.toNat + 64 * c := addr destination _ (by omega)
  have p8 : (sp + 8).toNat = sp.toNat + 8 := plus 8 (by decide)
  have p72 : (sp + 72).toNat = sp.toNat + 72 := plus 72 (by decide)
  have p224 : (sp + 224).toNat = sp.toNat + 224 := plus 224 (by decide)
  have p256 : (sp + 256).toNat = sp.toNat + 256 := plus 256 (by decide)
  have hf := hInv.frame
  rw [hInv.label] at hf
  let window := if use256 then 2688 else 2160
  let baseOff := if use256 then 2312 else 1800
  let live := [Atom.reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
    .reg 51 ⟨16, fr.fcw⟩, .fact (fr.rsp.toNat % 16 = 8),
    .fact (fr.low.toNat + window ≤ fr.rsp.toNat),
    .writable (fr.rsp - BitVec.ofNat 64 window) window]
  have fixed (atom : Atom) (ha : atom ∈ live) : atom.Holds code loc.arguments loc.store :=
    atomsAll_mem hf (by
      cases use256 <;> simp only [live, window, cryptFrameAt, LIR.Fn107050.frameAt,
        LIR.Fn107050.frameAtG6, LIR.Fn1084e0.frameAt, LIR.Fn1084e0.frameAtG6,
        Bool.false_eq_true, ↓reduceIte, List.mem_cons, List.not_mem_nil, or_false] at ha ⊢ <;> grind only)
  have df : loc.arguments[22]'(by change 22 < 53; decide) = ⟨1,0⟩ := fixed (.reg 22 ⟨1,0⟩) (by simp [live])
  have mx : loc.arguments[39]'(by change 39 < 53; decide) = ⟨32,fr.mxcsr⟩ := fixed (.reg 39 ⟨32,fr.mxcsr⟩) (by simp [live])
  have ft : loc.arguments[50]'(by change 50 < 53; decide) = ⟨16,fr.ftw⟩ := fixed (.reg 50 ⟨16,fr.ftw⟩) (by simp [live])
  have fc : loc.arguments[51]'(by change 51 < 53; decide) = ⟨16,fr.fcw⟩ := fixed (.reg 51 ⟨16,fr.fcw⟩) (by simp [live])
  have align0 : fr.rsp.toNat % 16 = 8 := fixed (.fact _) (by simp [live])
  have room : fr.low.toNat + window ≤ fr.rsp.toNat := fixed (.fact _) (by simp [live])
  have stack : Writable code loc.store (fr.rsp - BitVec.ofNat 64 window) window :=
    fixed (.writable _ _) (by simp [live])
  have offsetRoom : baseOff + 80 ≤ window := by cases use256 <;> decide
  have baseEq : sp = fr.rsp - BitVec.ofNat 64 baseOff := by cases use256 <;> rfl
  have spNat : sp.toNat = fr.rsp.toNat - baseOff := by
    rw [baseEq, stack_sub_toNat fr room (by omega)]
  have winNat := stack_sub_toNat fr room (Nat.le_refl window)
  have depthAlign : baseOff % 16 = 8 := by cases use256 <;> decide
  have align : sp.toNat % 16 = 0 := by omega
  have inputStack : Writable code loc.store (sp - 80) 400 :=
    stack.sub (by omega) (by omega)
  obtain ⟨mid, first, midLabel, midTypes, keep, words, newCounter, frame1⟩ :=
    batch_input_reaches use256 code hcode loc.arguments loc.store sp counter hInv.typed
      (congrArg (Value.get 64) state.stackPointer) (congrArg (Value.get 64) state.counter)
      (by omega) align inputStack state.counter_write (by omega)
      df (by rw [mx]; rfl) (by rw [ft]; rfl) (by rw [fc]; rfl)
  let regions1 := [span (sp - 80) 80, span (sp + 8) 64, span (sp + 256) 64, span (counter + 16) 4]
  have local1 (k n : Nat) (hk : 72 ≤ k ∧ k + n ≤ 1800 ∧ (k + n ≤ 256 ∨ 320 ≤ k)) :
      Outside regions1 (sp + BitVec.ofNat 64 k) n := by
    simp only [regions1, Outside, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
      and_true, span, plus k (by omega), sub80, p8, p256, ctr16]
    omega
  have local2 (k : Nat) (hk : 216 ≤ k ∧ k + 8 ≤ 1800 ∧ (k + 8 ≤ 224 ∨ 232 ≤ k)) :
      Outside [span (sp - 296) 512, span (sp + 224) 8] (sp + BitVec.ofNat 64 k) 8 := by
    simp only [Outside, List.forall_mem_cons, List.not_mem_nil, false_implies, implies_true,
      and_true, span, plus k (by omega), sub296, p224]
    omega
  obtain ⟨_, slotsOutside, _⟩ := hInv.batch_outside hsize hbatches
  have slot1 (a : BitVec 64) (ha : a ∈ ([0x201208,0x201210,0x201230] : List (BitVec 64))) :
      Outside regions1 a 8 := by
    have h := slotsOutside a ha
    change Outside (batchWriteRegions sp counter destination c) a 8 at h
    simp only [regions1, batchWriteRegions, Outside, List.forall_mem_cons, List.not_mem_nil,
      false_implies, implies_true, and_true, span] at h ⊢
    omega
  let ks := narrowScheduleWords (AES16.variant use256) key
  have ksize : 8 * ((AES16.variant use256).Nr + 1) = keyWords use256 := by cases use256 <;> rfl
  have kmax : 64 / 8 * (8 * ((AES16.variant use256).Nr + 1)) ≤ 960 := by cases use256 <;> decide
  have keys : WordsAt loc.store (sp + 344) 64 (ks.map Fixslice16.widenWord) :=
    atomsAll_mem (atom := .words _ _ _) hInv.outer (by simp [outerAtoms, sp, ks])
  have midKeys := keys.of_frame frame1 (by decide) (local1 344 _ (by omega))
  have keysCast : WordsAt mid.store (sp + 344) 64 ((ks.cast ksize).map Fixslice16.widenWord) := by
    intro i hi
    exact midKeys i (by omega)
  have midBlocks : WordsAt mid.store (sp + 8) 64 (Vector.ofFn (Fixslice.encode (counterBlocks loc.store counter))) := by
    intro i hi
    simpa only [wordAddr, Nat.reduceDiv, Vector.getElem_ofFn] using words ⟨i,hi⟩
  obtain ⟨cipher, second, cipherLabel, stream, cipher4, cipher5, cipherCount, cipherTypes,
      cipherRegs, frame2⟩ :=
    batch_cipher_call use256 code fr mid.arguments mid.store key (counterBlocks loc.store counter)
      sp (ks.cast ksize) hcode midTypes (congrArg (Value.get 64) ((keep 4 (by decide)).trans state.stackPointer))
      (state.stack.of_frame frame1) (state.stack_tail.of_frame frame1) (state.key_read.of_frame frame1)
      keysCast midBlocks (fun _ => rfl) ((keep 22 (by decide)).trans df)
      ⟨by rw [show mid.arguments[39]'(by change 39 < 53; decide) = ⟨32,fr.mxcsr⟩ from (keep 39 (by decide)).trans mx]; rfl,
       by rw [show mid.arguments[50]'(by change 50 < 53; decide) = ⟨16,fr.ftw⟩ from (keep 50 (by decide)).trans ft]; rfl,
       by rw [show mid.arguments[51]'(by change 51 < 53; decide) = ⟨16,fr.fcw⟩ from (keep 51 (by decide)).trans fc]; rfl⟩ align
      (state.slot0_readable.of_frame frame1) ((frame1.memLoad_eq (slot1 _ (by decide))).trans state.slot0_value)
      (state.slot1_readable.of_frame frame1) ((frame1.memLoad_eq (slot1 _ (by decide))).trans state.slot1_value)
      (state.slot2_readable.of_frame frame1) ((frame1.memLoad_eq (slot1 _ (by decide))).trans state.slot2_value)
      (atomsAll_mem (atom := .fact _) hInv.outer (by simp [outerAtoms, sp]))
  have localLoad (k : Nat) (hk : 216 ≤ k ∧ k + 8 ≤ 1800 ∧
      (k + 8 ≤ 224 ∨ 232 ≤ k) ∧ (k + 8 ≤ 256 ∨ 320 ≤ k)) :
      memLoad cipher.store (sp + BitVec.ofNat 64 k) 64 = memLoad loc.store (sp + BitVec.ofNat 64 k) 64 :=
    (frame2.memLoad_eq (local2 k (by omega))).trans (frame1.memLoad_eq (local1 k 8 (by omega)))
  have countWord := cipherCount.trans ((frame1.memLoad_eq (local1 224 8 (by decide))).trans hInv.count_word)
  have offsetEq : BitVec.ofNat 64 c <<< 6 = off := by
    change BitVec.ofNat 64 c <<< 6 = BitVec.ofNat 64 (64 * c)
    rw [BitVec.shiftLeft_eq_mul_twoPow]
    change BitVec.ofNat 64 c * BitVec.ofNat 64 64 = BitVec.ofNat 64 (64 * c)
    rw [← BitVec.ofNat_mul, Nat.mul_comm]
  have batchesWord : memLoad loc.store (sp + 328) 64 = BitVec.ofNat 64 batches := by
    have e : input.size / 16 / 4 = batches := by omega
    rw [← e]
    exact atomsAll_mem (atom := .mem _ 64 _) hInv.outer (by simp [outerAtoms, sp])
  have counterWord : memLoad loc.store (sp + 248) 64 = counter :=
    atomsAll_mem (atom := .mem _ 64 _) hInv.outer (by simp [outerAtoms, sp])
  have srcRead : Readable cipher.store (source + off) 64 :=
    ((state.source_read.sub (by omega) (by omega)).of_frame frame1).of_frame frame2
  have dstWrite : Writable code cipher.store (destination + off) 64 :=
    ((state.destination_write.sub (by omega) (by omega)).of_frame frame1).of_frame frame2
  obtain ⟨next, run, nextLabel, _, next2, next9, nextCount, xorWords, xorRegs, nextTypes, frame3⟩ :=
    batch_xor use256 code hcode cipher.arguments cipher.store sp source destination off
      (BitVec.ofNat 64 c) (BitVec.ofNat 64 batches) counter cipherTypes (congrArg (Value.get 64) cipher4)
      ((congrArg (Value.get 64) cipher5).trans (by rw [countWord]; exact offsetEq))
      ((state.stack_tail.of_frame frame1).of_frame frame2) srcRead dstWrite (by rw [p72]; omega) (by rw [p72]; omega)
      ((localLoad 240 (by decide)).trans state.source_word)
      ((localLoad 216 (by decide)).trans hInv.destination_slot) countWord
      ((localLoad 328 (by decide)).trans batchesWord) ((localLoad 248 (by decide)).trans counterWord)
  have first' : (LIR.program.sem (dialect code)).Reaches ⟨loc, []⟩ ⟨mid, []⟩ := by
    change (LIR.program.sem (dialect code)).Reaches ⟨⟨loc.label, loc.arguments, loc.store⟩, []⟩ _
    rw [hInv.label]
    exact first
  have second' : (LIR.program.sem (dialect code)).Reaches ⟨mid, []⟩ ⟨cipher, []⟩ := by
    change (LIR.program.sem (dialect code)).Reaches ⟨⟨mid.label, mid.arguments, mid.store⟩, []⟩ _
    rw [midLabel]
    exact second
  have finalStep : LIR.program.step (dialect code) ⟨cipher, []⟩ = .next ⟨next, []⟩ := by
    change LIR.program.step (dialect code) ⟨⟨cipher.label, cipher.arguments, cipher.store⟩, []⟩ = _
    rw [cipherLabel, Program.step, batchCipherResume, run]
    rfl
  obtain ⟨writes, sourceAtCipher, counterPreserved, ctrBits⟩ :=
    hInv.batch_memory hsize hbatches frame1 frame2 frame3
  have chunk := batch_payload _ key fr.original loc.store cipher.store next.store sp counter
    source destination input c ctrBits stream sourceAtCipher size (dstWrite.readable.of_frame frame3) xorWords
  have inc : BitVec.ofNat 64 c + 1 = BitVec.ofNat 64 (c + 1) := (BitVec.ofNat_add ..).symm
  have branch : (BitVec.ofNat 64 c + 1 = BitVec.ofNat 64 batches) ↔ c + 1 = batches := by
    rw [inc]
    constructor
    · intro h
      have h' := congrArg BitVec.toNat h
      simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (show c + 1 < 2^64 by omega),
        Nat.mod_eq_of_lt (show batches < 2^64 by omega)] at h'
      exact h'
    · rintro e
      rw [e]
  have label : next.label = (if c + 1 < batches then
      (if use256 then .l108e98 else .l107a08) else (if use256 then .l109509 else .l10805f)) := by
    by_cases done : c + 1 = batches
    · simpa only [ite_eq_left (branch.mpr done), ite_eq_right (show ¬ c + 1 < batches by omega)] using nextLabel
    · simpa only [ite_eq_right (fun e => done (branch.mp e)), ite_eq_left (show c + 1 < batches by omega)] using nextLabel
  refine ⟨next, first'.trans (second'.trans (Semantics.Reaches.single finalStep)), ?_⟩
  apply hInv.advance_batch hsize hbatches label nextTypes writes next2
    ((xorRegs 4 (by decide)).trans cipher4) next9 _ (nextCount.trans inc)
    (counterPreserved.trans newCounter) chunk
  intro r hr
  have mem (xs : List Nat) (h : ∀ i ∈ ([22,39,50,51] : List Nat), i ∈ xs) : r.val ∈ xs := h _ hr
  exact (xorRegs r (mem _ (by decide))).trans ((cipherRegs r hr).trans (keep r (mem _ (by decide))))
end AesGcm.Proofs.Machine.CTR
