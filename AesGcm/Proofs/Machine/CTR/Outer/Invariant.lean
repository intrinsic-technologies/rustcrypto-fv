import AesGcm.Proofs.Machine.Runtime.Atoms
import AesGcm.Proofs.Machine.CTR.GCTR
import AesGcm.Proofs.Machine.CTR.InitialCounter
import AesGcm.Spec.GCM
import AesGcm.Proofs.Machine.LIR.Fn107050.Frame
import AesGcm.Proofs.Machine.LIR.Fn1084e0.Frame
import AesGcm.Proofs.Machine.KeySchedule.Memory
namespace AesGcm.Proofs.Machine.CTR

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime
open AesGcm.Proofs.Machine.Fixslice
open AesGcm.Proofs.Machine.KeySchedule
open Standards.NIST.GCM
open AesGcm.Spec.GCM

def outerStackPointer (fr : Activation) (use256 : Bool) : BitVec 64 :=
  fr.rsp - (if use256 then 2312 else 1800)

def cryptFrameAt (use256 : Bool) (label : LIR.Label) (fr : Activation) : List Atom :=
  if use256 then LIR.Fn1084e0.frameAt label fr else LIR.Fn107050.frameAt label fr

def outerAtoms (use256 : Bool) (fr : Activation)
    (key : Vector UInt8 ((AES16.variant use256).keyBytes)) (input : ByteArray)
    (count : Nat) (schedule counter source destination : BitVec 64) : List Atom :=
  let sp := outerStackPointer fr use256
  [.gpr 2 destination, .gpr 4 (outerStackPointer fr use256), .gpr 9 counter,
   .mem (sp + 232) 64 (BitVec.ofNat 64 (count % 4)),
   .mem (sp + 240) 64 source,
   .mem (sp + 248) 64 counter,
   .mem (sp + 320) 64 (BitVec.ofNat 64 count),
   .mem (sp + 328) 64 (BitVec.ofNat 64 (count / 4)),
   .mem (sp + 336) 64 schedule,
   .mem 0x201208 64 0x103f00,
   .mem 0x201210 64 0x103880,
   .mem 0x201230 64 0x101230,
   .readable 0x201208 8, .readable 0x201210 8, .readable 0x201230 8,
   .readable (sp - 296) 528,
   .writable (sp - 296) 528,
   .writable (sp + 72) 264,
   .readable (sp + 344) (if use256 then 960 else 704),
   .words (sp + 344) 64 ((narrowScheduleWords (AES16.variant use256) key).map
     Fixslice16.widenWord),
   .readable source input.size,
   .writable destination input.size,
   .readable counter 20,
   .writable counter 20,
   .readable schedule (16 * ((AES16.variant use256).Nr + 1)),
   .fact ((if use256 then 0x2013b0 else 0x2013a0) ≤ sp.toNat ∨
     sp.toNat + 232 ≤ 0x201208),
   .fact (∀ region ∈ [span fr.rdi 8, span fr.rsi 32,
       span schedule (16 * ((AES16.variant use256).Nr + 1)), span counter 20,
       span source input.size, span destination input.size],
     (callStack fr).Disjoint region),
   .fact (∀ region ∈ [span fr.rdi 8, span fr.rsi 32,
       span schedule (16 * ((AES16.variant use256).Nr + 1)), span counter 20],
     (span destination input.size).Disjoint region),
   .fact (∀ region ∈ [span fr.rdi 8, span fr.rsi 32,
       span schedule (16 * ((AES16.variant use256).Nr + 1)), span source input.size,
       span destination input.size], (span counter 20).Disjoint region),
   .fact (source = destination ∨
     (span source input.size).Disjoint (span destination input.size)),
   .fact (∀ slot ∈ ([0x201208, 0x201210, 0x201230] : List (BitVec 64)),
     (span destination input.size).Disjoint (span slot 8) ∧
     (span counter 20).Disjoint (span slot 8)),
   .fact ((if use256 then 0x201cb8 else 0x201aa8) ≤ fr.rsp.toNat ∨
      fr.rsp.toNat ≤ 0x201208)]

structure OuterState (use256 : Bool) (code : CodeMap) (fr : Activation)
    (key : Vector UInt8 ((AES16.variant use256).keyBytes)) (input : ByteArray)
    (blockCount : Nat) (schedule counter source destination : BitVec 64)
    (loc : LIR.lifted.Location) : Prop where
  frame : Atom.All code loc.arguments loc.store (cryptFrameAt use256 loc.label fr)
  outer : Atom.All code loc.arguments loc.store
    (outerAtoms use256 fr key input blockCount schedule counter source destination)
  written : RamWriteFrame fr.original loc.store [fr.region, span (counter + 16) 4, span destination input.size]
  typed : GPRsTyped loc.arguments
  schedule_in : AES16.ScheduleIn (AES16.variant use256) key schedule loc.store
  schedule_read : Readable loc.store schedule (16 * ((AES16.variant use256).Nr + 1))

structure OuterInvariant (use256 : Bool) (code : CodeMap) (fr : Activation)
    (key : Vector UInt8 ((AES16.variant use256).keyBytes)) (input : ByteArray)
    (batches c : Nat) (schedule counter source destination : BitVec 64)
    (loc : LIR.lifted.Location) extends
    OuterState use256 code fr key input (input.size / 16) schedule counter source destination loc where
  label : loc.label = (if use256 then .l108e98 else .l107a08)
  count_lt : c < batches
  destination_slot : memLoad loc.store (outerStackPointer fr use256 + 216) 64 = destination
  count_word : memLoad loc.store (outerStackPointer fr use256 + 224) 64 = BitVec.ofNat 64 c
  counter_value : memLoad loc.store (counter + 16) 32 =
    memLoad fr.original (counter + 16) 32 + BitVec.ofNat 32 (4 * c)
  source_bytes :
    (span (source + BitVec.ofNat 64 (64 * c)) (input.size - 64 * c)).HasBytes
      loc.store (input.extract (64 * c) input.size)
  prefix_bytes :
    (span destination (64 * c)).HasBytes loc.store
      ((byteArrayOfBits (GCTR (AesGcm.Spec.GCM.forwardCipher (AES16.variant use256) key)
        (bitsOfBytes (initialCounterBlock fr.original counter))
        (bitsOfByteArray input))).extract 0 (64 * c))

structure OuterExit (use256 : Bool) (code : CodeMap) (fr : Activation)
    (key : Vector UInt8 ((AES16.variant use256).keyBytes)) (input : ByteArray)
    (blockCount : Nat) (schedule counter source destination : BitVec 64)
    (loc : LIR.lifted.Location) extends
    OuterState use256 code fr key input blockCount schedule counter source destination loc where
  label : loc.label = (if use256 then .l109509 else .l10805f)
  counter_value : memLoad loc.store (counter + 16) 32 =
    memLoad fr.original (counter + 16) 32 + BitVec.ofNat 32 (4 * (blockCount / 4))
  source_bytes :
    (span (source + BitVec.ofNat 64 (input.size - input.size % 64))
      (input.size % 64)).HasBytes loc.store
      (input.extract (input.size - input.size % 64) input.size)
  destination_prefix :
    (span destination (input.size - input.size % 64)).HasBytes loc.store
      ((byteArrayOfBits (GCTR (AesGcm.Spec.GCM.forwardCipher (AES16.variant use256) key)
        (bitsOfBytes (initialCounterBlock fr.original counter))
        (bitsOfByteArray input))).extract 0 (input.size - input.size % 64))

namespace OuterState

variable {use256 : Bool} {code : CodeMap} {fr : Activation}
    {key : Vector UInt8 ((AES16.variant use256).keyBytes)} {input : ByteArray}
    {count : Nat} {schedule counterPtr source destinationPtr : BitVec 64} {loc : LIR.lifted.Location}

theorem stackPointer
    (h : OuterState use256 code fr key input count schedule counterPtr source destinationPtr loc) :
    loc.arguments[4]'(by change 4 < 53; decide) = ⟨64, outerStackPointer fr use256⟩ :=
  atomsAll_mem (atom := .gpr 4 (outerStackPointer fr use256)) h.outer (by simp only [outerAtoms, List.mem_cons, true_or, or_true])

theorem destination
    (h : OuterState use256 code fr key input count schedule counterPtr source destinationPtr loc) :
    loc.arguments[2]'(by change 2 < 53; decide) = ⟨64, destinationPtr⟩ :=
  atomsAll_mem (atom := .gpr 2 destinationPtr) h.outer (by simp only [outerAtoms, List.mem_cons, true_or])

theorem counter
    (h : OuterState use256 code fr key input count schedule counterPtr source destinationPtr loc) :
    loc.arguments[9]'(by change 9 < 53; decide) = ⟨64, counterPtr⟩ :=
  atomsAll_mem (atom := .gpr 9 counterPtr) h.outer (by simp only [outerAtoms, List.mem_cons, true_or, or_true])

theorem source_word
    (h : OuterState use256 code fr key input count schedule counterPtr source destinationPtr loc) :
    memLoad loc.store (outerStackPointer fr use256 + 240) 64 = source :=
  atomsAll_mem (atom := .mem (outerStackPointer fr use256 + 240) 64 source) h.outer (by simp only [outerAtoms, List.mem_cons, true_or, or_true])

theorem schedule_word
    (h : OuterState use256 code fr key input count schedule counterPtr source destinationPtr loc) :
    memLoad loc.store (outerStackPointer fr use256 + 336) 64 = schedule :=
  atomsAll_mem (atom := .mem (outerStackPointer fr use256 + 336) 64 schedule) h.outer (by simp only [outerAtoms, List.mem_cons, true_or, or_true])

theorem counter_write
    (h : OuterState use256 code fr key input count schedule counterPtr source destinationPtr loc) :
    Writable code loc.store counterPtr 20 :=
  atomsAll_mem (atom := .writable counterPtr 20) h.outer (by simp only [outerAtoms, List.mem_cons, true_or, or_true])

theorem source_read
    (h : OuterState use256 code fr key input count schedule counterPtr source destinationPtr loc) :
    Readable loc.store source input.size :=
  atomsAll_mem (atom := .readable source input.size) h.outer (by simp only [outerAtoms, List.mem_cons, true_or, or_true])

theorem destination_write
    (h : OuterState use256 code fr key input count schedule counterPtr source destinationPtr loc) :
    Writable code loc.store destinationPtr input.size :=
  atomsAll_mem (atom := .writable destinationPtr input.size) h.outer (by simp only [outerAtoms, List.mem_cons, true_or, or_true])

theorem stack
    (h : OuterState use256 code fr key input count schedule counterPtr source destinationPtr loc) :
    Writable code loc.store (outerStackPointer fr use256 - 296) 528 :=
  atomsAll_mem (atom := .writable (outerStackPointer fr use256 - 296) 528) h.outer (by simp only [outerAtoms, List.mem_cons, true_or, or_true])

theorem stack_tail
    (h : OuterState use256 code fr key input count schedule counterPtr source destinationPtr loc) :
    Writable code loc.store (outerStackPointer fr use256 + 72) 264 :=
  atomsAll_mem (atom := .writable (outerStackPointer fr use256 + 72) 264) h.outer (by simp only [outerAtoms, List.mem_cons, true_or, or_true])

theorem key_read
    (h : OuterState use256 code fr key input count schedule counterPtr source destinationPtr loc) :
    Readable loc.store (outerStackPointer fr use256 + 344) (if use256 then 960 else 704) :=
  atomsAll_mem (atom := .readable (outerStackPointer fr use256 + 344) (if use256 then 960 else 704)) h.outer (by simp only [outerAtoms, List.mem_cons, true_or, or_true])

theorem slot0_readable
    (h : OuterState use256 code fr key input count schedule counterPtr source destinationPtr loc) :
    Readable loc.store 0x201208 8 :=
  atomsAll_mem (atom := .readable 0x201208 8) h.outer (by simp only [outerAtoms, List.mem_cons, true_or, or_true])

theorem slot0_value
    (h : OuterState use256 code fr key input count schedule counterPtr source destinationPtr loc) :
    memLoad loc.store 0x201208 64 = 0x103f00 :=
  atomsAll_mem (atom := .mem 0x201208 64 0x103f00) h.outer (by simp only [outerAtoms, List.mem_cons, true_or, or_true])

theorem slot1_readable
    (h : OuterState use256 code fr key input count schedule counterPtr source destinationPtr loc) :
    Readable loc.store 0x201210 8 :=
  atomsAll_mem (atom := .readable 0x201210 8) h.outer (by simp only [outerAtoms, List.mem_cons, true_or, or_true])

theorem slot1_value
    (h : OuterState use256 code fr key input count schedule counterPtr source destinationPtr loc) :
    memLoad loc.store 0x201210 64 = 0x103880 :=
  atomsAll_mem (atom := .mem 0x201210 64 0x103880) h.outer (by simp only [outerAtoms, List.mem_cons, true_or, or_true])

theorem slot2_readable
    (h : OuterState use256 code fr key input count schedule counterPtr source destinationPtr loc) :
    Readable loc.store 0x201230 8 :=
  atomsAll_mem (atom := .readable 0x201230 8) h.outer (by simp only [outerAtoms, List.mem_cons, true_or, or_true])

theorem slot2_value
    (h : OuterState use256 code fr key input count schedule counterPtr source destinationPtr loc) :
    memLoad loc.store 0x201230 64 = 0x101230 :=
  atomsAll_mem (atom := .mem 0x201230 64 0x101230) h.outer (by simp only [outerAtoms, List.mem_cons, true_or, or_true])

end OuterState

end AesGcm.Proofs.Machine.CTR
