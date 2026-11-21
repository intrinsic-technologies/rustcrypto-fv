import AesGcm.Proofs.Machine.Core.Decrypt.FullBlocksCall
import AesGcm.Proofs.Machine.Core.Decrypt.FullBlocksSuffix
import AesGcm.Proofs.Machine.Core.Decrypt.TailExit
import AesGcm.Proofs.Machine.Core.Decrypt.TailOutput
import AesGcm.Proofs.Machine.Core.Decrypt.Branches

namespace AesGcm.Proofs.Machine.Core.Decrypt

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

set_option maxHeartbeats 1200000 in
set_option maxRecDepth 3072 in
theorem payload_reaches (use256 : Bool) (code : CodeMap) (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (key : Vector UInt8 (AES16.variant use256).keyBytes) (crypt : CTR.CryptCall use256 code key)
    (fr : Activation) (counter : LIR.lifted.Location) (source destination : BitVec 64)
    (ciphertext : ByteArray) (positive : 0 < ciphertext.size)
    (cLabel : counter.label = (if ciphertext.size < 17 then (if use256 then .l1028dc else .l10247c)
      else (if use256 then .l102885 else .l102425)))
    (cFrame : Atom.All code counter.arguments counter.store
      (if use256 then LIR.Fn102720.frameAt counter.label fr else LIR.Fn1022c0.frameAt counter.label fr))
    (cTyped : GPRsTyped counter.arguments)
    (cLength : ((counter.arguments[14]'(by change 14 < 53; decide)).get 64).toNat = ciphertext.size)
    (cSource : (counter.arguments[12]'(by change 12 < 53; decide)).get 64 = source)
    (cMask : (counter.arguments[3]'(by change 3 < 53; decide)).get 64 = 0xfffffffe0)
    (cCounter : (counter.arguments[15]'(by change 15 < 53; decide)).get 64 = fr.rsp - 120)
    (counterKeyValue : memLoad counter.store (fr.rsp - 128) 64 = fr.rdi + 32)
    (counterBuffer : BufferIn counter.store fr.r8 source destination ciphertext)
    (schedule : AES16.ScheduleIn (AES16.variant use256) key (fr.rdi + 32) counter.store)
    (scheduleReadCounter : Readable counter.store (fr.rdi + 32) (16 * ((AES16.variant use256).Nr + 1)))
    (destWriteCounter : Writable code counter.store destination ciphertext.size)
    (descriptorWrite : Writable code counter.store (fr.r8 + 8) 8)
    (hsep : ∀ r ∈ [span (fr.rdi + 32) (16 * ((AES16.variant use256).Nr + 1)), span source ciphertext.size,
      span destination ciphertext.size, span fr.r8 24], (callStack fr).Disjoint r)
    (hdescsep : ∀ r ∈ [span (fr.rdi + 32) (16 * ((AES16.variant use256).Nr + 1)), span source ciphertext.size,
      span destination ciphertext.size], (span fr.r8 24).Disjoint r)
    (destSep : (span destination ciphertext.size).Disjoint
      (span (fr.rdi + 32) (16 * ((AES16.variant use256).Nr + 1))))
    (hslots : ∀ slot ∈ ([0x201208,0x201210,0x201228,0x201230] : List (BitVec 64)),
      (span destination ciphertext.size).Disjoint (span slot 8) ∧ (span fr.r8 24).Disjoint (span slot 8)) :
    ∃ last : LIR.lifted.Location,
      (LIR.program.sem (dialect code)).Reaches ⟨counter, []⟩ ⟨last, []⟩ ∧
      last.label = (if use256 then .l102961 else .l102501) ∧
      Atom.All code last.arguments last.store
        (if use256 then LIR.Fn102720.frameAt .l102961 fr else LIR.Fn1022c0.frameAt .l102501 fr) ∧
      GPRsTyped last.arguments ∧ RamWriteFrame counter.store last.store
        [fr.region, span destination ciphertext.size, span (fr.r8 + 8) 8] ∧
      (last.arguments[0]'(by change 0 < 53; decide)).get 8 =
        (counter.arguments[0]'(by change 0 < 53; decide)).get 8 ∧
      (span destination ciphertext.size).HasBytes last.store (AesGcm.Spec.GCM.byteArrayOfBits
        (Standards.NIST.GCM.GCTR (AesGcm.Spec.GCM.forwardCipher (AES16.variant use256) key)
          (Standards.NIST.GCM.bitsOfBytes (CTR.initialCounterBlock counter.store (fr.rsp - 120)))
          (AesGcm.Spec.GCM.bitsOfByteArray ciphertext))) ∧
      memLoad last.store (fr.r8 + 8) 64 = destination +
        BitVec.ofNat 64 (if 17 ≤ ciphertext.size then 16 * (ciphertext.size / 16) else 0) := by
  have subdisjoint {a b : BitVec 64} {n m n' m' : Nat}
      (hs : (span a n).Disjoint (span b m)) (hn : n' ≤ n) (hm : m' ≤ m) :
      (span a n').Disjoint (span b m') := by
    intro x hx hy
    apply hs x
    · simp only [span,MemoryRegion.Contains] at hx ⊢
      omega
    · simp only [span,MemoryRegion.Contains] at hy ⊢
      omega
  let prefixSize := if 17 ≤ ciphertext.size then 16 * (ciphertext.size / 16) else 0
  let front := ciphertext.extract 0 prefixSize
  let tailBytes := ciphertext.extract prefixSize ciphertext.size
  have prefixBound : prefixSize ≤ ciphertext.size := by
    dsimp only [prefixSize]
    split <;> omega
  have frontSize : front.size = prefixSize := by simp only [front,ByteArray.size_extract,Nat.min_eq_left prefixBound,Nat.sub_zero]
  have tailSize : tailBytes.size = ciphertext.size - prefixSize := by simp only [tailBytes,ByteArray.size_extract,Nat.min_self]
  have tailBound : tailBytes.size ≤ 16 := by
    rw [tailSize]
    dsimp only [prefixSize]
    split <;> omega
  have bytesSplit : front ++ tailBytes = ciphertext := by
    change ciphertext.extract 0 prefixSize ++ ciphertext.extract prefixSize ciphertext.size = ciphertext
    rw [ByteArray.extract_append_extract,Nat.min_eq_left (Nat.zero_le _),Nat.max_eq_right prefixBound,ByteArray.extract_zero_size]
  have ndesc : (fr.r8 + 8).toNat = fr.r8.toNat + 8 := by have hh := counterBuffer.1.low; bv_omega
  have descriptorContains (x : Nat) (hx : (span (fr.r8 + 8) 8).Contains x) :
      (span fr.r8 24).Contains x := by
    simp only [span,MemoryRegion.Contains,ndesc] at hx ⊢
    omega
  have prefixContains (ptr : BitVec 64) (x : Nat) (hx : (span ptr front.size).Contains x) :
      (span ptr ciphertext.size).Contains x := by
    simp only [span,MemoryRegion.Contains,frontSize] at hx ⊢
    omega
  have scheduleSep := hsep (span (fr.rdi + 32) (16 * ((AES16.variant use256).Nr + 1))) (by simp)
  have sourceSep := hsep (span source ciphertext.size) (by simp)
  have descriptorSep := hsep (span fr.r8 24) (by simp)
  by_cases hlong : 17 ≤ ciphertext.size
  · have cLong : counter.label = (if use256 then .l102885 else .l102425) := by
      simpa only [Nat.not_lt.mpr hlong, ↓reduceIte] using cLabel
    rw [cLong] at cFrame
    have fullFrame : Atom.All code counter.arguments counter.store
        (if use256 then LIR.Fn102720.frameAt .l102885 fr else LIR.Fn1022c0.frameAt .l102425 fr) := by
      cases use256 <;> exact cFrame
    have frontCount : front.size = 16 * (ciphertext.size / 16) := by
      rw [frontSize]
      exact ite_eq_left hlong
    have readFront : Readable counter.store source front.size :=
      counterBuffer.2.2.2.2.1.sub (Nat.le_refl _) (by rw [frontSize]; omega)
    have bytesFront : (span source front.size).HasBytes counter.store front := by
      have hb := hasBytes_extract counterBuffer.2.2.2.2.2.1 0 prefixSize (by omega) prefixBound
        (by have hh := counterBuffer.2.2.2.2.1.low; omega)
      simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_zero,Nat.sub_zero,frontSize] using hb
    have writeFront : Writable code counter.store destination front.size :=
      destWriteCounter.sub (Nat.le_refl _) (by rw [frontSize]; omega)
    have frontAlias : source = destination ∨ (span source front.size).Disjoint (span destination front.size) := by
      rcases counterBuffer.2.2.2.2.2.2 with eq | sep
      · exact Or.inl eq
      · exact Or.inr (subdisjoint sep (by rw [frontSize]; exact prefixBound) (by rw [frontSize]; exact prefixBound))
    obtain ⟨full,fullRun,fullLabel,fullWorking,fullTyped,fullWrites,fullStatus,fullSource,
      fullLength,fullCounter,fullDescriptor,fullCount,fullAdvanced,fullBytes,fullKey⟩ :=
      Decrypt.fullBlocks_reaches use256 code hcode key crypt front
        ((counter.arguments[14]'(by change 14 < 53; decide)).get 64) source destination fr
        counter.arguments counter.store fullFrame cTyped rfl cSource cCounter cMask
        (by rw [cLength]; have hh := counterBuffer.2.2.2.2.1.low; omega)
        (by rw [cLength]; omega) (by rw [cLength]; exact frontCount)
        schedule scheduleReadCounter counterKeyValue descriptorWrite counterBuffer.2.2.1
        readFront bytesFront writeFront frontAlias
        (by
          intro r hin
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hin
          rcases hin with rfl | rfl | rfl | rfl
          · exact scheduleSep
          · intro x hx hy
            exact sourceSep x hx (prefixContains source x hy)
          · intro x hx hy
            exact hsep (span destination ciphertext.size) (by simp) x hx (prefixContains destination x hy)
          · intro x hx hy
            exact descriptorSep x hx (descriptorContains x hy))
        (by
          intro r hin
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hin
          rcases hin with rfl | rfl | rfl
          · intro x hx hy
            exact hdescsep (span (fr.rdi + 32) (16 * ((AES16.variant use256).Nr + 1))) (by simp)
              x (descriptorContains x hx) hy
          · intro x hx hy
            exact hdescsep (span source ciphertext.size) (by simp)
              x (descriptorContains x hx) (prefixContains source x hy)
          · intro x hx hy
            exact hdescsep (span destination ciphertext.size) (by simp)
              x (descriptorContains x hx) (prefixContains destination x hy))
        (by
          intro x hx hy
          exact destSep
            x (prefixContains destination x hx) hy)
        (by
          intro slot hin
          constructor
          · intro x hx hy
            exact (hslots slot hin).1 x (prefixContains destination x hx) hy
          · intro x hx hy
            exact (hslots slot hin).2 x (descriptorContains x hx) hy)
    obtain ⟨branched, branchRun, branchLabel, branchStore, branch0, branchKeep, branchTypes⟩ :=
      Decrypt.afterFull_runBlock use256 code full.arguments full.store
    have fullLoc : full = ⟨(if use256 then .l1028d0 else .l102470), full.arguments, full.store⟩ := by
      cases full with
      | mk l a m => change l = _ at fullLabel; cases fullLabel; rfl
    have branchReach : (LIR.program.sem (dialect code)).Reaches ⟨full, []⟩ ⟨branched, []⟩ := by
      have run : LIR.program.runBlock (dialect code) full = .jump branched := by rw [fullLoc]; exact branchRun
      exact .single (congrArg (Transfer.next (dialect code) []) run)
    have branchFrame : Atom.All code branched.arguments branched.store
        (if use256 then LIR.Fn102720.frameAt .l1028e4 fr else LIR.Fn1022c0.frameAt .l102484 fr) := by
      rw [branchStore]
      cases use256 <;>
        rcases fullWorking with ⟨r4,r22,r5,r39,r50,r51,m152,m136,m48,m40,m32,m24,m16,m8,
          rr,rv,rl,ww,room,align,s0r,s0v,s1r,s1v,s2r,s2v,s3r,s3v,ss⟩
      all_goals refine ⟨(branchKeep 4 (by decide)).trans r4,
        (branchKeep 22 (by decide)).trans r22,
        (branchKeep 5 (by decide)).trans r5,
        (branchKeep 39 (by decide)).trans r39,
        (branchKeep 50 (by decide)).trans r50,
        (branchKeep 51 (by decide)).trans r51,
        m152,m136,m48,m40,m32,m24,m16,m8,rr,rv,rl,ww,room,align,
        s0r,s0v,s1r,s1v,s2r,s2v,s3r,s3v,ss⟩
    have bLength : ((branched.arguments[14]'(by change 14 < 53; decide)).get 64).toNat =
        ciphertext.size % 16 := by
      have hh := (congrArg (fun v : Value => (v.get 64).toNat) (branchKeep 14 (by decide))).trans
        (congrArg BitVec.toNat fullLength)
      rw [cLength] at hh
      simp only [BitVec.toNat_ofNat] at hh
      rw [Nat.mod_eq_of_lt (by omega : ciphertext.size % 16 < 2^64)] at hh
      exact hh
    have bSource : (branched.arguments[13]'(by change 13 < 53; decide)).get 64 =
        source + BitVec.ofNat 64 front.size := by
      exact (congrArg (Value.get 64) (branchKeep 13 (by decide))).trans fullSource
    have bDescriptor : memLoad branched.store (fr.r8 + 8) 64 =
        destination + BitVec.ofNat 64 front.size := by
      rw [branchStore]
      exact fullDescriptor
    have bCounter : (branched.arguments[15]'(by change 15 < 53; decide)).get 64 =
        fr.rsp - 120 := by
      exact (congrArg (Value.get 64) (branchKeep 15 (by decide))).trans fullCounter
    have bKey : memLoad branched.store (fr.rsp - 128) 64 = fr.rdi + 32 := by
      rw [branchStore]
      exact fullKey
    have windowRoom : fr.low.toNat + (if use256 then 2912 else 2384) ≤ fr.rsp.toNat := by
      apply atomsAll_mem (atom := .fact _) fullFrame
      cases use256 <;> simp [LIR.Fn102720.frameAt, LIR.Fn102720.frameAtG2,
        LIR.Fn1022c0.frameAt, LIR.Fn1022c0.frameAtG1]
    let window := if use256 then 2912 else 2384
    have windowAddr : (fr.rsp - BitVec.ofNat 64 window).toNat = fr.rsp.toNat - window := by
      rw [BitVec.toNat_sub_of_le (by change window % 2^64 ≤ fr.rsp.toNat; omega),
        BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := fr.rsp.isLt; omega)]
    have branchedWrites : RamWriteFrame counter.store branched.store
        [span (fr.rsp - BitVec.ofNat 64 window) (window - 100),
          span (fr.r8 + 8) 8, span destination front.size] := by
      rw [branchStore]
      exact fullWrites
    have written : RamWriteFrame counter.store branched.store
        [fr.region, span destination ciphertext.size, span (fr.r8 + 8) 8] := by
      apply (RamWriteFrame.refl _ _).trans branchedWrites
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl
      · refine ⟨fr.region, by simp, ?_, ?_⟩ <;> simp only [span, Activation.region, windowAddr] <;> omega
      · exact ⟨_, by simp, Nat.le_refl _, Nat.le_refl _⟩
      · exact ⟨span destination ciphertext.size, by simp, Nat.le_refl _,
          Nat.add_le_add_left (show front.size ≤ ciphertext.size by omega) _⟩
    have reached : (LIR.program.sem (dialect code)).Reaches ⟨counter, []⟩ ⟨branched, []⟩ := by
      change (LIR.program.sem (dialect code)).Reaches ⟨⟨counter.label, counter.arguments, counter.store⟩, []⟩ _
      rw [cLong]
      exact fullRun.trans branchReach
    have branchedAL : (branched.arguments[0]'(by change 0 < 53; decide)).get 8 =
        (counter.arguments[0]'(by change 0 < 53; decide)).get 8 := by
      rw [branch0]
      simpa only [Value.get, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64),
        BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 32)] using fullStatus
    by_cases htail : ciphertext.size % 16 = 0
    · have bLabel : branched.label = (if use256 then .l1028d7 else .l102477) := by
        have fullZero : (full.arguments[14]'(by change 14 < 53; decide)).get 64 = 0 := by
          apply BitVec.eq_of_toNat_eq
          rw [fullLength, cLength]
          simp only [BitVec.toNat_ofNat]
          rw [Nat.mod_eq_of_lt (by omega : ciphertext.size % 16 < 2^64)]
          exact htail
        simpa only [fullZero,↓reduceIte] using branchLabel
      obtain ⟨done,doneRun,doneLabel,doneStore,doneKeep,doneTypes⟩ :=
        Decrypt.fullDone_runBlock use256 code branched.arguments branched.store
      have doneReach : (LIR.program.sem (dialect code)).Reaches ⟨branched,[]⟩ ⟨done,[]⟩ := by
        have run : LIR.program.runBlock (dialect code) branched = .jump done := by
          change LIR.program.runBlock (dialect code)
            ⟨branched.label,branched.arguments,branched.store⟩ = .jump done
          rw [bLabel]
          exact doneRun
        exact .single (congrArg (Transfer.next (dialect code) []) run)
      have doneFrame : Atom.All code done.arguments done.store
          (if use256 then LIR.Fn102720.frameAt .l102961 fr else LIR.Fn1022c0.frameAt .l102501 fr) := by
        rw [doneStore]
        cases use256 <;>
          rcases branchFrame with ⟨r4,r22,r5,r39,r50,r51,m152,m136,m48,m40,m32,m24,m16,m8,
            rr,rv,rl,ww,room,align,s0r,s0v,s1r,s1v,s2r,s2v,s3r,s3v,ss⟩
        all_goals refine ⟨(doneKeep 4 (by decide)).trans r4,
          (doneKeep 22 (by decide)).trans r22,
          (doneKeep 39 (by decide)).trans r39,
          (doneKeep 50 (by decide)).trans r50,
          (doneKeep 51 (by decide)).trans r51,
          m48,m40,m32,m24,m16,m8,rr,rv,rl,ww,room,align,trivial⟩
      have tailEmpty : tailBytes = ByteArray.empty := by
        apply ByteArray.size_eq_zero_iff.mp
        rw [tailSize]
        dsimp only [prefixSize]
        split <;> omega
      have frontEq : front = ciphertext := by
        simpa only [tailEmpty, ByteArray.append_empty] using bytesSplit
      refine ⟨done, reached.trans doneReach, doneLabel, doneFrame, doneTypes (branchTypes fullTyped),
        (by rw [doneStore]; exact written), (congrArg (Value.get 8) (doneKeep 0 (by decide))).trans branchedAL, ?_, ?_⟩
      · rw [doneStore, branchStore]
        rw [frontEq] at fullBytes
        exact fullBytes
      · rw [doneStore, bDescriptor, frontSize]
    · have fullNZ : (full.arguments[14]'(by change 14 < 53; decide)).get 64 ≠ 0 := by
        intro eq
        have bits := congrArg BitVec.toNat (fullLength.symm.trans eq)
        rw [cLength] at bits
        change (ciphertext.size % 16) % 2^64 = 0 at bits
        omega
      have bLabel : branched.label = (if use256 then .l1028e4 else .l102484) := by
        simpa only [fullNZ, ↓reduceIte] using branchLabel
      have remEq : tailBytes.size = ciphertext.size % 16 := by
        rw [tailSize, ← frontSize, frontCount]; omega
      have tailSrcLow := counterBuffer.2.2.2.2.1.low
      have tailDstLow := destWriteCounter.readable.low
      have addr (ptr : BitVec 64) (bound : ptr.toNat + ciphertext.size ≤ 2^32) :
          (ptr + BitVec.ofNat 64 front.size).toNat = ptr.toNat + front.size := by
        rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := front.size) (by omega),
          Nat.mod_eq_of_lt (by omega)]
      have srcAddr := addr source tailSrcLow
      have dstAddr := addr destination tailDstLow
      have tailIn (ptr : BitVec 64) (off : (ptr + BitVec.ofNat 64 front.size).toNat = ptr.toNat + front.size)
          {a : Nat} (h : (span (ptr + BitVec.ofNat 64 front.size) tailBytes.size).Contains a) :
          (span ptr ciphertext.size).Contains a := by
        simp only [span, MemoryRegion.Contains, off] at h ⊢
        omega
      obtain ⟨sched, readTail, bytesTail, writeTail⟩ := fullBlocks_suffix
        (u := use256) (n := front.size) (by omega) windowRoom counterBuffer destWriteCounter
        schedule scheduleReadCounter
        (by
          intro r hr
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
          rcases hr with rfl | rfl
          · exact scheduleSep
          · exact sourceSep)
        (by
          intro r hr
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
          rcases hr with rfl | rfl <;> exact hdescsep _ (by simp))
        destSep branchedWrites
      have remSize : ciphertext.size - front.size = tailBytes.size := by rw [frontSize, tailSize]
      rw [remSize] at readTail bytesTail writeTail
      rw [frontSize] at bytesTail
      change (span (source + BitVec.ofNat 64 prefixSize) tailBytes.size).HasBytes branched.store tailBytes at bytesTail
      obtain ⟨last, tailRun, label, frame, typed, writes, al, tailPlain, descriptor⟩ := tail_exit
        use256 code hcode key crypt tailBytes (by omega) tailBound fr branched.arguments branched.store
        (source + BitVec.ofNat 64 front.size) (destination + BitVec.ofNat 64 front.size)
        branchFrame (branchTypes fullTyped) bSource (bLength.trans remEq.symm) bCounter sched
        (scheduleReadCounter.of_frame branchedWrites) bKey readTail (by rwa [frontSize])
        (counterBuffer.1.of_frame branchedWrites) bDescriptor writeTail
        (by
          intro r hr
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl
          · exact scheduleSep
          · exact fun a ha hb => sourceSep a ha (tailIn source srcAddr hb)
          · exact fun a ha hb => hsep (span destination ciphertext.size) (by simp) a ha (tailIn destination dstAddr hb)
          · exact descriptorSep)
        (fun a ha hb => hdescsep _ (by simp) a ha (tailIn destination dstAddr hb))
      have tailReaches : (LIR.program.sem (dialect code)).Reaches ⟨branched, []⟩ ⟨last, []⟩ := by
        change (LIR.program.sem (dialect code)).Reaches
          ⟨⟨branched.label, branched.arguments, branched.store⟩, []⟩ _
        rw [bLabel]
        exact tailRun
      refine ⟨last, reached.trans tailReaches, label, frame, typed, ?_, al.trans branchedAL, ?_, ?_⟩
      · apply written.trans writes
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact ⟨fr.region, by simp, Nat.le_refl _, Nat.le_refl _⟩
        · refine ⟨span destination ciphertext.size, by simp, ?_, ?_⟩ <;> simp only [span, dstAddr] <;> omega
      · rw [branchStore, fullAdvanced, cLength] at tailPlain
        have joined := tail_output frontCount (by omega : destination.toNat + front.size < 2^64)
          (fun a ha hb => hsep (span destination ciphertext.size) (by simp) a ha (prefixContains destination a hb))
          (by rw [branchStore]; exact fullBytes) writes tailPlain
        rw [bytesSplit] at joined
        exact joined
      · rw [descriptor, frontSize]
  · have cSmall : counter.label = (if use256 then .l1028dc else .l10247c) := by
      simpa only [Nat.lt_of_not_ge hlong, ↓reduceIte] using cLabel
    rw [cSmall] at cFrame
    obtain ⟨small, run, label, store, moved, keep, typed⟩ := small_runBlock use256 code counter.arguments counter.store
    have nz : (counter.arguments[14]'(by change 14 < 53; decide)).get 64 ≠ 0 := by
      intro eq; rw [eq] at cLength; change 0 = ciphertext.size at cLength; omega
    have smallLabel : small.label = (if use256 then .l1028e4 else .l102484) := by
      simpa only [nz, ↓reduceIte] using label
    have runStart : LIR.program.runBlock (dialect code) counter = .jump small := by
      change LIR.program.runBlock (dialect code) ⟨counter.label,counter.arguments,counter.store⟩ = _
      rw [cSmall]; exact run
    have frame : Atom.All code small.arguments small.store
        (if use256 then LIR.Fn102720.frameAt .l1028e4 fr else LIR.Fn1022c0.frameAt .l102484 fr) := by
      rw [store]
      cases use256 <;> rcases cFrame with ⟨r4,r22,r5,r13,r39,r50,r51,rest⟩
      all_goals exact ⟨(keep 4 (by decide)).trans r4, (keep 22 (by decide)).trans r22,
        (keep 5 (by decide)).trans r5, (keep 39 (by decide)).trans r39,
        (keep 50 (by decide)).trans r50, (keep 51 (by decide)).trans r51, rest⟩
    obtain ⟨last, tailRun, lastLabel, lastFrame, lastTyped, writes, al, bytes, desc⟩ := tail_exit
      use256 code hcode key crypt ciphertext positive (by omega) fr small.arguments small.store source destination
      frame (typed cTyped) (by rw [moved]; exact cSource)
      ((congrArg (fun v : Value => (v.get 64).toNat) (keep 14 (by decide))).trans cLength)
      ((congrArg (Value.get 64) (keep 15 (by decide))).trans cCounter)
      (by rwa [store]) (by rwa [store]) (by rwa [store]) (by rw [store]; exact counterBuffer.2.2.2.2.1)
      (by rw [store]; exact counterBuffer.2.2.2.2.2.1) (by rw [store]; exact counterBuffer.1)
      (by rw [store]; exact counterBuffer.2.2.1) (by rwa [store]) hsep (hdescsep _ (by simp))
    have tailReaches : (LIR.program.sem (dialect code)).Reaches ⟨small, []⟩ ⟨last, []⟩ := by
      change (LIR.program.sem (dialect code)).Reaches ⟨⟨small.label,small.arguments,small.store⟩,[]⟩ _
      rw [smallLabel]
      exact tailRun
    have firstStep : (LIR.program.sem (dialect code)).Reaches ⟨counter, []⟩ ⟨small, []⟩ :=
      .single (congrArg (Transfer.next (dialect code) []) runStart)
    rw [store] at writes bytes
    refine ⟨last, firstStep.trans tailReaches, lastLabel, lastFrame, lastTyped, ?_,
      al.trans (congrArg (Value.get 8) (keep 0 (by decide))), bytes, ?_⟩
    · apply (RamWriteFrame.refl _ _).trans writes
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl <;> exact ⟨_, by simp, Nat.le_refl _, Nat.le_refl _⟩
    · simpa only [hlong, ↓reduceIte, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using desc

end AesGcm.Proofs.Machine.Core.Decrypt
