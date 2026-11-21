import AesGcm.Proofs.Machine.CTR.CounterBatch
import AesGcm.Proofs.Machine.CTR.CounterBlocks
import AesGcm.Proofs.Machine.AES64.Input
import AesGcm.Proofs.Machine.Runtime.Frame
import AesGcm.Proofs.Machine.Runtime.Call

import AesGcm.Proofs.Machine.CTR.GCTR
import AesGcm.Proofs.Machine.CTR.InitialCounter
import X86Proofs.Program.ReadWrite.Bytes

namespace AesGcm.Proofs.Machine.CTR
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 4096 in
theorem batch_input_reaches (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (args : Values Value Reg.count) (mem : Ram) (sp counter : BitVec 64)
    (hTypes : GPRsTyped args) (hsp : args[4].get 64 = sp)
    (hcounter : args[9].get 64 = counter)
    (hroom : 80 ≤ sp.toNat) (halign : sp.toNat % 16 = 0)
    (hw : Writable code mem (sp - 80) 400)
    (hc : Writable code mem counter 20)
    (hApart : sp.toNat + 320 ≤ counter.toNat ∨ counter.toNat + 20 ≤ sp.toNat - 80)
    (hdf : args[22] = ⟨1, 0⟩)
    (h39 : args[39] = ⟨32, args[39].get 32⟩)
    (h50 : args[50] = ⟨16, args[50].get 16⟩)
    (h51 : args[51] = ⟨16, args[51].get 16⟩) :
    ∃ next : LIR.lifted.Location,
      (LIR.program.sem (dialect code)).Reaches
        ⟨⟨if use256 then .l108e98 else .l107a08, args, mem⟩, []⟩ ⟨next, []⟩ ∧
      next.label = batchReturnLabel use256 ∧ GPRsTyped next.arguments ∧
      (∀ r : Fin 53, r.val ∈ [3,4,5,12,13,14,15,22,39,50,51] → next.arguments[r] = args[r]) ∧
      (∀ p : Fin 8, memLoad next.store (sp + 8 + BitVec.ofNat 64 (8 * p.val)) 64 =
        Fixslice.encode (counterBlocks mem counter) p) ∧
      memLoad next.store (counter + 16) 32 = memLoad mem (counter + 16) 32 + 4 ∧
      RamWriteFrame mem next.store
        [span (sp - 80) 80, span (sp + 8) 64, span (sp + 256) 64, span (counter + 16) 4] := by
  have hs80 : (sp - 80).toNat = sp.toNat - 80 := by bv_omega
  have hs8 : (sp - 8).toNat = sp.toNat - 8 := by bv_omega
  have hlow : sp.toNat + 320 ≤ 2^32 := by have hh := hw.readable.low; rw [hs80] at hh; omega
  have hadd (n : Nat) (hn : n ≤ 320) : (sp + BitVec.ofNat 64 n).toNat = sp.toNat + n := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)]
  have ha8 : (sp + 8).toNat = sp.toNat + 8 := by simpa only [BitVec.ofNat_eq_ofNat] using hadd 8 (by decide)
  have ha256 : (sp + 256).toNat = sp.toNat + 256 := by simpa only [BitVec.ofNat_eq_ofNat] using hadd 256 (by decide)
  have hs8write : Writable code mem (sp - 8) 328 := hw.sub (by rw [hs80, hs8]; omega) (by rw [hs80, hs8]; omega)
  obtain ⟨callee, hcall, hlabel, h4, h7, h6, h2, hmem, hkeep, htyped⟩ :=
    batch_prepare_execution use256 code hcode args mem sp counter hTypes hsp hcounter hs8write hc
  have hc4 : (callee.arguments[4]'(by change 4 < 53; decide)).get 64 = sp - 8 := congrArg (Value.get 64) h4
  have hc7 : (callee.arguments[7]'(by change 7 < 53; decide)).get 64 = sp + 8 := congrArg (Value.get 64) h7
  have hc6 : (callee.arguments[6]'(by change 6 < 53; decide)).get 64 = 8 := congrArg (Value.get 64) h6
  have hc2 : (callee.arguments[2]'(by change 2 < 53; decide)).get 64 = sp + 256 := congrArg (Value.get 64) h2
  have hf : RamWriteFrame mem callee.store
      [span (sp - 8) 8, span (sp + 8) 64, span (sp + 256) 64, span (counter + 16) 4] := by
    rw [hmem]
    exact batchMemory_frame mem sp counter _ hs8write.readable.low hc.readable.low
  let af := activationOfValues callee.store callee.arguments (batchReturnAddress use256) (sp - 80)
  have hafsp : af.rsp = sp - 8 := hc4
  have haflow : af.low = sp - 80 := rfl
  have hafout : af.rdi = sp + 8 := hc7
  have hafin : af.rdx = sp + 256 := hc2
  have hpre : af.rsi = 8 ∧ Readable callee.store af.rdx 64 ∧
      Writable code callee.store af.rdi 64 ∧ (callStack af).Disjoint (span af.rdi 64) ∧
      (callStack af).Disjoint (span af.rdx 64) ∧ (span af.rdi 64).Disjoint (span af.rdx 64) := by
    rw [hafout, hafin]
    refine ⟨hc6, ?_, ?_, ?_, ?_, ?_⟩
    · apply (hw.readable.of_frame hf).sub
      all_goals rw [hs80, ha256]; omega
    · apply (hw.of_frame hf).sub
      all_goals rw [hs80, ha8]; omega
    all_goals intro x hx hy
    all_goals simp only [callStack, span, MemoryRegion.Contains, hafsp, haflow, hs8, hs80] at hx hy
    all_goals have h8 := hadd 8 (by decide); have h256 := hadd 256 (by decide)
    all_goals change (sp + 8).toNat = _ at h8
    all_goals change (sp + 256).toNat = _ at h256
    all_goals omega
  have hc39 : callee.arguments[39]'(by change 39 < 53; decide) = args[39] := hkeep 39 (by decide)
  have hc50 : callee.arguments[50]'(by change 50 < 53; decide) = args[50] := hkeep 50 (by decide)
  have hc51 : callee.arguments[51]'(by change 51 < 53; decide) = args[51] := hkeep 51 (by decide)
  obtain ⟨output, hexec, htag, hdone, houtTypes, hframe, hpost⟩ :=
    callContract_exec_values LIR.lifted code .l10a690 LIR.Fn10a690.frameInfo _ _ _
      (AES64.input_call code hcode) callee.store callee.arguments (batchReturnAddress use256) (sp - 80)
      htyped
      (by rw [hc39, h39]; rfl)
      (by rw [hc50, h50]; rfl)
      (by rw [hc51, h51]; rfl)
      ((hkeep 22 (by decide)).trans hdf)
      (by rw [hc4]; exact (hs8write.readable.of_frame hf).sub (Nat.le_refl _) (by omega))
      (by rw [hc4, hmem]; exact batchMemory_ret _ _ _ _)
      (by cases use256 <;> decide)
      (by intro _; rw [hc4]; change Writable code callee.store (sp - 8 - 72) 72
          rw [show sp - 8 - 72 = sp - 80 by bv_omega]
          exact (hw.of_frame hf).sub (Nat.le_refl _) (by omega))
      (by change (sp - 80).toNat + 72 ≤ ((callee.arguments[4]'(by change 4 < 53; decide)).get 64).toNat
          rw [hc4, hs80, hs8]; omega)
      (by rw [hc4, hs8]; omega)
      (by trivial) hpre
  change Atom.All code output.values output.store (LIR.Fn10a690.frameInfo.doneAtoms af) at hdone
  change RamWriteFrame callee.store output.store [af.region, span af.rdi 64] at hframe
  have hd : output.values[4] = ⟨64, af.rsp + 8⟩ ∧ output.values[22] = ⟨1, 0⟩ ∧
      output.values[3] = ⟨64, af.rbx⟩ ∧ output.values[5] = ⟨64, af.rbp⟩ ∧
      output.values[12] = ⟨64, af.r12⟩ ∧ output.values[13] = ⟨64, af.r13⟩ ∧
      output.values[14] = ⟨64, af.r14⟩ ∧ output.values[15] = ⟨64, af.r15⟩ ∧
      output.values[39] = ⟨32, af.mxcsr⟩ ∧ output.values[50] = ⟨16, af.ftw⟩ ∧
      output.values[51] = ⟨16, af.fcw⟩ ∧ True := hdone
  rcases hd with ⟨ho4, ho22, ho3, ho5, ho12, ho13, ho14, ho15, ho39, ho50, ho51, -⟩
  have keep (r : Fin 53) (hr : r.val ∈ [3,4,5,12,13,14,15,22,39,50,51]) : output.values[r] = args[r] := by
    rcases r with ⟨r, hrlt⟩
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ho3.trans ((htyped.value 3).symm.trans (hkeep 3 (by decide)))
    · change output.values[4] = args[4]
      rw [ho4, hafsp, show sp - 8 + 8 = sp by bv_omega, ← hsp]; exact (hTypes.value 4).symm
    · exact ho5.trans ((htyped.value 5).symm.trans (hkeep 5 (by decide)))
    · exact ho12.trans ((htyped.value 12).symm.trans (hkeep 12 (by decide)))
    · exact ho13.trans ((htyped.value 13).symm.trans (hkeep 13 (by decide)))
    · exact ho14.trans ((htyped.value 14).symm.trans (hkeep 14 (by decide)))
    · exact ho15.trans ((htyped.value 15).symm.trans (hkeep 15 (by decide)))
    · exact ho22.trans hdf.symm
    · exact ho39.trans ((congrArg (fun v : Value ↦ Value.mk 32 (v.get 32)) (hkeep 39 (by decide))).trans h39.symm)
    · exact ho50.trans ((congrArg (fun v : Value ↦ Value.mk 16 (v.get 16)) (hkeep 50 (by decide))).trans h50.symm)
    · exact ho51.trans ((congrArg (fun v : Value ↦ Value.mk 16 (v.get 16)) (hkeep 51 (by decide))).trans h51.symm)
  have hc16 : (counter + 16).toNat = counter.toNat + 16 := by
    have hh := hc.readable.low
    bv_omega
  have counterOutside : Outside [af.region, span af.rdi 64] (counter + 16) 4 := by
    refine ⟨by have hh := hc.readable.low; rw [hc16]; omega, ?_⟩
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    all_goals simp only [Activation.region, span, haflow, hafsp, hafout, hs80, hs8, ha8, hc16]
    all_goals omega
  have hcounterPost : memLoad output.store (counter + 16) 32 = memLoad mem (counter + 16) 32 + 4 := by
    rw [hframe.memLoad_eq counterOutside, hmem]
    exact batchMemory_counter mem sp counter _ hs8write.readable.low hc.readable.low (by omega) (by omega)
  have hframe0 : RamWriteFrame mem callee.store
      [span (sp - 80) 80, span (sp + 8) 64, span (sp + 256) 64, span (counter + 16) 4] := by
    apply (RamWriteFrame.refl _ _).trans hf
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · refine ⟨span (sp - 80) 80, by simp, ?_, ?_⟩ <;> simp only [span, hs80, hs8] <;> omega
    all_goals exact ⟨_, by simp, Nat.le_refl _, Nat.le_refl _⟩
  have hframeAll := hframe0.trans hframe (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    · refine ⟨span (sp - 80) 80, by simp, ?_, ?_⟩
      all_goals simp only [Activation.region, span, haflow, hafsp, hs80, hs8]
      all_goals omega
    · rw [hafout]; exact ⟨_, by simp, Nat.le_refl _, Nat.le_refl _⟩)
  have hexecc : LIR.program.Exec (dialect code) ⟨callee, []⟩ output := by
    change LIR.program.Exec (dialect code) ⟨⟨callee.label, callee.arguments, callee.store⟩, []⟩ output
    rw [hlabel]; exact hexec
  have ha : (batchFrame use256).Accepts (dialect code) output.tag = true := by
    simp only [batchFrame, StackFrame.Accepts, htag]
    cases use256 <;> rfl
  have hs : LIR.program.step (dialect code)
      ⟨⟨if use256 then .l108e98 else .l107a08, args, mem⟩, []⟩ =
      .next ⟨callee, [batchFrame use256]⟩ := by rw [Program.step, hcall]; rfl
  let next := (batchFrame use256).resume output
  have hnargs : next.arguments = output.values := CFGCall.resume_arguments _ _
  refine ⟨next, (Semantics.Reaches.single hs).trans (CFGCall.exec_reaches_resume hexecc _ [] ha),
    rfl, ?_, ?_, ?_, hcounterPost, hframeAll⟩
  · simpa only [hnargs] using houtTypes
  · simpa only [hnargs] using keep
  · intro p
    have hp := hpost p
    change memLoad output.store (af.rdi + BitVec.ofNat 64 (8 * p.val)) 64 =
      Fixslice.encode (Fixslice.memoryBlocks callee.store af.rdx) p at hp
    rw [hafout, hafin, hmem, memoryBlocks_batchMemory mem sp counter _ hs8write.readable.low
      hc.readable.low (by omega) (by omega)] at hp
    exact hp

open Standards.NIST Standards.NIST.GCM AesGcm.Spec.GCM

private theorem bytesOfBits_bit (x : Vector Bool (8 * n)) (i k : Nat) (hi : i < n)
    (hk : k < 8) :
    (bytesOfBits x)[i].toNat.testBit k = x[8 * i + (7 - k)]'(by omega) := by
  have he := congrArg (fun s : Vector Bool (8 * n) ↦ s[8 * i + (7 - k)]'(by omega))
    (bitsOfBytes_bytesOfBits x)
  simpa only [bitsOfBytes, Vector.getElem_ofFn, show (8 * i + (7 - k)) / 8 = i by omega,
    show 7 - (8 * i + (7 - k)) % 8 = k by omega] using he

theorem gctr_cipher_byte (v : AES.Variant) (key : Vector UInt8 v.keyBytes)
    (start : Vector Bool 128) (input : ByteArray) (i : Nat) (hi : i < input.size)
    (block : AES.Block) (hblock : Nat.repeat (inc 32) (i / 16) start = bitsOfBytes block) :
    (bytesOfBits (GCTR (forwardCipher v key) start (bitsOfByteArray input)))[i] =
      input[i] ^^^ (AES.cipher v key block)[i % 16]'(by omega) := by
  apply UInt8.eq_of_toBitVec_eq
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [UInt8.toBitVec_xor, BitVec.getLsbD_xor]
  change (bytesOfBits _)[i].toNat.testBit k = _
  rw [bytesOfBits_bit _ i k hi hk, gctr_getElem]
  let n := 8 * i + (7 - k)
  have hctr : n / 128 = i / 16 := by dsimp [n]; omega
  have ha : n / 8 = i := by dsimp [n]; omega
  have hb : 7 - n % 8 = k := by dsimp [n]; omega
  have hc : n % 128 / 8 = i % 16 := by dsimp [n]; omega
  have hd : 7 - ((n % 128) % 8) = k := by dsimp [n]; omega
  change ((bitsOfByteArray input)[n]'(by dsimp [n]; omega) ^^
    ((forwardCipher v key) (Nat.repeat (inc 32) (n / 128) start))[n % 128]'(by omega)) = _
  rw [hctr, hblock, forwardCipher, bytesOfBits_bitsOfBytes]
  simp only [bitsOfByteArray, bitsOfBytes, Vector.getElem_ofFn, Vector.getElem_mk,
    ha, hb, hc, hd]
  rfl

theorem batch_payload (v : AES.Variant) (key : Vector UInt8 v.keyBytes)
    (original current cipherMem after : Ram) (sp counter source destination : BitVec 64)
    (input : ByteArray) (c : Nat)
    (hcounter : bitsOfBytes (initialCounterBlock current counter) =
      Nat.repeat (inc 32) (4 * c) (bitsOfBytes (initialCounterBlock original counter)))
    (hcipher : Fixslice.memoryBlocks cipherMem (sp + 152) =
      Fixslice.fromStandard (fun b ↦ AES.cipher v key (Fixslice.toStandard (counterBlocks current counter) b)))
    (hsource : (span (source + BitVec.ofNat 64 (64 * c)) (input.size - 64 * c)).HasBytes
      cipherMem (input.extract (64 * c) input.size))
    (hfull : 64 * (c + 1) ≤ input.size)
    (hread : Readable after (destination + BitVec.ofNat 64 (64 * c)) 64)
    (hxor : ∀ w : Fin 8,
      memLoad after (destination + BitVec.ofNat 64 (64 * c) + BitVec.ofNat 64 (8 * w.val)) 64 =
      memLoad cipherMem (source + BitVec.ofNat 64 (64 * c) + BitVec.ofNat 64 (8 * w.val)) 64 ^^^
      memLoad cipherMem (sp + 152 + BitVec.ofNat 64 (8 * w.val)) 64) :
    (span (destination + BitVec.ofNat 64 (64 * c)) 64).HasBytes after
      ((byteArrayOfBits (GCTR (forwardCipher v key) (bitsOfBytes (initialCounterBlock original counter))
        (bitsOfByteArray input))).extract (64 * c) (64 * (c + 1))) := by
  let start := bitsOfBytes (initialCounterBlock original counter)
  let output := byteArrayOfBits (GCTR (forwardCipher v key) start (bitsOfByteArray input))
  have hsize : (output.extract (64 * c) (64 * (c + 1))).size = 64 := by
    rw [ByteArray.size_extract, show output.size = input.size from byteArrayOfBits_size _, Nat.min_eq_left hfull]
    omega
  refine ⟨hsize, ?_⟩
  rintro ⟨j, hj0⟩
  change j < (output.extract (64 * c) (64 * (c + 1))).size at hj0
  have hj : j < 64 := by omega
  let i := 64 * c + j
  let b : Fin 4 := ⟨j / 16, by omega⟩
  let t : Fin 16 := ⟨j % 16, by omega⟩
  have hadvance : Nat.repeat (inc 32) (i / 16) start =
      bitsOfBytes (Fixslice.toStandard (counterBlocks current counter) b) := by
    rw [counterBlocks_eq_repeat_inc, ← initialCounterBlock_eq_standard, hcounter]
    have hindex : i / 16 = 4 * c + b.val := by dsimp [i, b]; omega
    rw [hindex]
    have casesB : b.val = 0 ∨ b.val = 1 ∨ b.val = 2 ∨ b.val = 3 := by have := b.isLt; omega
    rcases casesB with h | h | h | h <;> rw [h] <;> rfl
  have hout := gctr_cipher_byte v key start input i (by dsimp [i]; omega) _ hadvance
  have hsrc := hsource.2 ⟨j, by rw [ByteArray.size_extract, Nat.min_self]; omega⟩
  simp only [span, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq,
    ByteArray.getElem_extract] at hsrc
  have hkey := congrFun (congrFun hcipher b) t
  change (memByte cipherMem (sp + 152 + BitVec.ofNat 64 (16 * b.val) + BitVec.ofNat 64 t.val)).toBitVec =
    (AES.cipher v key (Fixslice.toStandard (counterBlocks current counter) b))[t.val].toBitVec at hkey
  simp only [BitVec.add_assoc, ← BitVec.ofNat_add,
    show 16 * b.val + t.val = j by dsimp [b, t]; omega] at hkey
  have hword := congrArg (fun w : BitVec 64 ↦ storedByte w (j % 8))
    (hxor ⟨j / 8, by omega⟩)
  simp only [storedByte_xor, storedByte_memLoad _ _ _ (by omega : j % 8 < 64 / 8)] at hword
  simp only [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_assoc, show 8 * (j / 8) + j % 8 = j by omega] at hword
  have sbyte : memByte cipherMem (source + (BitVec.ofNat 64 (64 * c) + BitVec.ofNat 64 j)) =
      input[i]'(by dsimp [i]; omega) := by
    simp only [← BitVec.add_assoc, memByte, PhysicalMemory.read, hsrc, Option.getD_some, i]
  rw [← BitVec.ofNat_add] at sbyte
  simp only [show i % 16 = t.val by dsimp [i, t]; omega] at hout
  rw [sbyte, UInt8.eq_of_toBitVec_eq hkey, ← hout] at hword
  have present := hread.present j hj
  simp only [BitVec.add_assoc, ← BitVec.ofNat_add] at present
  obtain ⟨byte, hb⟩ := Option.isSome_iff_exists.mp present
  simp only [memByte, PhysicalMemory.read, hb, Option.getD_some] at hword
  change after[BitVec.ofNat 64 ((destination + BitVec.ofNat 64 (64 * c)).toNat + j)]? =
    some ((output.extract (64 * c) (64 * (c + 1)))[j]'hj0)
  simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, ByteArray.getElem_extract]
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, hb, hword]
  rfl

end AesGcm.Proofs.Machine.CTR
