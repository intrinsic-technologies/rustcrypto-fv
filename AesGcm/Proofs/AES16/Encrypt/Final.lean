import AesGcm.Proofs.AES16.Encrypt.Calls
import AesGcm.Proofs.AES16.Sbox
import AesGcm.Proofs.AES16.Output
import AesGcm.Proofs.Machine.Runtime.Frame

namespace AesGcm.Proofs.Machine.AES16.Encrypt

open Standards.NIST.AES Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime Fixslice16

def finalLabel (use256 : Bool) : LIR.Label := if use256 then .l106ebc else .l105636
def keyLabel (use256 : Bool) : LIR.Label := if use256 then .l106fbe else .l105735
def endLabel (use256 : Bool) : LIR.Label := if use256 then .l107038 else .l1057ae
def subReturn (use256 : Bool) : BitVec 64 := if use256 then 0x106fbe else 0x105735
def outReturn (use256 : Bool) : BitVec 64 := if use256 then 0x107038 else 0x1057ae
def planeOffset (use256 : Bool) : BitVec 64 := if use256 then 8 else 0

def finalContinuation (label : LIR.Label) (ret : BitVec 64) :
    LIR.lifted.StackFrame :=
  { target := label, kept := #v[], arity := rfl, guard := some ⟨64, ret⟩ }

private theorem rows128_rangeApart {code : CodeMap}
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) {mem : Ram} {a : BitVec 64} {n : Nat}
    (h : Writable code mem a n) : RangeApart a n 0x105636 255 := by
  have hx := storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l105636 x hx))
  have hlen : LIR.bytes_l105636.length = 255 := by decide +kernel
  rw [hlen] at hx
  exact hx.apart

private theorem rows256_rangeApart {code : CodeMap}
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) {mem : Ram} {a : BitVec 64} {n : Nat}
    (h : Writable code mem a n) : RangeApart a n 0x106ebc 258 := by
  have hx := storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l106ebc x hx))
  have hlen : LIR.bytes_l106ebc.length = 258 := by decide +kernel
  rw [hlen] at hx
  exact hx.apart

private theorem shiftRowsWord2_machine (x : BitVec 16) :
    (((x.setWidth 32 >>> 2).setWidth 16 ^^^ x) &&& 0x3030) <<< 2 ^^^
      (x ^^^ ((x.setWidth 32 >>> 2).setWidth 16 ^^^ x) &&& 0x3030) = shiftRowsWord2 x := by
  have hs : (x.setWidth 32 >>> 2).setWidth 16 = x >>> 2 := by
    rw [← BitVec.setWidth_ushiftRight (by decide : 16 ≤ 32)]
    simp only [BitVec.setWidth_setWidth_of_le (x >>> 2) (by decide : 16 ≤ 32), BitVec.setWidth_eq]
  rw [hs]
  simp only [shiftRowsWord2, deltaSwap1]
  rw [BitVec.xor_comm (x >>> 2) x]
  ac_rfl

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 4096 in
theorem finalRows_runBlock (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (args : Values Value Reg.count) (mem : Ram) (sp : BitVec 64)
    (planes : Planes16) (hsp : args[4].get 64 = sp)
    (hTypes : GPRsTyped args)
    (hStateWrite : Writable code mem (sp + planeOffset use256) 16)
    (hCallWrite : Writable code mem (sp - 8) 8)
    (hPlanes : ∀ p : Fin 8, (args[(planeReg p).val].get 64).setWidth 16 = planes p) :
    ∃ (callee : LIR.lifted.Location),
      LIR.program.runBlock (dialect code) ⟨finalLabel use256, args, mem⟩ =
        .call callee (finalContinuation (keyLabel use256) (subReturn use256)) ∧
      callee.label = .l100b10 ∧
      callee.arguments[4]'(by change 4 < 53; decide) = ⟨64, sp - 8⟩ ∧
      callee.arguments[7]'(by change 7 < 53; decide) = ⟨64, sp + planeOffset use256⟩ ∧
      callee.arguments[6]'(by change 6 < 53; decide) = ⟨64, 8⟩ ∧
      callee.arguments[15]'(by change 15 < 53; decide) = ⟨64, sp + planeOffset use256⟩ ∧
      (∀ r : Fin 53, r.val ∈ [3, 5, 12, 13, 14, 22, 39, 50, 51] →
        callee.arguments[r]'(by change r.val < 53; exact r.isLt) = args[r]) ∧
      GPRsTyped callee.arguments ∧
      WordsAt callee.store (sp + planeOffset use256) 16 (Vector.ofFn (shiftRows2 planes)) ∧
      RamWriteFrame mem callee.store [span (sp - 8) 8, span (sp + planeOffset use256) 16] ∧
      memLoad callee.store (sp - 8) 64 = subReturn use256 := by
  have hStateRead := hStateWrite.readable
  have hCallRead := hCallWrite.readable
  have hStateLow := hStateRead.low
  have hCallLow := hCallRead.low
  cases use256
  all_goals simp only [finalLabel, planeOffset, Bool.false_eq_true, ↓reduceIte] at *
  case false =>
    have hhelperApart := @rows128_rangeApart code hcode
    refine ⟨?callee, ?run, ?props⟩
    case run =>
      change LIR.program.runBlock (dialect code) ⟨.l105636, args, mem⟩ = _
      cfg_eval [hsp]
      runtime_guards call
      rfl
    case props =>
      refine ⟨rfl, rfl, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · runtime_finish []
      · runtime_finish []
      · rintro ⟨r, hr⟩ hin
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
        rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
      · runtime_typed
      · aes16_words
        all_goals runtime_finish [Vector.getElem_ofFn, shiftRows2, ← hPlanes, planeReg]
        all_goals exact shiftRowsWord2_machine _
      · runtime_finish [span]
      · runtime_finish []
  case true =>
    have hhelperApart := @rows256_rangeApart code hcode
    refine ⟨?callee256, ?run256, ?props256⟩
    case run256 =>
      change LIR.program.runBlock (dialect code) ⟨.l106ebc, args, mem⟩ = _
      cfg_eval [hsp]
      runtime_guards call
      rfl
    case props256 =>
      refine ⟨rfl, rfl, ?_, rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · runtime_finish []
      · runtime_finish []
      · rintro ⟨r, hr⟩ hin
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
        rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
      · runtime_typed
      · aes16_words
        all_goals runtime_finish [Vector.getElem_ofFn, shiftRows2, ← hPlanes, planeReg]
        all_goals exact shiftRowsWord2_machine _
      · runtime_finish [span]
      · runtime_finish []

private theorem key128_rangeApart {code : CodeMap}
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) {mem : Ram} {a : BitVec 64} {n : Nat}
    (h : Writable code mem a n) : RangeApart a n 0x105735 121 := by
  have hx := storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l105735 x hx))
  have hlen : LIR.bytes_l105735.length = 121 := by decide +kernel
  rw [hlen] at hx
  exact hx.apart

private theorem key256_rangeApart {code : CodeMap}
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) {mem : Ram} {a : BitVec 64} {n : Nat}
    (h : Writable code mem a n) : RangeApart a n 0x106fbe 122 := by
  have hx := storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l106fbe x hx))
  have hlen : LIR.bytes_l106fbe.length = 122 := by decide +kernel
  rw [hlen] at hx
  exact hx.apart

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 4096 in
theorem finalKey_runBlock (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (args : Values Value Reg.count) (mem : Ram) (sp base out : BitVec 64)
    (planes keys : Planes16)
    (hsp : args[4].get 64 = sp)
    (hbuf : args[15].get 64 = sp + planeOffset use256)
    (hbase : memLoad mem (sp + (if use256 then 48 else 40)) 64 = base)
    (hout : memLoad mem (sp + (if use256 then 64 else 48)) 64 = out)
    (hTypes : GPRsTyped args)
    (hStack : Writable code mem (sp - 8) 80)
    (hKeys : Readable mem (base + (if use256 then 224 else 160)) 16)
    (hApart : (sp - 8).toNat + 80 ≤ (base + (if use256 then 224 else 160)).toNat ∨
      (base + (if use256 then 224 else 160)).toNat + 16 ≤ (sp - 8).toNat)
    (hPlanes : WordsAt mem (sp + planeOffset use256) 16 (Vector.ofFn planes))
    (hKeyWords : WordsAt mem (base + (if use256 then 224 else 160)) 16 (Vector.ofFn keys)) :
    ∃ (callee : LIR.lifted.Location),
      LIR.program.runBlock (dialect code) ⟨keyLabel use256, args, mem⟩ =
        .call callee (finalContinuation (endLabel use256) (outReturn use256)) ∧
      callee.label = .l109d90 ∧
      callee.arguments[4]'(by change 4 < 53; decide) = ⟨64, sp - 8⟩ ∧
      callee.arguments[7]'(by change 7 < 53; decide) = ⟨64, out⟩ ∧
      callee.arguments[6]'(by change 6 < 53; decide) = ⟨64, sp + planeOffset use256⟩ ∧
      callee.arguments[2]'(by change 2 < 53; decide) = ⟨64, 8⟩ ∧
      (∀ r : Fin 53, r.val ∈ [5, 12, 13, 14, 15, 22, 39, 50, 51] →
        callee.arguments[r]'(by change r.val < 53; exact r.isLt) = args[r]) ∧
      GPRsTyped callee.arguments ∧
      WordsAt callee.store (sp + planeOffset use256) 16 (Vector.ofFn (xorPlanes planes keys)) ∧
      RamWriteFrame mem callee.store [span (sp - 8) 8, span (sp + planeOffset use256) 16] ∧
      memLoad callee.store (sp - 8) 64 = outReturn use256 := by
  have hStackRead := hStack.readable
  have hStackLow := hStackRead.low
  have hKeyLow := hKeys.low
  have hw0 := hPlanes 0 (by decide)
  have hw1 := hPlanes 1 (by decide)
  have hw2 := hPlanes 2 (by decide)
  have hw3 := hPlanes 3 (by decide)
  have hw4 := hPlanes 4 (by decide)
  have hw5 := hPlanes 5 (by decide)
  have hw6 := hPlanes 6 (by decide)
  have hw7 := hPlanes 7 (by decide)
  have hk0 := hKeyWords 0 (by decide)
  have hk1 := hKeyWords 1 (by decide)
  have hk2 := hKeyWords 2 (by decide)
  have hk3 := hKeyWords 3 (by decide)
  have hk4 := hKeyWords 4 (by decide)
  have hk5 := hKeyWords 5 (by decide)
  have hk6 := hKeyWords 6 (by decide)
  have hk7 := hKeyWords 7 (by decide)
  cases use256
  all_goals simp only [keyLabel, planeOffset, Bool.false_eq_true, ↓reduceIte, wordAddr,
    Nat.reduceDiv, Nat.reduceMul, Nat.reduceAdd, Vector.getElem_ofFn,
    BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.add_assoc, ← BitVec.ofNat_add] at *
  all_goals refine_norm [] at hbase
  all_goals refine_norm [] at hout
  all_goals refine_norm [] at hbuf
  all_goals refine_norm [] at hKeys
  all_goals refine_norm [] at hApart
  all_goals refine_norm [] at hw0
  all_goals refine_norm [] at hw1
  all_goals refine_norm [] at hw2
  all_goals refine_norm [] at hw3
  all_goals refine_norm [] at hw4
  all_goals refine_norm [] at hw5
  all_goals refine_norm [] at hw6
  all_goals refine_norm [] at hw7
  all_goals refine_norm [] at hk0
  all_goals refine_norm [] at hk1
  all_goals refine_norm [] at hk2
  all_goals refine_norm [] at hk3
  all_goals refine_norm [] at hk4
  all_goals refine_norm [] at hk5
  all_goals refine_norm [] at hk6
  all_goals refine_norm [] at hk7
  all_goals runtime_context [hbase, hout, hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7,
    hk0, hk1, hk2, hk3, hk4, hk5, hk6, hk7]
  case false =>
    have hhelperApart := @key128_rangeApart code hcode
    refine ⟨?callee, ?run, ?props⟩
    case run =>
      change LIR.program.runBlock (dialect code) ⟨.l105735, args, mem⟩ = _
      cfg_eval [hsp]
      runtime_guards call
      rfl
    case props =>
      refine ⟨rfl, rfl, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · runtime_finish [hout, hbase]
      · runtime_finish [hbuf]
      · rintro ⟨r, hr⟩ hin
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
        rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
      · runtime_typed
      · aes16_words
        all_goals runtime_finish [Vector.getElem_ofFn, xorPlanes, hbase, hout,
          hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7, hk0, hk1, hk2, hk3, hk4, hk5, hk6, hk7]
        all_goals rfl
      · runtime_finish [span]
      · runtime_finish []
  case true =>
    have hhelperApart := @key256_rangeApart code hcode
    refine ⟨?callee256, ?run256, ?props256⟩
    case run256 =>
      change LIR.program.runBlock (dialect code) ⟨.l106fbe, args, mem⟩ = _
      cfg_eval [hsp]
      runtime_guards call
      rfl
    case props256 =>
      refine ⟨rfl, rfl, ?_, ?_, rfl, ?_, ?_, ?_, ?_, ?_⟩
      · runtime_finish [hout, hbase]
      · runtime_finish [hbuf]
      · rintro ⟨r, hr⟩ hin
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
        rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
      · runtime_typed
      · aes16_words
        all_goals runtime_finish [Vector.getElem_ofFn, xorPlanes, hbase, hout,
          hw0, hw1, hw2, hw3, hw4, hw5, hw6, hw7, hk0, hk1, hk2, hk3, hk4, hk5, hk6, hk7]
        all_goals rfl
      · runtime_finish [span]
      · runtime_finish []

set_option maxHeartbeats 800000 in
theorem finalEpilogue_runBlock (use256 : Bool) (code : CodeMap)
    (fr : Activation) (args : Values Value Reg.count) (mem : Ram)
    (hRsp : args[4].get 64 = fr.rsp - (if use256 then 120 else 104))
    (hLoads : ∀ k : Fin 7, LoadOk mem (fr.rsp - BitVec.ofNat 64 (8 * k.val)) 8)
    (hSaved : ∀ r k : Nat, (r, k) ∈ [(3, 48), (12, 40), (13, 32),
      (14, 24), (15, 16), (5, 8)] →
      memLoad mem (fr.rsp - BitVec.ofNat 64 k) 64 = fr.entryReg r)
    (hRet : memLoad mem fr.rsp 64 = fr.ret) (hRetLow : fr.ret.toNat < 2 ^ 32)
    (hDF : args[22] = ⟨1, 0⟩) (hTypes : GPRsTyped args)
    (h39 : args[39] = ⟨32, fr.mxcsr⟩)
    (h50 : args[50] = ⟨16, fr.ftw⟩)
    (h51 : args[51] = ⟨16, fr.fcw⟩) :
    ∃ output, LIR.program.runBlock (dialect code) ⟨endLabel use256, args, mem⟩ =
      .returned output ∧ output.tag = some ⟨64, fr.ret⟩ ∧ output.store = mem ∧
      Atom.All code output.values output.store ((frameInfo use256).doneAtoms fr) ∧
      GPRsTyped output.values := by
  have hl0 := hLoads 0
  change LoadOk mem (fr.rsp - 0) 8 at hl0
  have hz : fr.rsp - (0 : BitVec 64) = fr.rsp := BitVec.sub_zero fr.rsp
  rw [hz] at hl0
  have hl1 := hLoads 1
  change LoadOk mem (fr.rsp - 8) 8 at hl1
  have hl2 := hLoads 2
  change LoadOk mem (fr.rsp - 16) 8 at hl2
  have hl3 := hLoads 3
  change LoadOk mem (fr.rsp - 24) 8 at hl3
  have hl4 := hLoads 4
  change LoadOk mem (fr.rsp - 32) 8 at hl4
  have hl5 := hLoads 5
  change LoadOk mem (fr.rsp - 40) 8 at hl5
  have hl6 := hLoads 6
  change LoadOk mem (fr.rsp - 48) 8 at hl6
  have hs3 := hSaved 3 48 (by decide)
  change memLoad mem (fr.rsp - 48) 64 = fr.rbx at hs3
  have hs12 := hSaved 12 40 (by decide)
  change memLoad mem (fr.rsp - 40) 64 = fr.r12 at hs12
  have hs13 := hSaved 13 32 (by decide)
  change memLoad mem (fr.rsp - 32) 64 = fr.r13 at hs13
  have hs14 := hSaved 14 24 (by decide)
  change memLoad mem (fr.rsp - 24) 64 = fr.r14 at hs14
  have hs15 := hSaved 15 16 (by decide)
  change memLoad mem (fr.rsp - 16) 64 = fr.r15 at hs15
  have hs5 := hSaved 5 8 (by decide)
  change memLoad mem (fr.rsp - 8) 64 = fr.rbp at hs5
  cases use256
  case false =>
    change args[4].get 64 = fr.rsp - 104 at hRsp
    change ∃ output, LIR.program.runBlock (dialect code) ⟨.l1057ae, args, mem⟩ =
      .returned output ∧ output.tag = some ⟨64, fr.ret⟩ ∧ output.store = mem ∧
      Atom.All code output.values output.store ((frameInfo false).doneAtoms fr) ∧
      GPRsTyped output.values
    cfg_eval [hRsp, hl0, hl1, hl2, hl3, hl4, hl5, hl6, hs3, hs12, hs13, hs14,
      hs15, hs5, hRet, hRetLow]
    refine ⟨_, rfl, rfl, rfl, ?_, ?_⟩
    · change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ True
      exact ⟨rfl, hDF, rfl, rfl, rfl, rfl, rfl, rfl, h39, h50, h51, trivial⟩
    · runtime_typed
  case true =>
    change args[4].get 64 = fr.rsp - 120 at hRsp
    change ∃ output, LIR.program.runBlock (dialect code) ⟨.l107038, args, mem⟩ =
      .returned output ∧ output.tag = some ⟨64, fr.ret⟩ ∧ output.store = mem ∧
      Atom.All code output.values output.store ((frameInfo true).doneAtoms fr) ∧
      GPRsTyped output.values
    cfg_eval [hRsp, hl0, hl1, hl2, hl3, hl4, hl5, hl6, hs3, hs12, hs13, hs14,
      hs15, hs5, hRet, hRetLow]
    refine ⟨_, rfl, rfl, rfl, ?_, ?_⟩
    · change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ True
      exact ⟨rfl, hDF, rfl, rfl, rfl, rfl, rfl, rfl, h39, h50, h51, trivial⟩
    · runtime_typed

private theorem decode_memory_words (block : Standards.NIST.AES.Block)
    {before after : Ram} {src dst : BitVec 64}
    (hwords : WordsAt before src 16 (Vector.ofFn (encodeStandard block)))
    (hdecode : Fixslice.memoryBlock after dst =
      decode (fun q ↦ memLoad before (src + BitVec.ofNat 64 (2 * q.val)) 16)) :
    Fixslice.memoryBlock after dst = fromStandard block := by
  have hp : (fun q : Fin 8 ↦ memLoad before (src + BitVec.ofNat 64 (2 * q.val)) 16) =
      encodeStandard block := by
    funext q
    simpa only [wordAddr, Nat.reduceDiv, Vector.getElem_ofFn] using hwords q.val q.isLt
  rw [hp] at hdecode
  simpa only [encodeStandard, decode_encode] using hdecode

set_option hygiene false in
local macro "final_proof" u:term "," win:num "," depth:num "," cp:num "," buf:num ","
    off:num "," keyoff:num "," outoff:num "," slot:num "," klen:num ","
    last:num "," subret:num "," outret:num "," ro:num : tactic =>
  `(tactic| (
    have hf := hwork.frame
    change args[4] = ⟨64, fr.rsp - $depth⟩ ∧ args[22] = ⟨1, 0⟩ ∧
      args[3] = ⟨64, fr.rsi⟩ ∧ args[39] = ⟨32, fr.mxcsr⟩ ∧
      args[50] = ⟨16, fr.ftw⟩ ∧ args[51] = ⟨16, fr.fcw⟩ ∧
      memLoad mem (fr.rsp - $slot) 64 = fr.rsi ∧ memLoad mem (fr.rsp - 56) 64 = fr.rdi ∧
      memLoad mem (fr.rsp - 48) 64 = fr.rbx ∧ memLoad mem (fr.rsp - 40) 64 = fr.r12 ∧
      memLoad mem (fr.rsp - 32) 64 = fr.r13 ∧ memLoad mem (fr.rsp - 24) 64 = fr.r14 ∧
      memLoad mem (fr.rsp - 16) 64 = fr.r15 ∧ memLoad mem (fr.rsp - 8) 64 = fr.rbp ∧
      Readable mem fr.rsp 8 ∧ memLoad mem fr.rsp 64 = fr.ret ∧ fr.ret.toNat < 2^32 ∧
      Writable code mem (fr.rsp - $win) $win ∧ fr.low.toNat + $win ≤ fr.rsp.toNat ∧
      fr.rsp.toNat % 16 = 8 ∧ Readable mem 0x201210 8 ∧ memLoad mem 0x201210 64 = 0x103880 ∧
      Readable mem 0x201230 8 ∧ memLoad mem 0x201230 64 = 0x101230 ∧
      ($ro ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x201210) ∧ True at hf
    rcases hf with ⟨hSP, hDF, h3, h39, h50, h51, hKeySlot, hOutSlot, hs3, hs12,
      hs13, hs14, hs15, hs5, hRetRead, hRet, hRetLow, hStack, hRoom, hAlign,
      hRoRead0, hRo0, hRoRead1, hRo1, hRoSep, -⟩
    have hBottom : (fr.rsp - $win).toNat = fr.rsp.toNat - $win := by bv_omega
    have hPreciseRoom := precise_room $u fr hRoom
    obtain ⟨hSpBound, hCPNat, hBNat, hCPRead, hChildWrite, hChildRoom, hChildAlign,
      hChildSep, hChildWithin, hTop⟩ :=
      call_geometry $u code mem (preciseActivation $u fr) 240 (by decide) hStack
        (Nat.le_of_eq hPreciseRoom) hAlign
    change (fr.rsp - $cp).toNat = fr.rsp.toNat - $cp at hCPNat
    change (fr.rsp - $buf).toNat = fr.rsp.toNat - $buf at hBNat
    change Readable mem (fr.rsp - $cp) 8 at hCPRead
    change Writable code mem (fr.rsp - $cp - 240) 240 at hChildWrite
    change (fr.rsp - $win).toNat + 240 ≤ (fr.rsp - $cp).toNat at hChildRoom
    change (fr.rsp - $cp).toNat % 16 = 8 at hChildAlign
    change (⟨(fr.rsp - $win).toNat,
      (fr.rsp - $cp).toNat + 8 - (fr.rsp - $win).toNat⟩ : MemoryRegion).Disjoint
        (span (fr.rsp - $buf) 16) at hChildSep
    let areas : List MemoryRegion :=
      [⟨(fr.rsp - $win).toNat, (fr.rsp - $cp).toNat - (fr.rsp - $win).toNat⟩,
        span (fr.rsp - $buf) 16, span (fr.rsp - $cp) 8]
    change RegionsWithin areas [(preciseActivation $u fr).region] at hChildWithin
    change ∀ k : Nat, k ≤ 72 → Outside areas (fr.rsp - BitVec.ofNat 64 k) 8 at hTop
    have hAreaRoot : RegionsWithin areas [fr.region] := by
      intro r hr
      obtain ⟨s, hs, ha, hb⟩ := hChildWithin r hr
      obtain ⟨t, ht, hc, hd⟩ := precise_within $u fr hRoom s hs
      exact ⟨t, ht, Nat.le_trans hc ha, Nat.le_trans hb hd⟩
    have areaWithin (rs : List MemoryRegion) (hin : rs ⊆ areas) : RegionsWithin rs areas := by
      intro r hr
      exact ⟨r, hin hr, Nat.le_refl _, Nat.le_refl _⟩
    have hRawWithin : RegionsWithin
        [span (fr.rsp - $cp) 8, span (fr.rsp - $buf) 16] areas := by
      apply areaWithin
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [areas, List.getElem_cons_zero, List.mem_cons, true_or, or_true]
    have hCallWithin : RegionsWithin
        [areas[0]'(by change 0 < 3; decide), span (fr.rsp - $buf) 16] areas := by
      apply areaWithin
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl <;> simp only [areas, List.getElem_cons_zero, List.mem_cons, true_or, or_true]
    have hRCP : fr.rsp - $depth - 8 = fr.rsp - $cp := by bv_omega
    have hRB : fr.rsp - $depth + planeOffset $u = fr.rsp - $buf := by
      change fr.rsp - $depth + $off = fr.rsp - $buf
      bv_omega
    have hBWrite : Writable code mem (fr.rsp - $buf) 16 :=
      hStack.of_offsets (addr_sub _ _) (addr_sub _ _) (by decide)
    have hCPWrite : Writable code mem (fr.rsp - $cp) 8 :=
      hStack.of_offsets (addr_sub _ _) (addr_sub _ _) (by decide)
    let p := roundState (variant $u) key input ((variant $u).Nr - 1)
    have hRegs : ∀ q : Fin 8, (args[(planeReg q).val].get 64).setWidth 16 = p q := hlast.regs
    obtain ⟨rows, hRowsRun, hRowsLabel, r4, r7, r6, r15, rKeep, rTypes, rWords, rFrame, rRet⟩ :=
      finalRows_runBlock $u code hcode args mem (fr.rsp - $depth) p
        (by rw [hSP]; rfl) hwork.typed (by rw [hRB]; exact hBWrite)
        (by rw [hRCP]; exact hCPWrite) hRegs
    rw [hRCP] at r4 rFrame rRet
    rw [hRB] at r7 r15 rWords rFrame
    rcases rows with ⟨rLab, rArgs, rMem⟩
    dsimp only at hRowsLabel hRowsRun r4 r7 r6 r15 rKeep rTypes rWords rFrame rRet
    subst rLab
    change Values Value Reg.count at rArgs
    have rWide : RamWriteFrame mem rMem areas := (RamWriteFrame.refl mem areas).trans rFrame hRawWithin
    have hSlotOutside0 := call_slot_outside $u code mem fr hStack hRoom hAlign hRoSep
      0x201210 (by decide) (by decide)
    have hSlotOutside1 := call_slot_outside $u code mem fr hStack hRoom hAlign hRoSep
      0x201230 (by decide) (by decide)
    change Outside areas 0x201210 8 at hSlotOutside0
    change Outside areas 0x201230 8 at hSlotOutside1
    have r39 : rArgs[39] = ⟨32, fr.mxcsr⟩ := (rKeep 39 (by decide)).trans h39
    have r50 : rArgs[50] = ⟨16, fr.ftw⟩ := (rKeep 50 (by decide)).trans h50
    have r51 : rArgs[51] = ⟨16, fr.fcw⟩ := (rKeep 51 (by decide)).trans h51
    have r22 : rArgs[22] = ⟨1, 0⟩ := (rKeep 22 (by decide)).trans hDF
    have subSlots : Atom.All code rArgs rMem
        (LIR.Fn100b10.frameInfo.callSlotAtoms LIR.Fn100b10.frameInfo.callSlots
          (activationOfValues rMem rArgs $subret (fr.rsp - $win))) := by
      change Readable rMem 0x201210 8 ∧ memLoad rMem 0x201210 64 = 0x103880 ∧
        Readable rMem 0x201230 8 ∧ memLoad rMem 0x201230 64 = 0x101230 ∧
        (0x201328 ≤ (rArgs[4].get 64).toNat ∨ (rArgs[4].get 64).toNat ≤ 0x201210) ∧ True
      rw [r4]
      refine ⟨hRoRead0.of_frame rWide, (rWide.memLoad_eq hSlotOutside0).trans hRo0,
        hRoRead1.of_frame rWide, (rWide.memLoad_eq hSlotOutside1).trans hRo1, ?_, trivial⟩
      change 0x201328 ≤ (fr.rsp - $cp).toNat ∨ (fr.rsp - $cp).toNat ≤ 0x201210
      omega
    obtain ⟨subOut, subExec, subTag, subDone, subTypes, subFrame, subPost⟩ :=
      callContract_exec_values LIR.lifted code .l100b10 LIR.Fn100b10.frameInfo
        (fun f ↦ [span f.rdi 16]) _ _ (subBytes_callContract code hcode)
        rMem rArgs $subret (fr.rsp - $win) rTypes
        (by rw [r39]; rfl) (by rw [r50]; rfl) (by rw [r51]; rfl) r22
        (by rw [r4]; exact hCPRead.of_frame rWide)
        (by rw [r4]; exact rRet)
        (by decide)
        (fun _ ↦ by rw [r4]; exact hChildWrite.of_frame rWide)
        (by rw [r4]; exact hChildRoom)
        (by rw [r4]; exact hChildAlign)
        subSlots (by
          change (rArgs[6].get 64) = 8 ∧ Writable code rMem (rArgs[7].get 64) 16 ∧
            (⟨(fr.rsp - $win).toNat, (rArgs[4].get 64).toNat + 8 - (fr.rsp - $win).toNat⟩ :
              MemoryRegion).Disjoint (span (rArgs[7].get 64) 16)
          rw [r6, r7, r4]
          exact ⟨rfl, hBWrite.of_frame rWide, hChildSep⟩)
    change RamWriteFrame rMem subOut.store
      [(activationOfValues rMem rArgs $subret (fr.rsp - $win)).region,
        span (activationOfValues rMem rArgs $subret (fr.rsp - $win)).rdi 16] at subFrame
    dsimp only [activationOfValues, Activation.region] at subFrame
    rw [r4, r7] at subFrame
    change RamWriteFrame rMem subOut.store [areas[0]'(by change 0 < 3; decide), span (fr.rsp - $buf) 16] at subFrame
    have internal : RamWriteFrame mem subOut.store areas := rWide.trans subFrame hCallWithin
    have hSubWords : WordsAt subOut.store (fr.rsp - $buf) 16
        (Vector.ofFn (subBytes (shiftRows2 p))) := by
      have hp : (fun q : Fin 8 ↦ memLoad rMem (fr.rsp - $buf + BitVec.ofNat 64 (2 * q.val)) 16) =
          shiftRows2 p := by
        funext q
        simpa only [wordAddr, Nat.reduceDiv, Vector.getElem_ofFn] using rWords q.val q.isLt
      change WordsAt subOut.store (rArgs[7].get 64) 16
        (Vector.ofFn (subBytes (fun q ↦ memLoad rMem
          (rArgs[7].get 64 + BitVec.ofNat 64 (2 * q.val)) 16))) at subPost
      rw [r7] at subPost
      change WordsAt subOut.store (fr.rsp - $buf) 16
        (Vector.ofFn (subBytes (fun q ↦ memLoad rMem
          (fr.rsp - $buf + BitVec.ofNat 64 (2 * q.val)) 16))) at subPost
      rw [hp] at subPost
      exact subPost
    change subOut.values[4] = ⟨64, rArgs[4].get 64 + 8⟩ ∧
      subOut.values[22] = ⟨1, 0⟩ ∧
      subOut.values[3] = ⟨64, rArgs[3].get 64⟩ ∧
      subOut.values[5] = ⟨64, rArgs[5].get 64⟩ ∧
      subOut.values[12] = ⟨64, rArgs[12].get 64⟩ ∧
      subOut.values[13] = ⟨64, rArgs[13].get 64⟩ ∧
      subOut.values[14] = ⟨64, rArgs[14].get 64⟩ ∧
      subOut.values[15] = ⟨64, rArgs[15].get 64⟩ ∧
      subOut.values[39] = ⟨32, rArgs[39].get 32⟩ ∧
      subOut.values[50] = ⟨16, rArgs[50].get 16⟩ ∧
      subOut.values[51] = ⟨16, rArgs[51].get 16⟩ ∧ True at subDone
    rcases subDone with ⟨s4, s22, s3, s5, s12, s13, s14, s15, s39, s50, s51, -⟩
    rw [r4] at s4
    change subOut.values[4] = ⟨64, fr.rsp - $cp + 8⟩ at s4
    have hBack : fr.rsp - $cp + 8 = fr.rsp - $depth := by bv_omega
    rw [hBack] at s4
    rw [r15] at s15
    change subOut.values[15] = ⟨64, fr.rsp - $buf⟩ at s15
    rw [r39] at s39
    rw [r50] at s50
    rw [r51] at s51
    change subOut.values[39] = ⟨32, fr.mxcsr⟩ at s39
    change subOut.values[50] = ⟨16, fr.ftw⟩ at s50
    change subOut.values[51] = ⟨16, fr.fcw⟩ at s51
    have internalRoot : RamWriteFrame mem subOut.store [fr.region] :=
      (RamWriteFrame.refl mem [fr.region]).trans internal hAreaRoot
    have hKeyOutside := key_outside (v := variant $u) (by omega : fr.low.toNat ≤ fr.rsp.toNat)
      hwork.readable hkeysep
    have hSchedule := scheduleIn_of_frame (v := variant $u) hwork.schedule internalRoot hKeyOutside
    have hKeyRead := hwork.readable.of_frame internal
    change Readable subOut.store fr.rsi $klen at hKeyRead
    have hLastRead : Readable subOut.store (fr.rsi + $last) 16 :=
      hKeyRead.of_offsets (x := fr.rsi) (c := $last) (d := 0) rfl (addr_self _) (by decide)
    have hLastWords := hSchedule.words ⟨(variant $u).Nr, by omega⟩
    change WordsAt subOut.store (fr.rsi + $last) 16
      (Vector.ofFn (expectedKey (variant $u) key ⟨(variant $u).Nr, by omega⟩)) at hLastWords
    have hBase : memLoad subOut.store (fr.rsp - $depth + $keyoff) 64 = fr.rsi := by
      have he : fr.rsp - $depth + $keyoff = fr.rsp - $slot := by bv_omega
      rw [he, internal.memLoad_eq (hTop $slot (by decide))]
      exact hKeySlot
    have hOut : memLoad subOut.store (fr.rsp - $depth + $outoff) 64 = fr.rdi := by
      have he : fr.rsp - $depth + $outoff = fr.rsp - 56 := by bv_omega
      rw [he, internal.memLoad_eq (hTop 56 (by decide))]
      exact hOutSlot
    have hLastLow := hKeyRead.low
    have hLastNat : (fr.rsi + $last).toNat = fr.rsi.toNat + $last := by bv_omega
    have hRootKeyApart := disjoint_bounds fr.low.toNat
      (fr.rsp.toNat + 8 - fr.low.toNat) fr.rsi.toNat $klen (by omega) (by decide) hkeysep
    have hLastApart : (fr.rsp - $cp).toNat + 80 ≤ (fr.rsi + $last).toNat ∨
        (fr.rsi + $last).toNat + 16 ≤ (fr.rsp - $cp).toNat := by
      rw [hLastNat]
      omega
    have hFinalWrite : Writable code subOut.store (fr.rsp - $cp) 80 :=
      (hStack.of_frame internal).of_offsets (addr_sub _ _) (addr_sub _ _) (by decide)
    obtain ⟨keyLoc, hKeyRun, hKeyLabel, k4, k7, k6, k2, kKeep, kTypes,
      kWords, kFrame, kRet⟩ := finalKey_runBlock $u code hcode subOut.values subOut.store
        (fr.rsp - $depth) fr.rsi fr.rdi (subBytes (shiftRows2 p))
        (expectedKey (variant $u) key ⟨(variant $u).Nr, by omega⟩)
        (by rw [s4]; rfl) (by rw [s15, hRB]; rfl) hBase hOut subTypes
        (by rw [hRCP]; exact hFinalWrite) hLastRead
        (by rw [hRCP]; exact hLastApart) (by rw [hRB]; exact hSubWords) hLastWords
    rw [hRCP] at k4 kFrame kRet
    rw [hRB] at k6 kWords kFrame
    rcases keyLoc with ⟨kLab, kArgs, kMem⟩
    dsimp only at hKeyRun hKeyLabel k4 k7 k6 k2 kKeep kTypes kWords kFrame kRet
    subst kLab
    change Values Value Reg.count at kArgs
    have internal2 : RamWriteFrame mem kMem areas := internal.trans kFrame hRawWithin
    have wholeKey : RamWriteFrame fr.original kMem [fr.region] :=
      hwork.written.trans internal2 hAreaRoot
    have hCipherWords : WordsAt kMem (fr.rsp - $buf) 16
        (Vector.ofFn (encodeStandard (cipher (variant $u) key input))) := by
      change WordsAt kMem (fr.rsp - $buf) 16
        (Vector.ofFn (xorPlanes (subBytes (shiftRows2
          (roundState (variant $u) key input ((variant $u).Nr - 1))))
          (expectedKey (variant $u) key ⟨(variant $u).Nr, by decide⟩))) at kWords
      rw [last_roundState $u key input] at kWords
      exact kWords
    have k39 : kArgs[39] = ⟨32, fr.mxcsr⟩ := (kKeep 39 (by decide)).trans s39
    have k50 : kArgs[50] = ⟨16, fr.ftw⟩ := (kKeep 50 (by decide)).trans s50
    have k51 : kArgs[51] = ⟨16, fr.fcw⟩ := (kKeep 51 (by decide)).trans s51
    have k22 : kArgs[22] = ⟨1, 0⟩ := (kKeep 22 (by decide)).trans s22
    have outSlots : Atom.All code kArgs kMem
        (LIR.Fn109d90.frameInfo.callSlotAtoms LIR.Fn109d90.frameInfo.callSlots
          (activationOfValues kMem kArgs $outret (fr.rsp - $win))) := by
      change Readable kMem 0x201210 8 ∧ memLoad kMem 0x201210 64 = 0x103880 ∧
        Readable kMem 0x201230 8 ∧ memLoad kMem 0x201230 64 = 0x101230 ∧
        (0x2012d8 ≤ (kArgs[4].get 64).toNat ∨ (kArgs[4].get 64).toNat ≤ 0x201210) ∧ True
      rw [k4]
      refine ⟨hRoRead0.of_frame internal2, (internal2.memLoad_eq hSlotOutside0).trans hRo0,
        hRoRead1.of_frame internal2, (internal2.memLoad_eq hSlotOutside1).trans hRo1, ?_, trivial⟩
      change 0x2012d8 ≤ (fr.rsp - $cp).toNat ∨ (fr.rsp - $cp).toNat ≤ 0x201210
      omega
    have hOutputApart := disjoint_bounds fr.low.toNat
      (fr.rsp.toNat + 8 - fr.low.toNat) fr.rdi.toNat 16 (by omega) (by decide) hsep
    have hChildOut : (⟨(fr.rsp - $win).toNat,
        (fr.rsp - $cp).toNat + 8 - (fr.rsp - $win).toNat⟩ : MemoryRegion).Disjoint
          (span fr.rdi 16) := by
      intro i hi ho
      dsimp only [MemoryRegion.Contains, span] at hi ho
      omega
    have hDataOut : (span fr.rdi 16).Disjoint (span (fr.rsp - $buf) 16) := by
      intro i hi ho
      dsimp only [MemoryRegion.Contains, span] at hi ho
      omega
    have hChildWrite160 : Writable code kMem (fr.rsp - $cp - 160) 160 :=
      by
        have he : fr.rsp - $cp - 160 = fr.rsp - ($cp + 160) := by bv_omega
        rw [he]
        exact (hStack.of_frame internal2).of_offsets (addr_sub _ _) (addr_sub _ _) (by decide)
    obtain ⟨decoded, decodeExec, decodeTag, decodeDone, decodeTypes, decodeFrame, decodePost⟩ :=
      callContract_exec_values LIR.lifted code .l109d90 LIR.Fn109d90.frameInfo
        (fun f ↦ [span f.rdi 16]) _ _ (output_call code hcode)
        kMem kArgs $outret (fr.rsp - $win) kTypes
        (by rw [k39]; rfl) (by rw [k50]; rfl) (by rw [k51]; rfl) k22
        (by rw [k4]; exact hCPRead.of_frame internal2)
        (by rw [k4]; exact kRet)
        (by decide)
        (fun _ ↦ by rw [k4]; exact hChildWrite160)
        (by rw [k4]; change (fr.rsp - $win).toNat + 160 ≤ (fr.rsp - $cp).toNat; omega)
        (by rw [k4]; exact hChildAlign)
        outSlots (by
          change kArgs[2].get 64 = 8 ∧ Readable kMem (kArgs[6].get 64) 16 ∧
            Writable code kMem (kArgs[7].get 64) 16 ∧
            (⟨(fr.rsp - $win).toNat, (kArgs[4].get 64).toNat + 8 - (fr.rsp - $win).toNat⟩ :
              MemoryRegion).Disjoint (span (kArgs[7].get 64) 16) ∧
            (⟨(fr.rsp - $win).toNat, (kArgs[4].get 64).toNat + 8 - (fr.rsp - $win).toNat⟩ :
              MemoryRegion).Disjoint (span (kArgs[6].get 64) 16) ∧
            (span (kArgs[7].get 64) 16).Disjoint (span (kArgs[6].get 64) 16)
          rw [k2, k6, k7, k4]
          exact ⟨rfl, hBWrite.readable.of_frame internal2, hwrite.of_frame wholeKey,
            hChildOut, hChildSep, hDataOut⟩)
    change RamWriteFrame kMem decoded.store
      [(activationOfValues kMem kArgs $outret (fr.rsp - $win)).region,
        span (activationOfValues kMem kArgs $outret (fr.rsp - $win)).rdi 16] at decodeFrame
    dsimp only [activationOfValues, Activation.region] at decodeFrame
    rw [k4, k7] at decodeFrame
    change RamWriteFrame kMem decoded.store [areas[0]'(by change 0 < 3; decide), span fr.rdi 16] at decodeFrame
    have hTotalWithin : RegionsWithin [areas[0]'(by change 0 < 3; decide), span fr.rdi 16]
        [fr.region, span fr.rdi 16] := by
      intro r hr
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl
      · obtain ⟨s, hs, ha, hb⟩ := hAreaRoot (areas[0]'(by change 0 < 3; decide))
          (by simp only [areas, List.getElem_cons_zero, List.mem_cons, true_or])
        have he : s = fr.region := List.mem_singleton.mp hs
        subst s
        exact ⟨fr.region, by simp only [List.mem_cons, true_or], ha, hb⟩
      · exact ⟨span fr.rdi 16, by simp only [List.mem_cons, true_or, or_true],
          Nat.le_refl _, Nat.le_refl _⟩
    have wholeOutput : RamWriteFrame fr.original decoded.store [fr.region, span fr.rdi 16] := by
      have hstart : RamWriteFrame fr.original kMem [fr.region, span fr.rdi 16] :=
        (RamWriteFrame.refl fr.original [fr.region, span fr.rdi 16]).trans wholeKey (by
          intro r hr
          have he : r = fr.region := List.mem_singleton.mp hr
          subst r
          exact ⟨fr.region, by simp only [List.mem_cons, true_or], Nat.le_refl _, Nat.le_refl _⟩)
      exact hstart.trans decodeFrame hTotalWithin
    have hDecodedTop (k : Nat) (hk : k ≤ 72) :
        memLoad decoded.store (fr.rsp - BitVec.ofNat 64 k) 64 =
          memLoad mem (fr.rsp - BitVec.ofNat 64 k) 64 := by
      have hi := hTop k hk
      have ho := output_slot_outside (by omega : fr.low.toNat + 72 ≤ fr.rsp.toNat)
        hSpBound hsep k hk
      have hout : Outside [areas[0]'(by change 0 < 3; decide), span fr.rdi 16]
          (fr.rsp - BitVec.ofNat 64 k) 8 := by
        refine ⟨hi.1, ?_⟩
        intro r hr
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl
        · exact hi.2 _ (by simp only [areas, List.getElem_cons_zero, List.mem_cons, true_or])
        · exact ho.2 _ (by simp only [List.mem_singleton])
      exact (decodeFrame.memLoad_eq hout).trans (internal2.memLoad_eq hi)
    have hFinalRet : memLoad decoded.store fr.rsp 64 = fr.ret := by
      have ht := hDecodedTop 0 (by decide)
      simp only [BitVec.ofNat_eq_ofNat, BitVec.sub_zero] at ht
      exact ht.trans hRet
    have hStackDecoded := (hStack.of_frame internal2).of_frame decodeFrame
    have hReadDecoded := (hRetRead.of_frame internal2).of_frame decodeFrame
    have hLoads : ∀ k : Fin 7, LoadOk decoded.store
        (fr.rsp - BitVec.ofNat 64 (8 * k.val)) 8 := by
      intro k
      have hk := k.isLt
      have hc : k.val = 0 ∨ k.val = 1 ∨ k.val = 2 ∨ k.val = 3 ∨
          k.val = 4 ∨ k.val = 5 ∨ k.val = 6 := by omega
      rcases hc with hk0 | hk1 | hk2 | hk3 | hk4 | hk5 | hk6
      · rw [hk0]
        simpa only [Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.sub_zero] using
          LoadOk.of_region (a := fr.rsp) (n := 8) hReadDecoded (Nat.le_refl _) (Nat.le_refl _)
      all_goals first
        | rw [hk1]
        | rw [hk2]
        | rw [hk3]
        | rw [hk4]
        | rw [hk5]
        | rw [hk6]
      all_goals exact LoadOk.of_offsets hStackDecoded.readable (addr_sub _ _) (addr_sub _ _) (by decide)
    have hSaved : ∀ r k : Nat, (r, k) ∈ [(3, 48), (12, 40), (13, 32),
        (14, 24), (15, 16), (5, 8)] →
        memLoad decoded.store (fr.rsp - BitVec.ofNat 64 k) 64 = fr.entryReg r := by
      intro r k hr
      simp only [List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hr
      rcases hr with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ |
        ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact (hDecodedTop 48 (by decide)).trans hs3
      · exact (hDecodedTop 40 (by decide)).trans hs12
      · exact (hDecodedTop 32 (by decide)).trans hs13
      · exact (hDecodedTop 24 (by decide)).trans hs14
      · exact (hDecodedTop 16 (by decide)).trans hs15
      · exact (hDecodedTop 8 (by decide)).trans hs5
    change decoded.values[4] = ⟨64, kArgs[4].get 64 + 8⟩ ∧
      decoded.values[22] = ⟨1, 0⟩ ∧
      decoded.values[3] = ⟨64, kArgs[3].get 64⟩ ∧
      decoded.values[5] = ⟨64, kArgs[5].get 64⟩ ∧
      decoded.values[12] = ⟨64, kArgs[12].get 64⟩ ∧
      decoded.values[13] = ⟨64, kArgs[13].get 64⟩ ∧
      decoded.values[14] = ⟨64, kArgs[14].get 64⟩ ∧
      decoded.values[15] = ⟨64, kArgs[15].get 64⟩ ∧
      decoded.values[39] = ⟨32, kArgs[39].get 32⟩ ∧
      decoded.values[50] = ⟨16, kArgs[50].get 16⟩ ∧
      decoded.values[51] = ⟨16, kArgs[51].get 16⟩ ∧ True at decodeDone
    rcases decodeDone with ⟨d4, d22, d3, d5, d12, d13, d14, d15, d39, d50, d51, -⟩
    rw [k4] at d4
    change decoded.values[4] = ⟨64, fr.rsp - $cp + 8⟩ at d4
    rw [hBack] at d4
    rw [k39] at d39
    rw [k50] at d50
    rw [k51] at d51
    change decoded.values[39] = ⟨32, fr.mxcsr⟩ at d39
    change decoded.values[50] = ⟨16, fr.ftw⟩ at d50
    change decoded.values[51] = ⟨16, fr.fcw⟩ at d51
    obtain ⟨output, hEpi, hTag, hStore, hDone, hTypes⟩ :=
      finalEpilogue_runBlock $u code fr decoded.values decoded.store (by rw [d4]; rfl)
        hLoads hSaved hFinalRet hRetLow d22 decodeTypes d39 d50 d51
    have hEnd : LIR.program.Exec (dialect code)
        ⟨⟨endLabel $u, decoded.values, decoded.store⟩, []⟩ output := by
      exact .done (by simp only [Program.step, hEpi, Transfer.next])
    have hDecodeAccept : (finalContinuation (endLabel $u) (outReturn $u)).Accepts
        (dialect code) decoded.tag = true := by
      simp only [finalContinuation, StackFrame.Accepts, decodeTag]
      rfl
    have hAfterSub : LIR.program.Exec (dialect code)
        ⟨⟨keyLabel $u, subOut.values, subOut.store⟩, []⟩ output :=
      CFGCall.exec_call hKeyRun decodeExec hDecodeAccept (by
        change LIR.program.Exec (dialect code)
          ⟨⟨endLabel $u, ((finalContinuation (endLabel $u) (outReturn $u)).resume decoded).arguments,
            decoded.store⟩, []⟩ output
        rw [CFGCall.resume_arguments]
        exact hEnd)
    have hSubAccept : (finalContinuation (keyLabel $u) (subReturn $u)).Accepts
        (dialect code) subOut.tag = true := by
      simp only [finalContinuation, StackFrame.Accepts, subTag]
      rfl
    have hExec : LIR.program.Exec (dialect code)
        ⟨⟨finalLabel $u, args, mem⟩, []⟩ output :=
      CFGCall.exec_call hRowsRun subExec hSubAccept (by
        change LIR.program.Exec (dialect code)
          ⟨⟨keyLabel $u, ((finalContinuation (keyLabel $u) (subReturn $u)).resume subOut).arguments,
            subOut.store⟩, []⟩ output
        rw [CFGCall.resume_arguments]
        exact hAfterSub)
    dsimp only [activationOfValues] at decodePost
    simp only [k7, k6, Value.get_mk_setWidth, BitVec.setWidth_eq] at decodePost
    have hDecoded : Fixslice.memoryBlock decoded.store fr.rdi =
        decode (fun q ↦ memLoad kMem (fr.rsp - $buf + BitVec.ofNat 64 (2 * q.val)) 16) := decodePost
    exact ⟨output, hExec, hTag, hDone, hTypes, by rw [hStore]; exact wholeOutput,
      kMem, fr.rsp - $buf, hCipherWords, by rw [hStore]; exact hDecoded⟩
  ))
set_option maxHeartbeats 3200000 in
set_option maxRecDepth 4096 in
private theorem finish128_encoded_exec (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (key : Vector UInt8 (variant false).keyBytes) (input : Standards.NIST.AES.Block)
    (fr : Activation) (loc : LIR.lifted.Location)
    (hwrite : Writable code fr.original fr.rdi 16)
    (hsep : (callStack fr).Disjoint (span fr.rdi 16))
    (hkeysep : (callStack fr).Disjoint (span fr.rsi (16 * ((variant false).Nr + 1))))
    (hwork : WorkingState code false key fr loc)
    (hlast : FinalState false key input fr loc) :
    ∃ output : Output Value Ram Reg.count,
      LIR.program.Exec (dialect code) ⟨loc, []⟩ output ∧
      output.tag = some ⟨64, fr.ret⟩ ∧
      Atom.All code output.values output.store ((frameInfo false).doneAtoms fr) ∧
      GPRsTyped output.values ∧
      RamWriteFrame fr.original output.store [fr.region, span fr.rdi 16] ∧
      ∃ (before : Ram) (src : BitVec 64),
        WordsAt before src 16 (Vector.ofFn (encodeStandard (cipher (variant false) key input))) ∧
        Fixslice.memoryBlock output.store fr.rdi =
          decode (fun q ↦ memLoad before (src + BitVec.ofNat 64 (2 * q.val)) 16) := by
  rcases loc with ⟨lab, args, mem⟩
  have hl := hlast.label
  change lab = .l105636 at hl
  subst lab
  change Values Value Reg.count at args
  final_proof false, 352, 104, 112, 104, 0, 40, 48, 64, 176, 160, 0x105735, 0x1057ae, 0x201398

set_option maxHeartbeats 3200000 in
set_option maxRecDepth 4096 in
private theorem finish256_encoded_exec (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (key : Vector UInt8 (variant true).keyBytes) (input : Standards.NIST.AES.Block)
    (fr : Activation) (loc : LIR.lifted.Location)
    (hwrite : Writable code fr.original fr.rdi 16)
    (hsep : (callStack fr).Disjoint (span fr.rdi 16))
    (hkeysep : (callStack fr).Disjoint (span fr.rsi (16 * ((variant true).Nr + 1))))
    (hwork : WorkingState code true key fr loc)
    (hlast : FinalState true key input fr loc) :
    ∃ output : Output Value Ram Reg.count,
      LIR.program.Exec (dialect code) ⟨loc, []⟩ output ∧
      output.tag = some ⟨64, fr.ret⟩ ∧
      Atom.All code output.values output.store ((frameInfo true).doneAtoms fr) ∧
      GPRsTyped output.values ∧
      RamWriteFrame fr.original output.store [fr.region, span fr.rdi 16] ∧
      ∃ (before : Ram) (src : BitVec 64),
        WordsAt before src 16 (Vector.ofFn (encodeStandard (cipher (variant true) key input))) ∧
        Fixslice.memoryBlock output.store fr.rdi =
          decode (fun q ↦ memLoad before (src + BitVec.ofNat 64 (2 * q.val)) 16) := by
  rcases loc with ⟨lab, args, mem⟩
  have hl := hlast.label
  change lab = .l106ebc at hl
  subst lab
  change Values Value Reg.count at args
  final_proof true, 368, 120, 128, 112, 8, 48, 64, 72, 240, 224, 0x106fbe, 0x107038, 0x2013a8

set_option maxHeartbeats 1600000 in
theorem finish (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (key : Vector UInt8 (variant use256).keyBytes) (input : Standards.NIST.AES.Block)
    (fr : Activation) (loc : LIR.lifted.Location)
    (hwrite : Writable code fr.original fr.rdi 16)
    (hsep : (callStack fr).Disjoint (span fr.rdi 16))
    (hkeysep : (callStack fr).Disjoint (span fr.rsi (16 * ((variant use256).Nr + 1))))
    (hwork : WorkingState code use256 key fr loc)
    (hlast : FinalState use256 key input fr loc) :
    ∃ output : Output Value Ram Reg.count,
      LIR.program.Exec (dialect code) ⟨loc, []⟩ output ∧ Result code use256 key input fr output := by
  have hrun : ∃ output : Output Value Ram Reg.count,
      LIR.program.Exec (dialect code) ⟨loc, []⟩ output ∧
      output.tag = some ⟨64, fr.ret⟩ ∧
      Atom.All code output.values output.store ((frameInfo use256).doneAtoms fr) ∧
      GPRsTyped output.values ∧
      RamWriteFrame fr.original output.store [fr.region, span fr.rdi 16] ∧
      ∃ (before : Ram) (src : BitVec 64),
        WordsAt before src 16 (Vector.ofFn (encodeStandard (cipher (variant use256) key input))) ∧
        Fixslice.memoryBlock output.store fr.rdi =
          decode (fun q ↦ memLoad before (src + BitVec.ofNat 64 (2 * q.val)) 16) := by
    cases use256
    · exact finish128_encoded_exec code hcode key input fr loc hwrite hsep hkeysep hwork hlast
    · exact finish256_encoded_exec code hcode key input fr loc hwrite hsep hkeysep hwork hlast
  obtain ⟨output, hExec, hTag, hDone, hTypes, hFrame, before, src, hWords, hDecode⟩ := hrun
  refine ⟨output, hExec, hTag, hDone, hTypes, hFrame, ?_⟩
  exact decode_memory_words (cipher (variant use256) key input)
    (before := before) (after := output.store) (src := src) (dst := fr.rdi) hWords hDecode

end AesGcm.Proofs.Machine.AES16.Encrypt
