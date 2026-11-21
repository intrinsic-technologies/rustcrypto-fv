import AesGcm.Proofs.Machine.CTR.BatchKey1
import AesGcm.Proofs.Machine.Fixslice.Linear
namespace AesGcm.Proofs.Machine.CTR
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime Fixslice

theorem shiftRowsWord2_native (x : BitVec 64) :
    (((((x >>> 8) ^^^ x) &&& 0x00ff000000ff0000) <<< 8) +
      (((x >>> 8) ^^^ x) &&& 0x00ff000000ff0000)) ^^^ x = shiftRowsWord2 x := by
  let t := ((x >>> 8) ^^^ x) &&& 0x00ff000000ff0000
  have hd : (t <<< 8) &&& t = 0 := by
    dsimp only [t]
    rw [BitVec.shiftLeft_and_distrib]
    calc
      _ = ((((x >>> 8) ^^^ x) <<< 8) &&& ((x >>> 8) ^^^ x)) &&&
        (((0x00ff000000ff0000#64) <<< 8) &&& 0x00ff000000ff0000) := by ac_rfl
      _ = 0 := by rw [show (((0x00ff000000ff0000#64) <<< 8) &&& 0x00ff000000ff0000) = 0 by decide]; exact BitVec.and_zero
  simp only [shiftRowsWord2, deltaSwap1, BitVec.xor_comm x (x >>> 8)]
  change ((t <<< 8) + t) ^^^ x = x ^^^ t ^^^ (t <<< 8)
  rw [BitVec.add_eq_or_of_and_eq_zero _ _ hd]
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  have hh := congrArg (fun b : BitVec 64 => b.getLsbD i) hd
  simp only [BitVec.getLsbD_and] at hh
  simp only [BitVec.getLsbD_xor, BitVec.getLsbD_or]
  cases ha : (t <<< 8).getLsbD i <;> cases hb : t.getLsbD i <;> cases hc : x.getLsbD i <;> simp_all

def batchFinalRowsFrame (use256 : Bool) : StackFrame Value LIR.Label signature Reg.count :=
  { target := if use256 then .l108728 else .l107298, kept := #v[], arity := rfl,
    guard := some ⟨64, if use256 then 0x108728 else 0x107298⟩ }

set_option maxRecDepth 2048 in
set_option maxHeartbeats 2400000 in
theorem batch_final_rows (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (args : Values Value Reg.count) (mem : Ram) (sp count : BitVec 64) (planes : Planes)
    (hTypes : GPRsTyped args) (hsp : args[4].get 64 = sp)
    (hStack : Writable code mem (sp - 8) 240)
    (hCount : memLoad mem (sp + 224) 64 = count)
    (hRegs : ∀ p : Fin 8, (args[batchPlaneRegister p]).get 64 = planes p) :
    ∃ callee : LIR.lifted.Location,
      LIR.program.runBlock (dialect code) ⟨(if use256 then .l108600 else .l107170), args, mem⟩ =
        .call callee (batchFinalRowsFrame use256) ∧
      callee.label = .l100e90 ∧
      callee.arguments[4]'(by change 4 < 53; decide) = ⟨64, sp - 8⟩ ∧
      callee.arguments[7]'(by change 7 < 53; decide) = ⟨64, sp + 8⟩ ∧
      callee.arguments[3]'(by change 3 < 53; decide) = ⟨64, sp + 8⟩ ∧
      callee.arguments[6]'(by change 6 < 53; decide) = ⟨64, 8⟩ ∧
      callee.arguments[5]'(by change 5 < 53; decide) = ⟨64, count <<< 6⟩ ∧
      WordsAt callee.store (sp + 8) 64 (Vector.ofFn (shiftRows2 planes)) ∧
      memLoad callee.store (sp + 224) 64 = count ∧
      memLoad callee.store (sp - 8) 64 = (if use256 then 0x108728 else 0x107298) ∧
      (∀ r : Fin 53, r.val ∈ [12,13,15,22,39,50,51] → callee.arguments[r] = args[r]) ∧
      GPRsTyped callee.arguments ∧
      RamWriteFrame mem callee.store [span (sp - 8) 8, span (sp + 8) 64, span (sp + 224) 8] := by
  have hStackRead := hStack.readable
  have hStackLow := hStackRead.low
  have h0 := hRegs 0
  have h1 := hRegs 1
  have h2 := hRegs 2
  have h3 := hRegs 3
  have h4 := hRegs 4
  have h5 := hRegs 5
  have h6 := hRegs 6
  have h7 := hRegs 7
  simp only [batchPlaneRegister] at h0 h1 h2 h3 h4 h5 h6 h7
  runtime_context [hsp, hCount, h0, h1, h2, h3, h4, h5, h6, h7]
  have hRange {m : Ram} {a : BitVec 64} {n : Nat}
      (h : Writable code m a n) : RangeApart a n
        (if use256 then 0x108600 else 0x107170) 296 := by
    cases use256
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l107170 x hx))).apart
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l108600 x hx))).apart
  cases use256
  all_goals
    have hhelperApart := @hRange
    simp only [Bool.false_eq_true, ↓reduceIte] at hhelperApart
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    rotate_left
    · first
      | change LIR.program.runBlock (dialect code) ⟨.l107170, args, mem⟩ = _
      | change LIR.program.runBlock (dialect code) ⟨.l108600, args, mem⟩ = _
      cfg_eval [LIR.program, batchFinalRowsFrame, hsp]
      runtime_guards call
      rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · runtime_finish [hCount]
      all_goals rfl
    · intro i hi
      rw [Vector.getElem_ofFn]
      change memLoad (_ : Ram) ((sp + 8) + BitVec.ofNat 64 (8 * i)) 64 = shiftRowsWord2 (planes ⟨i, hi⟩)
      have he : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 := by omega
      rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      runtime_finish_all [wordAddr, Nat.reduceMul, BitVec.add_assoc, BitVec.reduceAdd, shiftRowsWord2_native]
      all_goals first | exact congrArg shiftRowsWord2 h0 | exact congrArg shiftRowsWord2 h1 | exact congrArg shiftRowsWord2 h2 | exact congrArg shiftRowsWord2 h3 | exact congrArg shiftRowsWord2 h4 | exact congrArg shiftRowsWord2 h5 | exact congrArg shiftRowsWord2 h6 | exact congrArg shiftRowsWord2 h7
    · runtime_finish [hCount]
      all_goals rfl
    · exact memLoad_memStore_eq _ _ rfl (by decide) (by decide)
    · rintro ⟨r, hr⟩ hin
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
      rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
    · runtime_typed
    · runtime_finish [span]
end AesGcm.Proofs.Machine.CTR
