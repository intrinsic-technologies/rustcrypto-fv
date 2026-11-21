import AesGcm.Proofs.Machine.LIR.Fn1034a0.Frame
import AesGcm.Proofs.Machine.LIR.Program
import AesGcm.Proofs.Machine.Runtime.Tactics

namespace AesGcm.Proofs.Machine.Tag

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

def finalizeRam (mem : Ram) (dst src : BitVec 64) : Ram :=
  memStore (memStore mem (dst + 8) (memLoad mem (src + 24) 64)) dst
    (memLoad mem (src + 16) 64)

theorem finalize_runBlock (code : CodeMap) (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (args : Values Value Reg.count) (mem : Ram)
    (hr : Readable mem (args[6].get 64 + 16) 16)
    (hw : Writable code mem (args[7].get 64) 16)
    (hret : LoadOk (finalizeRam mem (args[7].get 64) (args[6].get 64)) (args[4].get 64) 8 ∧
      (memLoad (finalizeRam mem (args[7].get 64) (args[6].get 64))
        (args[4].get 64) 64).toNat < 2^32) :
    ∃ output,
      LIR.program.runBlock (dialect code) ⟨.l1034a0, args, mem⟩ = .returned output ∧
      output.store = finalizeRam mem (args[7].get 64) (args[6].get 64) ∧
      output.tag = some ⟨64, memLoad output.store (args[4].get 64) 64⟩ ∧
      output.values[4] = ⟨64, args[4].get 64 + 8⟩ ∧
      (∀ r : Fin 53, r.val ∈ [3, 5, 12, 13, 14, 15, 22, 39, 50, 51] →
        output.values[r] = args[r]) ∧
      (GPRsTyped args → GPRsTyped output.values) := by
  rcases hret with ⟨hretRead, hretLow⟩
  have hhelperApart {m : Ram} {a : BitVec 64} {n : Nat}
      (h : Writable code m a n) : RangeApart a n 0x1034a0 19 :=
    (storeOk_of_codeRange h (fun x hx => hcode x (LIR.code_l1034a0 x hx))).apart
  refine ⟨?_, ?exec, ?_, ?_, ?_, ?_, ?_⟩
  case exec =>
    cfg_eval []
    simp only [finalizeRam, BitVec.ofNat_eq_ofNat] at hretRead hretLow
    simp only [BitVec.ofNat_eq_ofNat, hretRead, hretLow]
    runtime_guards returned
    rfl
  · rfl
  · rfl
  · rfl
  · rintro ⟨r, hr⟩ hin
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl
  · intro hTypes
    runtime_typed

theorem finalizeRam_frame (mem : Ram) (dst src : BitVec 64)
    (hw : Readable mem dst 16) :
    RamWriteFrame mem (finalizeRam mem dst src) [span dst 16] := by
  have hlow := hw.low
  unfold finalizeRam
  runtime_finish [span]

theorem finalizeRam_words (mem : Ram) (dst src : BitVec 64)
    (hw : Readable mem dst 16) :
    memLoad (finalizeRam mem dst src) dst 64 = memLoad mem (src + 16) 64 ∧
    memLoad (finalizeRam mem dst src) (dst + 8) 64 = memLoad mem (src + 24) 64 := by
  have hlow := hw.low
  unfold finalizeRam
  constructor <;> runtime_finish []


theorem finalize_call (code : CodeMap) (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) :
    CallContract LIR.lifted code .l1034a0 LIR.Fn1034a0.frameInfo
      (fun fr ↦ [span fr.rdi 16])
      (fun fr mem ↦ Readable mem (fr.rsi + 16) 16 ∧ Writable code mem fr.rdi 16 ∧
        RangeApart fr.rsp 8 fr.rdi 16)
      (fun fr mem ↦ memLoad mem fr.rdi 64 = memLoad fr.original (fr.rsi + 16) 64 ∧
        memLoad mem (fr.rdi + 8) 64 = memLoad fr.original (fr.rsi + 24) 64) := by
  intro fr loc hlabel hmem hentry htypes hpre
  rcases loc with ⟨label, args, mem⟩
  dsimp only at hlabel hmem hentry htypes hpre
  subst label
  subst mem
  change args[4] = ⟨64, fr.rsp⟩ ∧ args[22] = ⟨1, 0⟩ ∧ args[1] = ⟨64, fr.rcx⟩ ∧
    args[2] = ⟨64, fr.rdx⟩ ∧ args[3] = ⟨64, fr.rbx⟩ ∧ args[5] = ⟨64, fr.rbp⟩ ∧
    args[6] = ⟨64, fr.rsi⟩ ∧ args[7] = ⟨64, fr.rdi⟩ ∧ args[8] = ⟨64, fr.r8⟩ ∧
    args[9] = ⟨64, fr.r9⟩ ∧ args[12] = ⟨64, fr.r12⟩ ∧ args[13] = ⟨64, fr.r13⟩ ∧
    args[14] = ⟨64, fr.r14⟩ ∧ args[15] = ⟨64, fr.r15⟩ ∧
    args[39] = ⟨32, fr.mxcsr⟩ ∧ args[50] = ⟨16, fr.ftw⟩ ∧ args[51] = ⟨16, fr.fcw⟩ ∧
    Readable fr.original fr.rsp 8 ∧ memLoad fr.original fr.rsp 64 = fr.ret ∧
    fr.ret.toNat < 2^32 ∧ fr.low.toNat ≤ fr.rsp.toNat ∧ fr.rsp.toNat % 16 = 8 ∧ True at hentry
  rcases hentry with ⟨hsp, hdf, -, -, hbx, hbp, hsrc, hdst, -, -, h12, h13, h14, h15, h39, h50, h51,
    hreturnRead, hreturnValue, hretlow, -, -, -⟩
  rcases hpre with ⟨hr, hw, hapret⟩
  have hreturn : memLoad (finalizeRam fr.original fr.rdi fr.rsi) fr.rsp 64 = fr.ret := by
    unfold finalizeRam
    rw [memLoad_memStore_of_rangeApart _ _ _ _ 64 (by
      intro i hi j hj he
      exact hapret j hj i (by omega) he.symm),
      memLoad_memStore_of_rangeApart _ _ _ _ 64 (by
        intro i hi j hj he
        apply hapret j hj (8 + i) (by omega)
        simpa only [BitVec.add_assoc, BitVec.ofNat_add, BitVec.ofNat_eq_ofNat] using he.symm),
      hreturnValue]
  have hread : Readable (finalizeRam fr.original fr.rdi fr.rsi) fr.rsp 8 := by
    exact (hreturnRead.memStore (fr.rdi + 8) (memLoad fr.original (fr.rsi + 24) 64)).memStore
      fr.rdi (memLoad fr.original (fr.rsi + 16) 64)
  have hgetsp : args[4].get 64 = fr.rsp := by rw [hsp]; rfl
  have hgetsrc : args[6].get 64 = fr.rsi := by rw [hsrc]; rfl
  have hgetdst : args[7].get 64 = fr.rdi := by rw [hdst]; rfl
  obtain ⟨output, hblock, hstore, htag, ho4, hpres, hotypes⟩ :=
    finalize_runBlock code hcode args fr.original
      (by rw [hgetsrc]; exact hr) (by rw [hgetdst]; exact hw)
      (by rw [hgetsrc, hgetdst, hgetsp]; exact ⟨⟨hread.low, hread.present⟩, by rw [hreturn]; exact hretlow⟩)
  rw [hgetsrc, hgetdst] at hstore
  refine ⟨output, .done ?_, ?_, ?_, hotypes htypes, ?_, ?_⟩
  · change (LIR.program.runBlock (dialect code)
      ⟨.l1034a0, args, fr.original⟩).next (dialect code) [] = .done output
    rw [hblock]
    rfl
  · rw [htag, hstore, hgetsp, hreturn]
  · change output.values[4] = ⟨64, fr.rsp + 8⟩ ∧ output.values[22] = ⟨1, 0⟩ ∧
      output.values[3] = ⟨64, fr.rbx⟩ ∧ output.values[5] = ⟨64, fr.rbp⟩ ∧
      output.values[12] = ⟨64, fr.r12⟩ ∧ output.values[13] = ⟨64, fr.r13⟩ ∧
      output.values[14] = ⟨64, fr.r14⟩ ∧ output.values[15] = ⟨64, fr.r15⟩ ∧
      output.values[39] = ⟨32, fr.mxcsr⟩ ∧ output.values[50] = ⟨16, fr.ftw⟩ ∧
      output.values[51] = ⟨16, fr.fcw⟩ ∧ True
    refine ⟨?_, (hpres 22 (by decide)).trans hdf, (hpres 3 (by decide)).trans hbx,
      (hpres 5 (by decide)).trans hbp, (hpres 12 (by decide)).trans h12,
      (hpres 13 (by decide)).trans h13, (hpres 14 (by decide)).trans h14,
      (hpres 15 (by decide)).trans h15, (hpres 39 (by decide)).trans h39,
      (hpres 50 (by decide)).trans h50, (hpres 51 (by decide)).trans h51, trivial⟩
    simpa only [hgetsp] using ho4
  · rw [hstore]
    have hf := finalizeRam_frame fr.original fr.rdi fr.rsi hw.readable
    exact ⟨fun x hx ↦ hf.outside x ⟨hx.1, fun r hr ↦ hx.2 r (List.mem_cons_of_mem _ hr)⟩,
      hf.present⟩
  · rw [hstore]
    exact finalizeRam_words fr.original fr.rdi fr.rsi hw.readable

end AesGcm.Proofs.Machine.Tag
