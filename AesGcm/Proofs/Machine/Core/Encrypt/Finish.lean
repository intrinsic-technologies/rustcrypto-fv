import AesGcm.Proofs.Machine.Runtime.Tactics
import AesGcm.Proofs.Machine.LIR.Program
import AesGcm.Proofs.Machine.LIR.Fn102520.Frame
import AesGcm.Proofs.Machine.LIR.Fn102980.Frame

namespace AesGcm.Proofs.Machine.Core.Encrypt

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

set_option maxRecDepth 2048 in
set_option maxHeartbeats 1600000 in
theorem exit_runBlock (use256 : Bool) (code : CodeMap)
    (args : Values Value Reg.count) (mem : Ram)
    (hr : Readable mem (args[4].get 64 + 152) 56)
    (hret : (memLoad mem (args[4].get 64 + 200) 64).toNat < 2^32) :
    ∃ output,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l102b6a else .l10270a), args, mem⟩ = .returned output ∧
      output.store = mem ∧
      output.tag = some ⟨64, memLoad mem (args[4].get 64 + 200) 64⟩ ∧
      output.values[4] = ⟨64, args[4].get 64 + 208⟩ ∧
      output.values[0] = ⟨64, args[3].get 64⟩ ∧
      output.values[3] = ⟨64, memLoad mem (args[4].get 64 + 152) 64⟩ ∧
      output.values[12] = ⟨64, memLoad mem (args[4].get 64 + 160) 64⟩ ∧
      output.values[13] = ⟨64, memLoad mem (args[4].get 64 + 168) 64⟩ ∧
      output.values[14] = ⟨64, memLoad mem (args[4].get 64 + 176) 64⟩ ∧
      output.values[15] = ⟨64, memLoad mem (args[4].get 64 + 184) 64⟩ ∧
      output.values[5] = ⟨64, memLoad mem (args[4].get 64 + 192) 64⟩ ∧
      (∀ r : Fin 53, r.val ∈ [22, 39, 50, 51] → output.values[r] = args[r]) ∧
      (GPRsTyped args → GPRsTyped output.values) := by
  cases use256
  all_goals
    refine ⟨?_, ?exec, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    case exec =>
      first
        | change LIR.program.runBlock (dialect code) ⟨.l10270a, args, mem⟩ = _
        | change LIR.program.runBlock (dialect code) ⟨.l102b6a, args, mem⟩ = _
      cfg_eval []
      refine_norm []
      runtime_guards returned
      rfl
    all_goals first
      | rfl
      | (intro hTypes; runtime_typed)
      | (rintro ⟨r, hr⟩ hin; simp only [List.mem_cons, List.not_mem_nil, or_false] at hin;
          rcases hin with rfl | rfl | rfl | rfl <;> rfl)
      | runtime_finish []

set_option maxHeartbeats 800000 in
theorem success_runBlock (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code) (args : Values Value Reg.count) (mem : Ram)
    (hw : Writable code mem (args[3].get 64) 1) :
    ∃ next,
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l102b67 else .l102707), args, mem⟩ = .jump next ∧
      next.label = (if use256 then .l102b6a else .l10270a) ∧
      next.store = memStore mem (args[3].get 64) (0#8) ∧
      (∀ r : Fin 53, r.val ∈ [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 22, 39, 50, 51] →
        next.arguments[r] = args[r]) ∧
      (GPRsTyped args → GPRsTyped next.arguments) := by
  have hhelperApart {m : Ram} {a : BitVec 64} {n : Nat}
      (h : Writable code m a n) :
      RangeApart a n (if use256 then 0x102b67 else 0x102707) 3 := by
    cases use256
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l102707 x hx))).apart
    · exact (storeOk_of_codeRange h (fun x hx ↦ hcode x (LIR.code_l102b67 x hx))).apart
  cases use256
  all_goals simp only [Bool.false_eq_true, ↓reduceIte] at hhelperApart ⊢
  all_goals
    refine ⟨?_, ?exec, ?_, ?_, ?_, ?_⟩
    case exec =>
      first
        | change LIR.program.runBlock (dialect code) ⟨.l102707, args, mem⟩ = _
        | change LIR.program.runBlock (dialect code) ⟨.l102b67, args, mem⟩ = _
      cfg_eval []
      refine_norm []
      runtime_guards transfer
      rfl
    all_goals first
      | rfl
      | (intro hTypes; runtime_typed)
      | (rintro ⟨r, hr⟩ hin; simp only [List.mem_cons, List.not_mem_nil, or_false] at hin;
          rcases hin with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
            rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
      | runtime_finish []

theorem return_exec (use256 : Bool) (code : CodeMap)
    (fr : Activation) (args : Values Value Reg.count) (mem : Ram)
    (hsp : args[4].get 64 = fr.rsp - 200)
    (hread : Readable mem (fr.rsp - 48) 56)
    (hreturn : memLoad mem fr.rsp 64 = fr.ret)
    (hlow : fr.ret.toNat < 2^32)
    (hsaved : memLoad mem (fr.rsp - 48) 64 = fr.rbx ∧
      memLoad mem (fr.rsp - 40) 64 = fr.r12 ∧
      memLoad mem (fr.rsp - 32) 64 = fr.r13 ∧
      memLoad mem (fr.rsp - 24) 64 = fr.r14 ∧
      memLoad mem (fr.rsp - 16) 64 = fr.r15 ∧
      memLoad mem (fr.rsp - 8) 64 = fr.rbp)
    (hdf : args[22] = ⟨1, 0⟩)
    (h39 : args[39] = ⟨32, fr.mxcsr⟩)
    (h50 : args[50] = ⟨16, fr.ftw⟩)
    (h51 : args[51] = ⟨16, fr.fcw⟩)
    (hTypes : GPRsTyped args) :
    ∃ output,
      LIR.program.Exec (dialect code)
        ⟨⟨(if use256 then .l102b6a else .l10270a), args, mem⟩, []⟩ output ∧
      output.store = mem ∧ output.tag = some ⟨64, fr.ret⟩ ∧
      Atom.All code output.values output.store
        ((if use256 then LIR.Fn102980.frameInfo else LIR.Fn102520.frameInfo).doneAtoms fr) ∧
      output.values[0] = ⟨64, args[3].get 64⟩ ∧ GPRsTyped output.values := by
  have hsum : args[4].get 64 + 200 = fr.rsp := by rw [hsp]; bv_omega
  have hstart : args[4].get 64 + 152 = fr.rsp - 48 := by rw [hsp]; bv_omega
  obtain ⟨output, hrun, hmem, htag, h4, h0, h3, h12, h13, h14, h15, h5,
      hkeep, htypes⟩ := exit_runBlock use256 code args mem
        (by rw [hstart]; exact hread) (by rw [hsum, hreturn]; exact hlow)
  rcases hsaved with ⟨hs3, hs12, hs13, hs14, hs15, hs5⟩
  have h4' : output.values[4] = ⟨64, fr.rsp + 8⟩ := by
    rw [h4, hsp]
    congr 1
    bv_omega
  have h3' : output.values[3] = ⟨64, fr.rbx⟩ := by rw [h3, hstart, hs3]
  have h12' : output.values[12] = ⟨64, fr.r12⟩ := by
    rw [h12, hsp, show fr.rsp - 200 + 160 = fr.rsp - 40 by bv_omega, hs12]
  have h13' : output.values[13] = ⟨64, fr.r13⟩ := by
    rw [h13, hsp, show fr.rsp - 200 + 168 = fr.rsp - 32 by bv_omega, hs13]
  have h14' : output.values[14] = ⟨64, fr.r14⟩ := by
    rw [h14, hsp, show fr.rsp - 200 + 176 = fr.rsp - 24 by bv_omega, hs14]
  have h15' : output.values[15] = ⟨64, fr.r15⟩ := by
    rw [h15, hsp, show fr.rsp - 200 + 184 = fr.rsp - 16 by bv_omega, hs15]
  have h5' : output.values[5] = ⟨64, fr.rbp⟩ := by
    rw [h5, hsp, show fr.rsp - 200 + 192 = fr.rsp - 8 by bv_omega, hs5]
  refine ⟨output, .done ?_, hmem, ?_, ?_, h0, htypes hTypes⟩
  · change (LIR.program.runBlock (dialect code) _).next (dialect code) [] = .done output
    rw [hrun]
    rfl
  · rw [htag, hsum, hreturn]
  · have hd : Atom.All code output.values output.store (LIR.Fn102520.frameInfo.doneAtoms fr) := by
      exact ⟨h4', (hkeep 22 (by decide)).trans hdf, h3', h5', h12', h13', h14', h15',
        (hkeep 39 (by decide)).trans h39, (hkeep 50 (by decide)).trans h50,
        (hkeep 51 (by decide)).trans h51, trivial⟩
    cases use256 <;> exact hd

set_option maxHeartbeats 800000 in
theorem success_exec (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (fr : Activation) (args : Values Value Reg.count) (mem : Ram)
    (hsp : args[4].get 64 = fr.rsp - 200)
    (hresult : args[3].get 64 = fr.rdi)
    (hw : Writable code mem fr.rdi 1)
    (hread : Readable mem (fr.rsp - 48) 56)
    (hapart : fr.rdi.toNat + 1 ≤ (fr.rsp - 48).toNat ∨
      (fr.rsp - 48).toNat + 56 ≤ fr.rdi.toNat)
    (hreturn : memLoad mem fr.rsp 64 = fr.ret)
    (hlow : fr.ret.toNat < 2^32)
    (hsaved : memLoad mem (fr.rsp - 48) 64 = fr.rbx ∧
      memLoad mem (fr.rsp - 40) 64 = fr.r12 ∧
      memLoad mem (fr.rsp - 32) 64 = fr.r13 ∧
      memLoad mem (fr.rsp - 24) 64 = fr.r14 ∧
      memLoad mem (fr.rsp - 16) 64 = fr.r15 ∧
      memLoad mem (fr.rsp - 8) 64 = fr.rbp)
    (hdf : args[22] = ⟨1, 0⟩)
    (h39 : args[39] = ⟨32, fr.mxcsr⟩)
    (h50 : args[50] = ⟨16, fr.ftw⟩)
    (h51 : args[51] = ⟨16, fr.fcw⟩)
    (hTypes : GPRsTyped args) :
    ∃ output,
      LIR.program.Exec (dialect code)
        ⟨⟨(if use256 then .l102b67 else .l102707), args, mem⟩, []⟩ output ∧
      output.store = memStore mem fr.rdi (0#8) ∧ output.tag = some ⟨64, fr.ret⟩ ∧
      Atom.All code output.values output.store
        ((if use256 then LIR.Fn102980.frameInfo else LIR.Fn102520.frameInfo).doneAtoms fr) ∧
      output.values[0] = ⟨64, fr.rdi⟩ ∧ GPRsTyped output.values ∧
      RamWriteFrame mem output.store [span fr.rdi 1] ∧ output.store[fr.rdi]? = some 0 := by
  obtain ⟨next, hstep, hlabel, hmem, keep, typed⟩ :=
    success_runBlock use256 code hcode args mem (by rw [hresult]; exact hw)
  rw [hresult] at hmem
  have nsp : next.arguments[4]'(by change 4 < 53; decide) = args[4] := keep 4 (by decide)
  have nr : next.arguments[3]'(by change 3 < 53; decide) = args[3] := keep 3 (by decide)
  have hs := hread.low
  have hwlow := hw.readable.low
  rcases hsaved with ⟨hs3, hs12, hs13, hs14, hs15, hs5⟩
  have hret' : memLoad (memStore mem fr.rdi (0#8)) fr.rsp 64 = fr.ret := by
    runtime_finish []
  have hsave' : memLoad (memStore mem fr.rdi (0#8)) (fr.rsp - 48) 64 = fr.rbx ∧
      memLoad (memStore mem fr.rdi (0#8)) (fr.rsp - 40) 64 = fr.r12 ∧
      memLoad (memStore mem fr.rdi (0#8)) (fr.rsp - 32) 64 = fr.r13 ∧
      memLoad (memStore mem fr.rdi (0#8)) (fr.rsp - 24) 64 = fr.r14 ∧
      memLoad (memStore mem fr.rdi (0#8)) (fr.rsp - 16) 64 = fr.r15 ∧
      memLoad (memStore mem fr.rdi (0#8)) (fr.rsp - 8) 64 = fr.rbp := by
    repeat' apply And.intro
    all_goals runtime_finish []
  obtain ⟨output, hexec, hm, ht, hd, h0, htyped⟩ := return_exec use256 code fr next.arguments
    (memStore mem fr.rdi (0#8)) (by rw [nsp]; exact hsp) (hread.memStore _ _)
    hret' hlow hsave' ((keep 22 (by decide)).trans hdf)
    ((keep 39 (by decide)).trans h39) ((keep 50 (by decide)).trans h50)
    ((keep 51 (by decide)).trans h51) (typed hTypes)
  refine ⟨output, ?_, hm, ht, hd, ?_, htyped, ?_, ?_⟩
  · apply Program.Exec.next (next := ⟨next, []⟩)
    · simp only [Program.step, hstep, Transfer.next]
    · have hloc : next =
          ⟨(if use256 then .l102b6a else .l10270a), next.arguments, memStore mem fr.rdi (0#8)⟩ := by
        cases next with
        | mk label arguments store =>
          dsimp only at hlabel hmem ⊢
          subst label store
          rfl
      rw [hloc]
      exact hexec
  · rw [h0, nr, hresult]
  · rw [hm]
    runtime_finish [span]
  · rw [hm]
    have hb := memStore_getElem?_self mem fr.rdi (0#8) (by decide) 0 (by decide)
    change (memStore mem fr.rdi (0#8))[fr.rdi + 0]? = some 0 at hb
    have he : fr.rdi + 0 = fr.rdi := by bv_omega
    rw [he] at hb
    exact hb

end AesGcm.Proofs.Machine.Core.Encrypt
