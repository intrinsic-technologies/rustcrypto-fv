import AesGcm.Proofs.Machine.Runtime.Tactics
import AesGcm.Proofs.Machine.Runtime.StackGeometry
import AesGcm.Proofs.Machine.Runtime.MemorySlices
import AesGcm.Proofs.Machine.LIR.Fn107050.Frame
import AesGcm.Proofs.Machine.LIR.Fn1084e0.Frame

namespace AesGcm.Proofs.Machine.CTR
open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 4096 in
theorem return_runBlock (use256 : Bool) (code : CodeMap)
    (fr : Activation) (args : Values Value Reg.count) (mem : Ram)
    (hsp : args[4].get 64 = fr.rsp - (if use256 then 2312 else 1800))
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
      LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l109961 else .l1084c1), args, mem⟩ = .returned output ∧
      output.store = mem ∧ output.tag = some ⟨64, fr.ret⟩ ∧
      Atom.All code output.values output.store
        ((if use256 then LIR.Fn1084e0.frameInfo else LIR.Fn107050.frameInfo).doneAtoms fr) ∧
      GPRsTyped output.values := by
  rcases hsaved with ⟨hs3, hs12, hs13, hs14, hs15, hs5⟩
  have hreadLow := hread.low
  cases use256
  all_goals
    simp only [Bool.false_eq_true, ↓reduceIte] at hsp ⊢
    runtime_context [hsp, hreturn, hs3, hs12, hs13, hs14, hs15, hs5]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    rotate_left
    · first
      | change LIR.program.runBlock (dialect code) ⟨.l1084c1, args, mem⟩ = _
      | change LIR.program.runBlock (dialect code) ⟨.l109961, args, mem⟩ = _
      cfg_eval [LIR.program, hsp]
      runtime_guards returned
      rfl
    · rfl
    · runtime_finish []
    · change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ True
      refine ⟨?_, hdf, ?_, ?_, ?_, ?_, ?_, ?_, h39, h50, h51, trivial⟩
      all_goals runtime_finish []
      all_goals rfl
    · runtime_typed

theorem return_of_tail (use256 : Bool) (code : CodeMap) (fr : Activation)
    (args values : Values Value Reg.count) (before after : Ram)
    (hframe : Atom.All code args before (if use256 then LIR.Fn1084e0.frameAt .l109509 fr
      else LIR.Fn107050.frameAt .l10805f fr))
    (regions : List MemoryRegion) (hf : RamWriteFrame before after regions)
    (hsave : ∀ r ∈ regions, (span (fr.rsp - 48) 56).Disjoint r)
    (hkeep : ∀ r : Fin 53, r.val ∈ [4,22,39,50,51] → values[r] = args[r])
    (ht : GPRsTyped values) :
    ∃ output, LIR.program.runBlock (dialect code)
        ⟨(if use256 then .l109961 else .l1084c1), values, after⟩ = .returned output ∧
      output.store = after ∧ output.tag = some ⟨64, fr.ret⟩ ∧
      Atom.All code output.values output.store
        ((if use256 then LIR.Fn1084e0.frameInfo else LIR.Fn107050.frameInfo).doneAtoms fr) ∧
      GPRsTyped output.values := by
  let win : Nat := if use256 then 2688 else 2160
  have facts :
      args[4] = ⟨64, fr.rsp - (if use256 then 2312 else 1800)⟩ ∧
      args[22] = ⟨1, 0⟩ ∧ args[39] = ⟨32, fr.mxcsr⟩ ∧
      args[50] = ⟨16, fr.ftw⟩ ∧ args[51] = ⟨16, fr.fcw⟩ ∧
      memLoad before (fr.rsp - 48) 64 = fr.rbx ∧ memLoad before (fr.rsp - 40) 64 = fr.r12 ∧
      memLoad before (fr.rsp - 32) 64 = fr.r13 ∧ memLoad before (fr.rsp - 24) 64 = fr.r14 ∧
      memLoad before (fr.rsp - 16) 64 = fr.r15 ∧ memLoad before (fr.rsp - 8) 64 = fr.rbp ∧
      Readable before fr.rsp 8 ∧ memLoad before fr.rsp 64 = fr.ret ∧ fr.ret.toNat < 2^32 ∧
      Writable code before (fr.rsp - BitVec.ofNat 64 win) win ∧ fr.low.toNat + win ≤ fr.rsp.toNat := by
    cases use256 <;>
      obtain ⟨a,b,c,d,e,f,g,i,j,k,l,m,n,o,p,q,_⟩ := hframe <;>
      exact ⟨a,b,c,d,e,f,g,i,j,k,l,m,n,o,p,q⟩
  obtain ⟨sp, df, mx, ftw, fcw, bx, r12, r13, r14, r15, bp, hr, ret, low, ws, room⟩ := facts
  have w48 : 48 ≤ win := by cases use256 <;> decide
  have b48 := stack_sub_toNat fr room w48
  have bw := stack_sub_toNat fr room (Nat.le_refl win)
  have rd : Readable before (fr.rsp - 48) 48 := ws.readable.sub (by change _ ≤ (fr.rsp - BitVec.ofNat 64 48).toNat; omega)
    (by change (fr.rsp - BitVec.ofNat 64 48).toNat + 48 ≤ _; omega)
  have tailRead := readable_append rd (k := 8) (by rw [show fr.rsp - 48 + BitVec.ofNat 64 48 = fr.rsp by bv_omega]; exact hr)
  have load (n : Nat) (hn : n ≤ 48) :
      memLoad after (fr.rsp - BitVec.ofNat 64 n) 64 = memLoad before (fr.rsp - BitVec.ofNat 64 n) 64 := by
    have bn := stack_sub_toNat fr room (n := n) (by omega)
    have lr := hr.low
    apply memLoad_eq_of_disjoint hf (by rw [bn]; omega)
    intro r hr' x hx
    apply hsave r hr' x
    change (fr.rsp - BitVec.ofNat 64 n).toNat ≤ x ∧ x < (fr.rsp - BitVec.ofNat 64 n).toNat + 8 at hx
    change (fr.rsp - BitVec.ofNat 64 48).toNat ≤ x ∧ x < (fr.rsp - BitVec.ofNat 64 48).toNat + 56
    omega
  apply return_runBlock use256 code fr values after _ (tailRead.of_frame hf) _ low _ _ _ _ _ ht
  · exact congrArg (Value.get 64) ((hkeep 4 (by decide)).trans sp)
  · simpa using (load 0 (by decide)).trans (by simpa using ret)
  · exact ⟨(load 48 (by decide)).trans bx, (load 40 (by decide)).trans r12,
      (load 32 (by decide)).trans r13, (load 24 (by decide)).trans r14,
      (load 16 (by decide)).trans r15, (load 8 (by decide)).trans bp⟩
  · exact (hkeep 22 (by decide)).trans df
  · exact (hkeep 39 (by decide)).trans mx
  · exact (hkeep 50 (by decide)).trans ftw
  · exact (hkeep 51 (by decide)).trans fcw

end AesGcm.Proofs.Machine.CTR
