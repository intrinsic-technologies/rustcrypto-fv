import K256.Proofs.Verify.Wrapper.Frame
import K256.Proofs.Verify.LIR.Program
import K256.Proofs.Verify.LIR.Generated.Values

namespace K256.Proofs.Verify.Wrapper

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine Verify.LIR

private theorem epilogue {s : RamState} {key message sig : ByteArray}
    {a : Vector Value 53} {m : Ram} {status : BitVec 64}
    (call : ValidCall verifyingKeyVerify s [key, message, sig]) (memory : Memory s m)
    (sp : a[4].get 64 = localSp s) (ax : a[0] = ⟨64, status⟩)
    (bp : a[5] = (Reg.ofIndex 5).read s) (r13 : a[13] = (Reg.ofIndex 13).read s)
    (df : a[22] = ⟨1, 0⟩) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l1033f9, a, m⟩, []⟩ out ∧
      Common.Returned s #v[stack s] out ∧ out.values[0] = ⟨64, status⟩ := by
  obtain ⟨ret, slot, low, _⟩ := call.returnAddress
  have target : (memLoad m (stackPtr s) 64).toNat < 2^32 := by
    have addr : (returnBoundary s).rip = ret := memLoad_returnSlot slot
    rw [memory.saved.ret, addr]
    exact low
  have read (d : Nat) (hd : d ≤ 13000) :
      LoadOk m (stackPtr s - BitVec.ofNat 64 d) 8 := by
    have w := ((Common.stackWritable (len := 8) call hd (by omega) (by decide)).readable.of_frame memory.frame)
    exact ⟨w.low, w.present⟩
  have r32 : LoadOk m (stackPtr s - 32) 8 := read 32 (by decide)
  have r24 : LoadOk m (stackPtr s - 24) 8 := read 24 (by decide)
  have r16 : LoadOk m (stackPtr s - 16) 8 := read 16 (by decide)
  have r8 : LoadOk m (stackPtr s - 8) 8 := read 8 (by decide)
  have r0 : LoadOk m (stackPtr s) 8 := by simpa using read 0 (by decide)
  have p32 : localSp s + 504 = stackPtr s - 32 := by unfold localSp; bv_omega
  have p24 : localSp s + 512 = stackPtr s - 24 := by unfold localSp; bv_omega
  have p16 : localSp s + 520 = stackPtr s - 16 := by unfold localSp; bv_omega
  have p8 : localSp s + 528 = stackPtr s - 8 := by unfold localSp; bv_omega
  have p0 : localSp s + 536 = stackPtr s := by unfold localSp; bv_omega
  have pNext : localSp s + 544 = stackPtr s + 8 := by unfold localSp; bv_omega
  have block : ∃ out, program.runBlock (dialect Extracted.programImage) ⟨.l1033f9, a, m⟩ =
      .returned out ∧ Common.Returned s #v[stack s] out ∧ out.values[0] = ⟨64, status⟩ := by
    refine ⟨?_, ?eval, ?post⟩
    case eval =>
      cfg_eval
      simp only [sp, p32, p24, p16, p8, p0, pNext, r32, r24, r16, r8, r0, target, and_self, ↓reduceIte]
      rfl
    case post =>
      refine ⟨⟨?_, rfl, df, ?_, memory.frame, congrArg Value.width ax⟩, ax⟩
      · exact congrArg (fun b => some (⟨64,b⟩ : Value)) memory.saved.ret
      · intro ⟨i, hi⟩ hm
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
        rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
        · exact congrArg (fun b => (⟨64,b⟩ : Value)) memory.saved.rbx
        · exact bp
        · exact congrArg (fun b => (⟨64,b⟩ : Value)) memory.saved.r12
        · exact r13
        · exact congrArg (fun b => (⟨64,b⟩ : Value)) memory.saved.r14
        · exact congrArg (fun b => (⟨64,b⟩ : Value)) memory.saved.r15
  obtain ⟨out, h, post⟩ := block
  exact ⟨out, .done (congrArg (Transfer.next _ []) h), post⟩

private theorem rejectCleanup {a : Vector Value 53} {m : Ram} {sp : BitVec 64}
    (rsp : a[4].get 64 = sp) (rd : LoadOk m (sp + 168) 8) (zero : memLoad m (sp + 168) 64 = 0) :
    program.runBlock (dialect Extracted.programImage) ⟨.l1033d4, a, m⟩ =
      .jump ⟨.l1033f9, (a.set 7 ⟨64,0⟩).set 19 (.ofBool true), m⟩ := by
  cfg_eval [rsp, rd, zero, testFlags, Option.getD_some, beq_self_eq_true]
  congr 2
  apply (show ∀ {u v : Vector Value 53}, (∀ i : Fin 53, u[i.val] = v[i.val]) → u = v from
    fun eq => Vector.ext fun i hi => eq ⟨i, hi⟩)
  intro i
  finite_cases i <;> simp only [Vector.getElem_set] <;> rfl

theorem finish {s : RamState} {key message sig : ByteArray}
    {a : Vector Value 53} {m : Ram} {status : BitVec 64}
    (call : ValidCall verifyingKeyVerify s [key, message, sig]) (memory : Memory s m)
    (sp : a[4].get 64 = localSp s)
    (result : memLoad m (localSp s + 160) 64 = status)
    (payload : status ≠ 0 → memLoad m (localSp s + 168) 64 = 0)
    (bp : a[5] = (Reg.ofIndex 5).read s) (r13 : a[13] = (Reg.ofIndex 13).read s)
    (df : a[22] = ⟨1, 0⟩) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l1033c7, a, m⟩, []⟩ out ∧
      Common.Returned s #v[stack s] out ∧ out.values[0] = ⟨64, status⟩ := by
  have read (off d : Nat) (hd : d ≤ 13000) (eq : localSp s + BitVec.ofNat 64 off =
      stackPtr s - BitVec.ofNat 64 d) : LoadOk m (localSp s + BitVec.ofNat 64 off) 8 := by
    rw [eq]
    have w := (Common.stackWritable (len := 8) call hd (by omega) (by decide)).readable.of_frame memory.frame
    exact ⟨w.low, w.present⟩
  have r160 : LoadOk m (localSp s + 160) 8 := read 160 376 (by decide) (by unfold localSp; bv_omega)
  have r168 : LoadOk m (localSp s + 168) 8 := read 168 368 (by decide) (by unfold localSp; bv_omega)
  let b := (a.set 0 ⟨64,status⟩).set 19 (.ofBool (status == 0))
  have dispatch : program.runBlock (dialect Extracted.programImage) ⟨.l1033c7, a, m⟩ =
      .jump ⟨if status = 0 then .l1033f9 else .l1033d4, b, m⟩ := by
    cfg_eval [sp, result, r160]
    simp only [testFlags, BitVec.and_self, Option.getD_some, beq_iff_eq]
    split <;> rename_i h
    all_goals
      first | rw [ite_eq_left h] | rw [ite_eq_right h]
      congr 2
      apply (show ∀ {u v : Vector Value 53}, (∀ i : Fin 53, u[i.val] = v[i.val]) → u = v from
        fun eq => Vector.ext fun i hi => eq ⟨i, hi⟩)
      intro i
      finite_cases i <;> simp only [b, Vector.getElem_set] <;> rfl
  by_cases h : status = 0
  · rw [ite_eq_left h] at dispatch
    obtain ⟨out, run, post⟩ := epilogue (a := b) (status := status) call memory
      (by simpa [b] using sp) (by simp [b]) (by simpa [b] using bp)
      (by simpa [b] using r13) (by simpa [b] using df)
    exact ⟨out, .next (congrArg (Transfer.next _ []) dispatch) run, post⟩
  · rw [ite_eq_right h] at dispatch
    let c := (b.set 7 ⟨64,0⟩).set 19 (.ofBool true)
    have clean : program.runBlock (dialect Extracted.programImage) ⟨.l1033d4, b, m⟩ =
        .jump ⟨.l1033f9, c, m⟩ := by
      have sb : b[4].get 64 = localSp s := by simpa [b] using sp
      exact rejectCleanup sb r168 (payload h)
    obtain ⟨out, run, post⟩ := epilogue (a := c) (status := status) call memory
      (by simpa [b,c] using sp) (by simp [b,c]) (by simpa [b,c] using bp)
      (by simpa [b,c] using r13) (by simpa [b,c] using df)
    exact ⟨out, .next (congrArg (Transfer.next _ []) dispatch)
      (.next (congrArg (Transfer.next _ []) clean) run), post⟩

end K256.Proofs.Verify.Wrapper
