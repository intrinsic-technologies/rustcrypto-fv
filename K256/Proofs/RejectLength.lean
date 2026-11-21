import K256.Proofs.Common.SignatureRun
import K256.Proofs.RejectLength.ErrorPayload
import K256.Proofs.RejectLength.LengthCheck
import K256.Proofs.RejectLength.Return
import K256.Proofs.RejectLength.Stack

namespace K256.Proofs

open K256.Spec K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine LIR SignatureSlice

theorem rejectLength
    [bindings : Machine.Bindings]
    {initial : Machine.RamState} {bytes : ByteArray}
    (hBindings : MachineRamUnitStrideDecodable bindings initial)
    (hMachine : SupportedIntegerMachineState bindings.processor initial)
    (hCall : ValidCall signatureFromSlice initial [bytes])
    (hLength : bytes.size ≠ 64) : SignatureSliceResult initial bytes := by
  have storeErrorBlock {code : CodeMap} {args : Vector Value 53} {mem : Ram}
      {sp : BitVec 64} (hsp : args[4] = ⟨64, sp⟩)
      (hstore : StoreOk code mem (sp + 16) 8 0x1024d6 9) :
      program.runBlock (dialect code) ⟨.l1024d6, args, mem⟩ =
        .jump ⟨.l1024df, args, memStore mem (sp + 16) (0 : BitVec 64)⟩ := by
    have rsp : Value.get 64 args[4] = sp := by rw [hsp]; rfl
    cfg_eval
    simp only [rsp, hstore, ite_true]
    congr 2
    apply (show ∀ {a b : Vector Value 53}, (∀ i : Fin 53, a[i.val] = b[i.val]) → a = b from
      fun h => Vector.ext fun i hi => h ⟨i, hi⟩)
    intro i
    finite_cases i <;> rfl
  let sp := initial.regValue .rsp
  let dx := initial.regValue .rdx
  let bx := initial.regValue .rbx
  let args : Vector Value 53 := (lifted.locationOf .l102450 initial).arguments
  let next := (args.set 4 ⟨64, sp - 88⟩).set 19 (.ofBool (dx == 64))
  let save := memStore initial.external (sp - 8) bx
  let empty := memStore save (sp - 72) (0 : BitVec 64)
  obtain ⟨ret, hslot, hlow, hout⟩ := hCall.returnAddress
  have hframe := Common.signatureFramePre hCall (memLoad_returnSlot hslot) hlow hout
  obtain ⟨hpush, hstore, hload, hzero, hpop, hsaved, hread, hret, hwritten⟩ :=
    rejectStack hCall.stackAvailable hframe
  have hdx : dx ≠ 64 := by
    intro he
    have length : dx.toNat = bytes.size := hCall.lengthArgumentsMatchInputs.1
    exact hLength (length.symm.trans (congrArg BitVec.toNat he))
  have hentry := lengthBlock (args := args) (sp := sp) (dx := dx) (bx := bx)
    (Vector.getElem_ofFn _) (Vector.getElem_ofFn _) (Vector.getElem_ofFn _) hpush
  simp only [ite_eq_right hdx] at hentry
  have hsp : next[4] = ⟨64, sp - 88⟩ := by
    simp [next]
  have haddr : sp - 88 + 16 = sp - 72 := by
    rw [show sp - 88 = sp - 72 - 16 by rw [BitVec.sub_sub]; rfl, BitVec.sub_add_cancel]
  have hstored := storeErrorBlock hsp (haddr.symm ▸ hstore)
  rw [haddr] at hstored
  obtain ⟨doneArgs, hbranch, hstatus, hkept⟩ :=
    emptyErrorBlock (code := Extracted.programImage) (mem := empty) hsp
      (haddr.symm ▸ hload) (haddr.symm ▸ hzero)
  have hdoneSP := (hkept 4 (by decide)).trans hsp
  obtain ⟨out, hdone, hmem, htag, hbx, hrsp, hsame⟩ :=
    returnBlock (code := Extracted.programImage) hdoneSP hpop hread
      (show (memLoad empty sp 64).toNat < 2^32 by rw [hret]; exact hlow)
  have hexec : program.Exec (dialect Extracted.programImage)
      ⟨⟨.l102450, args, initial.external⟩, []⟩ out := by
    apply Program.Exec.next (next := ⟨⟨.l1024d6, next, save⟩, []⟩)
    · exact congrArg (Transfer.next _ []) hentry
    apply Program.Exec.next (next := ⟨⟨.l1024df, next, empty⟩, []⟩)
    · exact congrArg (Transfer.next _ []) hstored
    apply Program.Exec.next (next := ⟨⟨.l1024d0, doneArgs, empty⟩, []⟩)
    · exact congrArg (Transfer.next _ []) hbranch
    exact .done (congrArg (Transfer.next _ []) hdone)
  have entryReg (i : Fin 53) (h4 : 4 ≠ i.val) (h19 : 19 ≠ i.val) :
      next[i.val] = (Reg.ofIndex i.val).read initial := by
    simp only [next, Vector.getElem_set, h4, h19, ↓reduceIte]
    exact Vector.getElem_ofFn _
  have eax : out.values[0] = ⟨64, 1⟩ := (hsame 0 (by decide)).trans hstatus
  apply Common.signatureSliceRejected hBindings hMachine hCall hexec _ eax
  · simp [Ecdsa.signatureScalars, hLength]
  · refine ⟨?_, hrsp, ?_, ?_, ?_, ?_⟩
    · rw [htag, hret, hframe.returnBoundary.1]
      rfl
    · refine (hsame 22 (by decide)).trans ((hkept 22 (by decide)).trans ?_)
      exact (entryReg 22 (by decide) (by decide)).trans (Reg.read_df_iff.mpr hCall.directionFlagUnset)
    · intro ⟨i, hi⟩ hm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl | rfl | rfl
      · exact hbx.trans (congrArg (fun x => (⟨64, x⟩ : Value)) hsaved)
      all_goals
        apply Eq.trans (hsame _ (by decide +revert))
        apply Eq.trans (hkept _ (by decide +revert))
        exact entryReg _ (by decide +revert) (by decide +revert)
    · exact hmem.symm ▸ hwritten
    · exact congrArg Value.width eax

end K256.Proofs
