import K256.Proofs.ParseSignature.Wrapper.Frame
import K256.Proofs.ParseSignature.Call
import K256.Proofs.RejectLength.LengthCheck
import K256.Proofs.RejectLength.Stack
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Common.Lift.Eval
import X86Proofs.Instructions.Adc.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Adc.Generated.MImm32.Triple
import X86Proofs.Instructions.Adc.Generated.MImm8.Triple
import X86Proofs.Instructions.Adc.Generated.MR.Triple
import X86Proofs.Instructions.Add.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Add.Generated.MImm32.Triple
import X86Proofs.Instructions.Add.Generated.MImm8.Triple
import X86Proofs.Instructions.Add.Generated.MR.Triple
import X86Proofs.Instructions.And.Generated.M8Imm8.Triple
import X86Proofs.Instructions.And.Generated.MImm32.Triple
import X86Proofs.Instructions.And.Generated.MImm8.Triple
import X86Proofs.Instructions.And.Generated.MR.Triple
import X86Proofs.Instructions.Or.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Or.Generated.MImm32.Triple
import X86Proofs.Instructions.Or.Generated.MImm8.Triple
import X86Proofs.Instructions.Or.Generated.MR.Triple
import X86Proofs.Instructions.Sbb.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Sbb.Generated.MImm32.Triple
import X86Proofs.Instructions.Sbb.Generated.MImm8.Triple
import X86Proofs.Instructions.Sbb.Generated.MR.Triple
import X86Proofs.Instructions.Setcc.Generated.M8.Triple
import X86Proofs.Instructions.Shld.Generated.MRCl.Triple
import X86Proofs.Instructions.Shld.Generated.MRImm8.Triple
import X86Proofs.Instructions.Shrd.Generated.MRCl.Triple
import X86Proofs.Instructions.Shrd.Generated.MRImm8.Triple
import X86Proofs.Instructions.Sub.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Sub.Generated.MImm32.Triple
import X86Proofs.Instructions.Sub.Generated.MImm8.Triple
import X86Proofs.Instructions.Sub.Generated.MR.Triple
import X86Proofs.Instructions.Xor.Generated.M8Imm8.Triple
import X86Proofs.Instructions.Xor.Generated.MImm32.Triple
import X86Proofs.Instructions.Xor.Generated.MImm8.Triple
import X86Proofs.Instructions.Xor.Generated.MR.Triple
import K256.Proofs.Common.Lift.Generated.Values.Store2

namespace K256.Proofs.ParseSignature.Wrapper

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine LIR SignatureSlice

private def pairCont : StackFrame Value Label signature Reg.count :=
  { target := .l102468, kept := #v[], arity := rfl, guard := some ⟨64, 0x102468⟩ }

private theorem callPairBlock {code : CodeMap} {args : Vector Value 53} {mem : Ram}
    {sp dst : BitVec 64} (hsp : args[4] = ⟨64, sp - 88⟩) (hdst : args[7] = ⟨64, dst⟩)
    (hstore : StoreOk code mem (sp - 96) 8 0x102463 5) :
    let child := ((args.set 3 ⟨64, dst⟩).set 7 ⟨64, sp - 80⟩).set 4 ⟨64, sp - 96⟩
    program.runBlock (dialect code) ⟨.l10245b, args, mem⟩ =
      .call ⟨.l103ac0, child, memStore mem (sp - 96) (0x102468 : BitVec 64)⟩ pairCont := by
  have rsp : Value.get 64 args[4] = sp - 88 := by rw [hsp]; rfl
  have rdi : Value.get 64 args[7] = dst := by rw [hdst]; rfl
  have hsub : sp - 88 - 8 = sp - 96 := by rw [BitVec.sub_sub]; rfl
  have hadd : sp - 88 + 8 = sp - 80 := by
    rw [show sp - 88 = sp - 80 - 8 by rw [BitVec.sub_sub]; rfl, BitVec.sub_add_cancel]
  dsimp only
  cfg_eval
  simp only [rsp, rdi, hsub, hadd, hstore, ↓reduceIte]
  congr 2
  apply (show ∀ {a b : Vector Value 53}, (∀ i : Fin 53, a[i.val] = b[i.val]) → a = b from
    fun h => Vector.ext fun i hi => h ⟨i, hi⟩)
  intro i
  finite_cases i <;> simp only [Vector.getElem_set] <;> rfl

theorem enterPair {initial : RamState} {bytes : ByteArray}
    (call : ValidCall signatureFromSlice initial [bytes]) (size : bytes.size = 64) :
    let fr := pairFrame initial
    ∃ args : Vector Value 53,
      Atom.All Extracted.programImage args fr.original (Fn103ac0.frameInfo.entryAtoms fr) ∧
      ∀ (pair final : Output Value Ram Reg.count),
        program.Exec (dialect Extracted.programImage) ⟨⟨.l103ac0, args, fr.original⟩, []⟩ pair →
        pair.tag = some ⟨64, fr.ret⟩ →
        program.Exec (dialect Extracted.programImage)
          ⟨⟨.l102468, pair.values, pair.store⟩, []⟩ final →
        program.Exec (dialect Extracted.programImage) ⟨lifted.locationOf .l102450 initial, []⟩ final := by
  intro fr
  let code := Extracted.programImage
  let sp := initial.regValue .rsp
  let bx := initial.regValue .rbx
  let dx := initial.regValue .rdx
  let dst := initial.regValue .rdi
  let args : Vector Value 53 := (lifted.locationOf .l102450 initial).arguments
  let next := (args.set 4 ⟨64, sp - 88⟩).set 19 (.ofBool (dx == 64))
  let save := memStore initial.external (sp - 8) bx
  let frRet := (0x102468 : BitVec 64)
  let localMem := memStore save (sp - 96) frRet
  obtain ⟨ret, hslot, hlow, hout⟩ := call.returnAddress
  have hf := Common.signatureFramePre call (memLoad_returnSlot hslot) hlow hout
  have hpush := (rejectStack call.stackAvailable hf).1
  have hdx : dx = 64 := by
    apply BitVec.eq_of_toNat_eq
    exact call.lengthArgumentsMatchInputs.1.trans size
  have hentry := lengthBlock (args := args) (sp := sp) (dx := dx) (bx := bx)
    (Vector.getElem_ofFn _) (Vector.getElem_ofFn _) (Vector.getElem_ofFn _) hpush
  simp only [ite_eq_left hdx] at hentry
  have wsp : Writable code initial.external (sp - 656) 656 := hf.window (by decide)
  have wa : Writable code save (sp - 96) 8 :=
    (wsp.of_offsets (addr_sub sp 96) (addr_sub sp 656) (by decide)).memStore _ _
  have hs : StoreOk code save (sp - 96) 8 0x102463 5 := by
    refine ⟨wa.readable.low, wa.readable.present, wa.tables, ?_, wa.notCode⟩
    intro i hi j hj hij
    have hmem := mem_codeRange 0x10245b bytes_l10245b (8 + j) (by change 8 + j < 13; omega)
    apply wa.notCode _ (Common.fnCode_subset_programImage _ (code_l10245b _ hmem)) i hi
    simp only [BitVec.ofNat_add, ← BitVec.add_assoc]
    exact hij.symm
  let child := ((next.set 3 ⟨64, dst⟩).set 7 ⟨64, sp - 80⟩).set 4 ⟨64, sp - 96⟩
  have rsp : next[4] = ⟨64, sp - 88⟩ := by simp [next]
  have rdi : next[7] = ⟨64, dst⟩ := by
    simp only [next, Vector.getElem_set, show ¬(4 = 7) by decide, show ¬(19 = 7) by decide, ↓reduceIte]
    exact Vector.getElem_ofFn _
  have cblock := callPairBlock rsp rdi hs
  refine ⟨child, ?_, ?_⟩
  · have hwin : Writable code localMem (sp - 96 - 560) 560 := by
      rw [BitVec.sub_sub]
      apply Writable.memStore
      apply Writable.memStore
      exact wsp.of_offsets (addr_sub sp 656) (addr_sub sp 656) (by decide)
    have slotReads := Fn103ac0.callSlots_loaded (sections := Extracted.programSections)
      (by exact List.mem_cons_of_mem _ List.mem_cons_self) (mem := localMem) (by
        intro x hx
        change (memStore save (sp - 96) frRet)[x.1]? = some x.2
        rw [memStore_getElem?_of_ne _ _ _ _ (fun i hi => Ne.symm (wa.notCode x hx i hi))]
        rw [show save = memStore initial.external (sp - 8) bx from rfl,
          memStore_getElem?_of_ne _ _ _ _ (fun i hi => Ne.symm (hpush.notCode x hx i hi))]
        exact call.programLoaded _ _ (Common.programSections_fetchByte_of_mem hx))
    have hslotRead : Readable localMem (sp - 96) 8 := wa.readable.memStore _ _
    have hslotVal : memLoad localMem (sp - 96) 64 = frRet :=
      memLoad_memStore_same save _ _ (by decide) (by decide)
    have hroom : 784 ≤ sp.toNat := call.stackAvailable.2.2.1
    have hspNat : (sp - 96).toNat = sp.toNat - 96 := by
      rw [BitVec.toNat_sub_of_le (by change 96 ≤ sp.toNat; omega)]
      rfl
    have parentRoom : fr.low.toNat + 656 ≤ sp.toNat := hf.room
    have room : fr.low.toNat + 560 ≤ (sp - 96).toNat := by omega
    have align : sp.toNat % 16 = 8 := hf.align
    have childAlign : (sp - 96).toNat % 16 = 8 := by omega
    have apart : 0x2040b8 ≤ sp.toNat ∨ sp.toNat ≤ 0x203dd0 := hf.callSlotsApart (by decide)
    have childApart : 0x204058 ≤ (sp - 96).toNat ∨ (sp - 96).toNat ≤ 0x203dd0 := by omega
    have argsAt (i : Fin 53) : args[i.val] = (Reg.ofIndex i.val).read initial :=
      Vector.getElem_ofFn _
    have savedReg (i : Fin 53) (hi : i.val ∉ [3, 4, 7, 19]) :
        child[i.val] = (Reg.ofIndex i.val).read initial := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hi
      obtain ⟨h3, h4, h7, h19⟩ := hi
      simpa only [child, next, Vector.getElem_set, ne_comm.mp h3, ne_comm.mp h4, ne_comm.mp h7,
        ne_comm.mp h19, ↓reduceIte] using argsAt i
    change Atom.All code child localMem (Fn103ac0.frameAt .l103ac0 fr)
    simp only [Fn103ac0.frameAt, Fn103ac0.frameAtG0, Atom.All, Atom.Holds]
    have csp : child[4] = ⟨64, sp - 96⟩ := by simp [child]
    have cbx : child[3] = ⟨64, dst⟩ := by simp [child]
    have cdi : child[7] = ⟨64, sp - 80⟩ := by simp [child]
    have slot₁ := slotReads (0x203dd0, 0x12a820) (by decide)
    have slot₂ := slotReads (0x203de0, 0x129770) (by decide)
    have slot₃ := slotReads (0x203e20, 0x100a20) (by decide)
    exact ⟨csp, (savedReg 22 (by decide)).trans (Reg.read_df_iff.mpr call.directionFlagUnset),
      savedReg 1 (by decide), savedReg 2 (by decide), cbx, savedReg 5 (by decide),
      savedReg 6 (by decide), cdi, savedReg 8 (by decide), savedReg 9 (by decide),
      savedReg 12 (by decide), savedReg 13 (by decide), savedReg 14 (by decide),
      savedReg 15 (by decide), savedReg 39 (by decide), savedReg 50 (by decide),
      savedReg 51 (by decide), hslotRead, hslotVal, by change 0x102468 < 2 ^ 32; decide, hwin, room, childAlign,
      slot₁.1, slot₁.2, slot₂.1, slot₂.2, slot₃.1, slot₃.2, childApart, trivial⟩
  · intro pair final hpair htag hfinal
    apply Program.Exec.next (next := ⟨⟨.l10245b, next, save⟩, []⟩)
    · exact congrArg (Transfer.next _ []) hentry
    apply exec_call cblock hpair
    · rw [htag]
      rfl
    · exact hfinal

end K256.Proofs.ParseSignature.Wrapper
