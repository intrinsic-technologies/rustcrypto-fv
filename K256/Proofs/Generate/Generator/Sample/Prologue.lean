import K256.Proofs.Generate.Generator.Sample.State
import K256.Proofs.Generate.LIR.Fn105f30
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Generate.Generator.Sample

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR

set_option maxHeartbeats 450000 in
theorem firstBlock {s : RamState} {random : ByteArray} {fr : Activation} {a : Registers}
    (call : ValidCall signingKeyGenerateFromRng s [random]) (entry : Entry s fr a)
    (bound : 0 < random.size / 32) (stack : List (StackFrame Value Label signature Reg.count)) :
    ∃ b mem, Run.Reaches ⟨⟨.l105f30, a, fr.original⟩, stack⟩ ⟨⟨.l106020, b, mem⟩, stack⟩ ∧
      AtBlock s random fr 0 b mem := by
  have atoms := entry.atoms
  change Atom.All _ _ _ (Fn105f30.frameAtG0 .l105f30 _) at atoms
  simp only [Fn105f30.frameAtG0, Atom.All, Atom.Holds] at atoms
  obtain ⟨hsp, hdf, _, hrdx, hbx, hbp, hsi, hdi, h8, h9, h12, h13, h14, h15, hmx, hftw, hfcw,
    hrRet, hRet, hRetLow, hWindow, hRoom, hAlign, hrSlot1, hSlot1, hrSlot2, hSlot2, hApart, _⟩ := atoms
  have room : 10168 ≤ fr.rsp.toNat := by omega
  have windowStart : (fr.rsp - 10168).toNat = fr.rsp.toNat - 10168 := by
    rw [BitVec.toNat_sub_of_le (by exact room)]
    rfl
  have wLow := hWindow.readable.low
  have wEnd : (fr.rsp - 10168).toNat + 10168 = fr.rsp.toNat := by omega
  have descriptorReadable : Readable fr.original fr.rsi 16 := by
    rw [entry.descriptor]
    exact ((stackWritable (off := 208) (len := 16) call (by decide) (by decide) (by decide)).of_frame
      entry.writes).readable
  have desc : fr.rsi = fr.rsp + 80 := by
    rw [entry.descriptor, entry.rsp]
    bv_omega
  have hBase := entry.base
  have hLength := entry.length
  rw [desc] at descriptorReadable hBase hLength
  rw [show fr.rsp + 80 + 8 = fr.rsp + 88 by bv_omega] at hLength
  generalize hOriginal : fr.original = original at *
  have len : (s.regValue .rdx).toNat = random.size := call.lengthArgumentsMatchInputs.1
  have enough : ¬ (s.regValue .rdx).toNat < 32 := by omega
  have lenWord : s.regValue .rdx = remaining random 0 := by
    apply BitVec.eq_of_toNat_eq
    simpa only [remaining, Nat.mul_zero, Nat.sub_zero, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (len ▸ (s.regValue .rdx).isLt)] using len
  have get (i : Fin Reg.count) (v : BitVec 64) (h : a[i.val] = ⟨64, v⟩) :
      a[i.val].get 64 = v := by rw [h]; rfl
  have rsp : a[4].get 64 = fr.rsp := get 4 _ hsp
  have rbp : a[5].get 64 = fr.rbp := get 5 _ hbp
  have r15 : a[15].get 64 = fr.r15 := get 15 _ h15
  have r14 : a[14].get 64 = fr.r14 := get 14 _ h14
  have r13 : a[13].get 64 = fr.r13 := get 13 _ h13
  have r12 : a[12].get 64 = fr.r12 := get 12 _ h12
  have rbx : a[3].get 64 = fr.rbx := get 3 _ hbx
  have rdi : a[7].get 64 = fr.rdi := get 7 _ hdi
  have rsi : a[6].get 64 = fr.rsi := get 6 _ hsi
  have ahead : Ahead lifted Extracted.programImage
      (fun l => ∃ h : l.label = .l106020, AtBlock s random fr 0 l.arguments l.store)
      ⟨.l105f30, a, original⟩ := by
    apply Ahead.of_step_jump
    change Onward lifted _ _ _ (program.runBlock (dialect Extracted.programImage) ⟨.l105f30, a, original⟩)
    cfg_eval
    rw [rsp, rbp, r15, r14, r13, r12, rbx, rdi, rsi, desc]
    repeat' (refine Onward.guard ?_ ?_ <;> (try slot_guard using code_l105f30))
    apply Onward.jump
    apply Ahead.of_step_jump
    cfg_eval [lifted, program]
    refine_norm [hLength, hBase]
    apply Onward.ite
    · intro short
      exact (enough short).elim
    intro _
    apply Onward.jump
    apply Ahead.of_step_jump
    cfg_eval [lifted, program]
    apply Onward.jump
    apply Ahead.here
    refine ⟨rfl, ⟨⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩⟩
    · change Atom.All _ _ _ (Fn105f30.frameAtG0 .l106020 _)
      simp only [Fn105f30.frameAtG0, Atom.All, Atom.Holds]
      refine ⟨rfl, hdf, ?r14, hmx, hftw, hfcw, ?output, ?rbx, ?saved12, ?saved13,
        ?saved14, ?saved15, ?rbp, ?readRet, ?returnWord, hRetLow, ?window, hRoom, hAlign,
        ?readSlot1, ?wordSlot1, ?readSlot2, ?wordSlot2, hApart, trivial⟩
      case' r14 => exact congrArg (fun v => (⟨64, v⟩ : Value)) desc.symm
      case' readRet | window | readSlot1 | readSlot2 => slot_state region
      all_goals refine_norm [hRet, hSlot1, hSlot2]
    · rw [hOriginal]
      have inside (off : BitVec 64) (hmin : 8 ≤ off.toNat) (hmax : off.toNat ≤ 10168) :
          InRegions (regions fr) (fr.rsp - off) 8 := by
        refine ⟨fr.region, List.mem_cons_self, ?_⟩
        unfold InRegion Activation.region
        rw [BitVec.toNat_sub_of_le (by exact Nat.le_trans hmax room)]
        change fr.low.toNat ≤ fr.rsp.toNat - off.toNat ∧
          fr.rsp.toNat - off.toNat + 8 ≤ fr.low.toNat + (fr.rsp.toNat - fr.low.toNat) ∧
          fr.rsp.toNat - off.toNat + 8 ≤ 2^64
        omega
      repeat' (refine RamWriteFrame.memStore ?_ _ ?_)
      all_goals first | exact RamWriteFrame.refl _ _ | exact inside _ (by decide) (by decide)
    · exact congrArg Value.width hrdx
    · exact congrArg Value.width h8
    · exact congrArg Value.width h9
    · rfl
    · exact congrArg (fun v => (⟨64, v⟩ : Value)) lenWord
    · rfl
    · rfl
  obtain ⟨⟨l, b, mem⟩, run, rfl, hb⟩ := ahead
  exact ⟨b, mem, run.reaches stack, hb⟩

end K256.Proofs.Generate.Generator.Sample
