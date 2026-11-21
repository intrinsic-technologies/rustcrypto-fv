import Sha1.Proofs.MemoryRoutines.Stos.RepForm

namespace Sha1.Proofs.MemoryRoutines.Stos

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem decodeLegacy0_run_of_opcodeAA [Bindings] (s u : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hrex2 : context.rex2_prefix_present = false)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xaa, u)) (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_AA ip context).run u) := by
  unfold Decode_Legacy_0
  rw [ite_eq_right (fun h ↦ Bool.false_ne_true (hrex2.symm.trans h))]
  rw [partialSpecM_liftTotal_bind_run _ _ hfetch]
  repeat erw [decodeLegacy0_modeGuard_run _ _ hmode]
  rfl

theorem decodeLegacy0_run_of_opcodeAB [Bindings] (s u : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hrex2 : context.rex2_prefix_present = false)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xab, u)) (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip context).run s = some ((Decode_Legacy_0_Opcode_AB ip context).run u) := by
  unfold Decode_Legacy_0
  rw [ite_eq_right (fun h ↦ Bool.false_ne_true (hrex2.symm.trans h))]
  rw [partialSpecM_liftTotal_bind_run _ _ hfetch]
  repeat erw [decodeLegacy0_modeGuard_run _ _ hmode]
  rfl

theorem selectLegacy0OpcodeAA_run_of_rep (context : Instruction_Context)
    (hrep : context.rep_prefix = 243) (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_AA context true a b c d e f 0 = .ok 2 := by
  simp [Select_Legacy_0_Opcode_AA, hrep, HAnd.hAnd, AndOp.and, strictAnd]
  rfl

theorem selectLegacy0OpcodeAB_run_of_rep_rexW (context : Instruction_Context)
    (hrep : context.rep_prefix = 243) (hw : context.rex_w = 1) (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_AB context true a b c d e f 0 = .ok 5 := by
  simp [Select_Legacy_0_Opcode_AB, hrep, hw, HAnd.hAnd, AndOp.and, strictAnd]
  rfl

theorem decodeLegacy0OpcodeAA_run_of_rep [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hrep : context.rep_prefix = 243)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_AA ip context).run s =
      (repStosForm .byte (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_AA
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z ↦
    Select_Legacy_0_Opcode_AA context mode a b c d e f z) _ 2 hmode hf
    (selectLegacy0OpcodeAA_run_of_rep context hrep)).trans ?_
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

theorem decodeLegacy0OpcodeAB_run_of_rep_rexW [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hrep : context.rep_prefix = 243) (hw : context.rex_w = 1)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_AB ip context).run s =
      (repStosForm .qword (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_AB
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z ↦
    Select_Legacy_0_Opcode_AB context mode a b c d e f z) _ 5 hmode hf
    (selectLegacy0OpcodeAB_run_of_rep_rexW context hrep hw)).trans ?_
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

noncomputable def Kind.context (kind : Kind) (seg : Segment) : Instruction_Context :=
  match kind with
  | .byte => repContext seg
  | .qword => repRexContext seg 0x48

theorem Kind.context_rex_w (seg : Segment) : (Kind.qword.context seg).rex_w = 1 := rfl

theorem decodeLegacy0_run_of_stos [Bindings] (kind : Kind) (s : RamState) (h : ReadyMidRep s)
    (hcode : BytesAt s s.RIP kind.code) (hlow : s.RIP.toNat + kind.code.length ≤ 2^32) :
    (Decode_Legacy_0 (BitVec.add s.RIP (BitVec.ofNat 64 (kind.code.length - 1)))
      (kind.context s.DS)).run (afterFetches (beforeFetch s) kind.code.length) =
      some ((repStosForm kind (BitVec.add s.RIP (BitVec.ofNat 64 kind.code.length))
        (kind.context s.DS)).run (afterFetches (beforeFetch s) (kind.code.length + 1))) := by
  have hf := h.fetchReady
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hfeatures (k : Nat) : DecoderFeatures (afterFetches (beforeFetch s) k) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  cases kind with
  | byte =>
    have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP [0xf3, 0xaa] := hcode
    have f2 : (Mem_Fetch (BitVec.add s.RIP 1#64) 8).run (afterFetches (beforeFetch s) 2) =
        (.ok 0xaa, afterFetches (beforeFetch s) 3) :=
      memFetch_run_of_bytesAt (beforeFetch s) 2 hf hc hlow 1 (by simp) (by decide)
    change (Decode_Legacy_0 (BitVec.add s.RIP 1#64) (repContext s.DS)).run
      (afterFetches (beforeFetch s) 2) = _
    rw [decodeLegacy0_run_of_opcodeAA _ _ _ _ rfl f2 (hmode 3),
      decodeLegacy0OpcodeAA_run_of_rep _ _ _ rfl (hmode 3) (hfeatures 3),
      show BitVec.add (BitVec.add s.RIP 1#64) 1#64 = BitVec.add s.RIP 2#64 from
        BitVec.add_assoc s.RIP 1#64 1#64]
    rfl
  | qword =>
    have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP [0xf3, 0x48, 0xab] := hcode
    have f3 : (Mem_Fetch (BitVec.add s.RIP 2#64) 8).run (afterFetches (beforeFetch s) 3) =
        (.ok 0xab, afterFetches (beforeFetch s) 4) :=
      memFetch_run_of_bytesAt (beforeFetch s) 3 hf hc hlow 2 (by simp) (by decide)
    change (Decode_Legacy_0 (BitVec.add s.RIP 2#64) (repRexContext s.DS 0x48)).run
      (afterFetches (beforeFetch s) 3) = _
    rw [decodeLegacy0_run_of_opcodeAB _ _ _ _ rfl f3 (hmode 4),
      decodeLegacy0OpcodeAB_run_of_rep_rexW _ _ _ rfl rfl (hmode 4) (hfeatures 4),
      show BitVec.add (BitVec.add s.RIP 2#64) 1#64 = BitVec.add s.RIP 3#64 from
        BitVec.add_assoc s.RIP 2#64 1#64]
    rfl

theorem step_f3_legacy0_midRep [Bindings] (s t : RamState) (h : ReadyMidRep s)
    (op : UInt8) (hop : LegacyOpcode op.toBitVec) (hcode : BytesAt s s.RIP [0xf3, op])
    (hlow : s.RIP.toNat + 2 ≤ 2^32)
    (hpreserve : scanPreservesRepeat op.toBitVec (repContext s.DS) = true)
    (hdecode : (Decode_Legacy_0 (BitVec.add s.RIP 1#64) (repContext s.DS)).run
        (afterFetches (beforeFetch s) 2) = some (.ok (), t)) (hmode : In64BitMode t) :
    X86.Machine.step s = some (.next (finishStep t)) := by
  apply step_of_fetchAndExecute s t h.readyToStepCore _ hmode
  rw [fetchAndExecute_scan_legacy0_of_fetchReady (beforeFetch s) h.fetchReady [0xF3] op
    [] (by simp [scanPrefix_f3]) hop (by simp) hcode hlow]
  have hp : scanPreservesRepeat op.toBitVec (repContext (beforeFetch s).DS) = true := by
    simpa [beforeFetch, resetStepFields] using hpreserve
  have hd : (Decode_Legacy_0 (BitVec.add (beforeFetch s).RIP 1#64)
      (repContext (beforeFetch s).DS)).run (afterFetches (beforeFetch s) 2) = some (.ok (), t) := by
    simpa [beforeFetch, resetStepFields] using hdecode
  have hc := completeDecoded_run_ok (scanPreservesRepeat op.toBitVec
    (repContext (beforeFetch s).DS)) _ hd
  simpa [finishDecoded, scanContext_f3, hp] using hc

end Sha1.Proofs.MemoryRoutines.Stos
