import X86Proofs.Instructions.Movs.Decode
import X86Proofs.Step.LegacyStep

namespace Hkdf.Proofs.Common.Memory.Copy.Movsb

open X86Proofs X86 X86.Machine X86.UserProcess X86.Helpers

theorem decodeLegacy0OpcodeA4_run_of_rep [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hrep : context.rep_prefix = 243)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_A4 ip context).run s =
      (X86.Instructions.REP_MOVSB_0 (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_A4
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_A4 context mode a b c d e f z) _ 2 hmode hf
    (selectLegacy0OpcodeA4_run_of_rep context hrep)).trans ?_
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

theorem decodeLegacy0_run_of_F3_A4 [Bindings] (s : RamState) (h : ReadyMidRep s)
    (hcode : BytesAt s s.RIP [0xF3, 0xA4])
    (hlow : s.RIP.toNat + 2 ≤ 2^32) :
    (Decode_Legacy_0 (BitVec.add s.RIP 1#64) (repContext s.DS)).run
        (afterFetches (beforeFetch s) 2) =
      some ((X86.Instructions.REP_MOVSB_0 (BitVec.add s.RIP 2#64)
        (repContext s.DS)).run (afterFetches (beforeFetch s) 3)) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP [0xF3, 0xA4] := hcode
  have f2 : (Mem_Fetch (BitVec.add s.RIP 1#64) 8).run (afterFetches (beforeFetch s) 2) =
      (.ok 0xA4, afterFetches (beforeFetch s) 3) :=
    memFetch_run_of_bytesAt (beforeFetch s) 2 hf hc hlow 1 (by simp) (by decide)
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) 3) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  rw [decodeLegacy0_run_of_opcodeA4 _ _ _ _ rfl f2 (hmode 3),
    decodeLegacy0OpcodeA4_run_of_rep _ _ _ rfl (hmode 3) hfeatures,
    show BitVec.add (BitVec.add s.RIP 1#64) 1#64 = BitVec.add s.RIP 2#64 from
      BitVec.add_assoc s.RIP 1#64 1#64]

theorem fetchAndExecute_f3_midRep [Bindings]
    (s : RamState) (h : ReadyMidRep s) (op : UInt8) (rest : List UInt8)
    (hop : LegacyOpcode op.toBitVec) (hcode : BytesAt s s.RIP (0xF3 :: op :: rest))
    (hlow : s.RIP.toNat + (0xF3 :: op :: rest).length ≤ 2^32) :
    Fetch_And_Execute.run (beforeFetch s) =
      (completeDecoded (scanPreservesRepeat op.toBitVec (repContext s.DS))
        (Decode_Legacy_0 (BitVec.add s.RIP 1#64) (repContext s.DS))).run
        (afterFetches (beforeFetch s) 2) := by
  exact fetchAndExecute_scan_legacy0_of_fetchReady (beforeFetch s) h.fetchReady [0xF3] op
    rest (by simp [scanPrefix_f3]) hop (by simp) hcode hlow

theorem step_f3_legacy0_midRep [Bindings]
    (s t : RamState) (h : ReadyMidRep s) (op : UInt8) (rest : List UInt8)
    (hop : LegacyOpcode op.toBitVec) (hcode : BytesAt s s.RIP (0xF3 :: op :: rest))
    (hlow : s.RIP.toNat + (0xF3 :: op :: rest).length ≤ 2^32)
    (hrep : scanPreservesRepeat op.toBitVec (repContext s.DS) = true)
    (hdecode : (Decode_Legacy_0 (BitVec.add s.RIP 1#64) (repContext s.DS)).run
        (afterFetches (beforeFetch s) 2) = some (.ok (), t))
    (hmode : In64BitMode t) :
    X86.Machine.step s = some (.next (finishStep t)) := by
  apply step_of_fetchAndExecute s t h.readyToStepCore _ hmode
  rw [fetchAndExecute_f3_midRep s h op rest hop hcode hlow, hrep]
  exact completeDecoded_run_ok _ _ hdecode

end Hkdf.Proofs.Common.Memory.Copy.Movsb
