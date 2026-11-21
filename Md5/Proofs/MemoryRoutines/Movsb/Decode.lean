import X86Proofs.Instructions.Movs.Decode

namespace Md5.Proofs.MemoryRoutines.Movsb

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem decodeLegacy0OpcodeA4_run_of_rep [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hrep : context.rep_prefix = 243)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_A4 ip context).run s =
      (X86.Instructions.REP_MOVSB_0 (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_A4
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z ↦
    Select_Legacy_0_Opcode_A4 context mode a b c d e f z) _ 2 hmode hf
    (selectLegacy0OpcodeA4_run_of_rep context hrep)).trans ?_
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

theorem decodeLegacy0_run_of_F3_A4 [Bindings] (s : RamState) (h : ReadyMidRep s)
    (hcode : BytesAt s s.RIP [0xF3, 0xA4]) (hlow : s.RIP.toNat + 2 ≤ 2^32) :
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

end Md5.Proofs.MemoryRoutines.Movsb
