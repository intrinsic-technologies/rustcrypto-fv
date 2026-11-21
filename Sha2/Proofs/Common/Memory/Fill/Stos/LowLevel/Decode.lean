import Sha2.Proofs.Common.Memory.Copy.Movsb.Decode
import X86Proofs.Instructions.Movs.RepStep

namespace Sha2.Proofs.Common.Memory.Fill.Stos

open X86Proofs X86 X86.Machine X86.UserProcess X86.Helpers

theorem decodeLegacy0_run_of_opcodeAA [Bindings] (s u : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xAA, u)) (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip ctx).run s = some ((Decode_Legacy_0_Opcode_AA ip ctx).run u) := by
  unfold Decode_Legacy_0
  rw [ite_eq_right (fun h => Bool.false_ne_true (hrex2.symm.trans h))]
  rw [partialSpecM_liftTotal_bind_run _ _ hfetch]
  repeat erw [decodeLegacy0_modeGuard_run _ _ hmode]
  rfl

theorem decodeLegacy0_run_of_opcodeAB [Bindings] (s u : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (hrex2 : ctx.rex2_prefix_present = false)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok 0xAB, u)) (hmode : In64BitMode u) :
    (Decode_Legacy_0 ip ctx).run s = some ((Decode_Legacy_0_Opcode_AB ip ctx).run u) := by
  unfold Decode_Legacy_0
  rw [ite_eq_right (fun h => Bool.false_ne_true (hrex2.symm.trans h))]
  rw [partialSpecM_liftTotal_bind_run _ _ hfetch]
  repeat erw [decodeLegacy0_modeGuard_run _ _ hmode]
  rfl

theorem selectLegacy0OpcodeAA_run_of_rep (context : Instruction_Context) (hrep : context.rep_prefix = 243)
    (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_AA context true a b c d e f 0 = .ok 2 := by
  simp only [Select_Legacy_0_Opcode_AA, HAnd.hAnd, AndOp.and, strictAnd, hrep, Int.reduceBEq,
    Bool.and_false, Bool.false_eq_true, ↓reduceIte, BEq.rfl, Bool.and_self]
  rfl

theorem selectLegacy0OpcodeAB_run_of_rep_rexW (context : Instruction_Context) (hrep : context.rep_prefix = 243)
    (hw : context.rex_w = 1) (a b c d e f : Bool) :
    Select_Legacy_0_Opcode_AB context true a b c d e f 0 = .ok 5 := by
  simp only [Select_Legacy_0_Opcode_AB, HAnd.hAnd, AndOp.and, strictAnd, Bool.true_and, hw,
    BitVec.ofNat_eq_ofNat, Int.toNat_one, BitVec.reduceBEq, Bool.and_false, hrep,
    Int.reduceBEq, Bool.and_self, Bool.false_eq_true, ↓reduceIte, BEq.rfl, Bool.and_true]
  rfl

theorem decodeLegacy0OpcodeAA_run_of_rep [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hrep : context.rep_prefix = 243)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_AA ip context).run s =
      (X86.Instructions.REP_STOSB_0 (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_AA
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_AA context mode a b c d e f z) _ 2 hmode hf
    (selectLegacy0OpcodeAA_run_of_rep context hrep)).trans ?_
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

theorem decodeLegacy0_run_of_F3_AA [Bindings] (s : RamState) (h : ReadyMidRep s)
    (hcode : BytesAt s s.RIP [0xF3, 0xAA])
    (hlow : s.RIP.toNat + 2 ≤ 2^32) :
    (Decode_Legacy_0 (BitVec.add s.RIP 1#64) (repContext s.DS)).run
        (afterFetches (beforeFetch s) 2) =
      some ((X86.Instructions.REP_STOSB_0 (BitVec.add s.RIP 2#64)
        (repContext s.DS)).run (afterFetches (beforeFetch s) 3)) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP [0xF3, 0xAA] := hcode
  have f2 : (Mem_Fetch (BitVec.add s.RIP 1#64) 8).run (afterFetches (beforeFetch s) 2) =
      (.ok 0xAA, afterFetches (beforeFetch s) 3) :=
    memFetch_run_of_bytesAt (beforeFetch s) 2 hf hc hlow 1 (by simp) (by decide)
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) 3) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  rw [decodeLegacy0_run_of_opcodeAA _ _ _ _ rfl f2 (hmode 3),
    decodeLegacy0OpcodeAA_run_of_rep _ _ _ rfl (hmode 3) hfeatures,
    show BitVec.add (BitVec.add s.RIP 1#64) 1#64 = BitVec.add s.RIP 2#64 from
      BitVec.add_assoc s.RIP 1#64 1#64]

theorem decodeLegacy0OpcodeAB_run_of_rep_rexW [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context) (hrep : context.rep_prefix = 243) (hw : context.rex_w = 1)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_0_Opcode_AB ip context).run s =
      (X86.Instructions.REP_STOSQ_0 (BitVec.add ip 1#64) context).run s := by
  unfold Decode_Legacy_0_Opcode_AB
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_0_Opcode_AB context mode a b c d e f z) _ 5 hmode hf
    (selectLegacy0OpcodeAB_run_of_rep_rexW context hrep hw)).trans ?_
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

theorem decodeLegacy0_run_of_F3_rex_AB [Bindings] (s : RamState) (h : ReadyMidRep s) (rex : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hcode : BytesAt s s.RIP [0xF3, rex, 0xAB])
    (hlow : s.RIP.toNat + 3 ≤ 2^32) :
    (Decode_Legacy_0 (BitVec.add s.RIP 2#64) (repRexContext s.DS rex.toBitVec)).run
        (afterFetches (beforeFetch s) 3) =
      some ((X86.Instructions.REP_STOSQ_0 (BitVec.add s.RIP 3#64)
        (repRexContext s.DS rex.toBitVec)).run (afterFetches (beforeFetch s) 4)) := by
  have hf := h.fetchReady
  have hc : BytesAt (beforeFetch s) (beforeFetch s).RIP [0xF3, rex, 0xAB] := hcode
  have f3 : (Mem_Fetch (BitVec.add s.RIP 2#64) 8).run (afterFetches (beforeFetch s) 3) =
      (.ok 0xAB, afterFetches (beforeFetch s) 4) :=
    memFetch_run_of_bytesAt (beforeFetch s) 3 hf hc hlow 2 (by simp) (by decide)
  have hmode (k : Nat) : In64BitMode (afterFetches (beforeFetch s) k) :=
    in64BitMode_of_userCodeSegment hf.cs hf.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) 4) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  have hw := repRexContext_rex_w hrex s.DS
  rw [decodeLegacy0_run_of_opcodeAB _ _ _ _ rfl f3 (hmode 4),
    decodeLegacy0OpcodeAB_run_of_rep_rexW _ _ _ rfl hw (hmode 4) hfeatures,
    show BitVec.add (BitVec.add s.RIP 2#64) 1#64 = BitVec.add s.RIP 3#64 from
      BitVec.add_assoc s.RIP 2#64 1#64]

end Sha2.Proofs.Common.Memory.Fill.Stos
