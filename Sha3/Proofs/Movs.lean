import Sha3.Proofs.Stos
import X86Proofs.Instructions.Movs.Execution

namespace Sha3.Proofs.Movs

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

theorem rep_movsb_form_zero [Bindings] (t : RamState) (ip : BitVec 64) (ctx : Instruction_Context)
    (haddr : ctx.address_size = 64) (hrex2 : ctx.rex2_prefix_present = false)
    (hlock : ctx.lock_prefix_present = false) (hcount : rcx.read t = 0) :
    (X86.Instructions.REP_MOVSB_0 ip ctx).run t =
      (.ok (), { t with Next_IP := ip, Repeat_String_Operation := false }) := by
  have hc : { ctx with address_size := 64 } = ctx := by cases ctx; simp_all
  rw [← hc]
  unfold X86.Instructions.REP_MOVSB_0
  simp only [hrex2, hlock, Bool.not_false, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rw [specM_bind_run (modify (fun a : RamState => { a with Next_IP := ip })) _ (s := t) rfl]
  simp only [show decide ((64 : Int) ≤ 64) = true from rfl,
    show decide ((0 : Int) ≤ 64) = true from rfl, assert_of_true, pure_bind, bind_assoc]
  have hslice (a : RamState) (v : BitVec 64) : (X86.Runtime.CheckedSlice.read v 0 64 :
      X86.Runtime.SpecM X86.Exception RamState (BitVec 64)).run a = (.ok v, a) := by
    simp [X86.Runtime.CheckedSlice.read, x86_runtime]
  rw [specM_bind_run _ _ (rcx_run _)]
  refine (specM_bind_run _ _ (hslice _ _)).trans ?_
  have hz : rcx.read { t with Next_IP := ip } = 0 := hcount
  rw [hz]
  simp only [show (X86.Runtime.Unsigned (0 : BitVec 64) == (0 : Int)) = true from rfl, ↓reduceIte]
  rw [specM_bind_run (modify (fun a : RamState => { a with Repeat_String_Operation := false })) _
    (s := { t with Next_IP := ip }) rfl]
  rw [specM_bind_run _ _ (rcx_run _), specM_bind_run _ _ (hslice _ _)]
  have hz' : rcx.read { t with Next_IP := ip, Repeat_String_Operation := false } = 0 := hcount
  rw [hz']
  rfl

theorem decodeLegacy0OpcodeA4_run_of_rep [Bindings] (s : RamState) (ip : BitVec 64)
    (context : Instruction_Context)
    (hrep : context.rep_prefix = 243)
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
    DecoderFeatures.of_sameControls (s := s)
      ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      h.features
  rw [decodeLegacy0_run_of_opcodeA4 _ _ _ _ rfl f2 (hmode 3),
    decodeLegacy0OpcodeA4_run_of_rep _ _ _ rfl (hmode 3) hfeatures,
    show BitVec.add (BitVec.add s.RIP 1#64) 1#64 = BitVec.add s.RIP 2#64 from
      BitVec.add_assoc s.RIP 1#64 1#64]

theorem rep_movsb_step_zero [Bindings] (s : RamState) (h : ReadyMidRep s)
    (hcode : BytesAt s s.RIP [0xF3, 0xA4])
    (hlow : s.RIP.toNat + 2 ≤ 2^32) (hcount : rcx.read s = 0) :
    X86.Machine.step s = some (.next (Stos.repStosZeroAfter 2 s)) := by
  have hdecode := decodeLegacy0_run_of_F3_A4 s h hcode hlow
  have hf := h.fetchReady
  let t := afterFetches (beforeFetch s) 3
  have hmode : In64BitMode t := in64BitMode_of_userCodeSegment (s := t) hf.cs hf.efer.lma
  rw [rep_movsb_form_zero t _ _ rfl rfl rfl hcount] at hdecode
  exact Stos.step_f3_legacy0_midRep s _ h 0xA4
    (legacyOpcode_of_check _ ⟨by decide, by decide⟩) hcode hlow rfl hdecode
    (hmode.of_cs_lma_eq rfl rfl)

theorem rep_movsb_zero_effect_step [Bindings] (p : BitVec 64) :
    StepEffect (fun s => s.RIP = p ∧ rcx.read s = 0) (codeRange p [0xf3, 0xa4])
      (fun _ => { rip := p + 2 }) := by
  intro s h hc hp
  have hs := rep_movsb_step_zero s h.midRep (hp.1 ▸ hc.bytesAt)
    (hp.1 ▸ hc.low (by simp) (by simp)) hp.2
  have hag : AgreesExcept [.rip] s (Stos.repStosZeroAfter 2 s) :=
    (show AgreesExcept [.rip] (X86Proofs.clearRep s)
      (X86Proofs.clearRep (Stos.repStosZeroAfter 2 s)) from
        Stos.agreesExcept_repStosZero 2 s).of_clearRep h.ready.repeatClear rfl
  refine ⟨_, hs, ReadyToStep.of_agreesExcept h hag h.memory.tables, ?_⟩
  refine ⟨?_, trivial, trivial, hag⟩
  rw [Stos.repStosZeroAfter_rip _ _ h.ready.msr, hp.1]
  rfl

end Sha3.Proofs.Movs
