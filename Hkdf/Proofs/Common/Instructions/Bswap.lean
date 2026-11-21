import X86Proofs.Step.Escape
import X86Proofs.Instructions.Not.Generated.R.Triple
import X86Proofs.Program.Compose

set_option autoImplicit false

namespace Hkdf.Proofs.Common.Instructions

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs

def bswap64 (x : BitVec 64) : BitVec 64 :=
  immPartial (fun i => x.extractLsb' ((7-i)*8) 8) 8

theorem bswap64_byte (x : BitVec 64) (j : Nat) (hj : j < 8) :
    (bswap64 x).extractLsb' (8*j) 8 = x.extractLsb' (8*(7-j)) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb']
  have hkj : 8*j+k < 64 := by omega
  rw [bswap64, immPartial_getLsbD _ _ _ hkj]
  simp only [show 8*j+k < 8*8 from hkj, decide_true, Bool.true_and,
    show (8*j+k)/8 = j by omega, show (8*j+k)%8 = k by omega,
    BitVec.getLsbD_extractLsb', hk, Nat.mul_comm (7-j) 8]

theorem bswap64_bswap64 (x : BitVec 64) : bswap64 (bswap64 x) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have h := bswap64_byte (bswap64 x) (k/8) (by omega)
  rw [bswap64_byte x (7-k/8) (by omega), show 7-(7-k/8)=k/8 by omega] at h
  have hb := congrArg (fun v => v.getLsbD (k%8)) h
  simpa only [BitVec.getLsbD_extractLsb', show k%8 < 8 by omega, decide_true,
    Bool.true_and, show 8*(k/8)+k%8=k by omega] using hb

theorem except_forIn_range' {ε α β : Type} (g : Nat → α)
    (f : α → β → Except ε (ForInStep β)) (v : Nat → β)
    (n j : Nat) (h : ∀ i, j ≤ i → i < j+n → f (g i) (v i) = .ok (.yield (v (i+1)))) :
    forIn ((List.range' j n).map g) (v j) f = .ok (v (j+n)) := by
  induction n generalizing j with
  | zero => simp only [List.range'_zero, List.map_nil, List.forIn_nil, Nat.add_zero]; rfl
  | succ n ih =>
    simp only [List.range'_succ, List.map_cons, List.forIn_cons]
    rw [h j (by omega) (by omega)]
    change forIn ((List.range' (j+1) n).map g) (v (j+1)) f = _
    simpa only [Nat.add_assoc, Nat.add_comm 1 n] using
      ih (j+1) (fun i h₁ h₂ => h i (by omega) (by omega))

theorem byteReverse64 (x : BitVec 64) : Byte_Reverse 8 x = .ok (bswap64 x) := by
  let b := fun i => x.extractLsb' ((7-i)*8) 8
  have hmask : maskPartial 64 8 = 0 := by decide +kernel
  unfold Byte_Reverse
  simp only [assert_of_true (by decide : decide ((0:Int) ≤ 8) = true), pure_bind]
  rw [intRange_zero 8 _ (by decide)]
  change (forIn _ (⟨immPartial b 0, maskPartial 64 0⟩ : Runtime.InitializedBits 64) _ >>= _) = _
  rw [except_forIn_range' (ε := Runtime.Error Empty) (fun i : Nat => (0:Int)+i) _
    (fun i => (⟨immPartial b i, maskPartial 64 i⟩ : Runtime.InitializedBits 64)) 8 0 ?_]
  · change ((Runtime.InitializedBits.mk (size := 64) (immPartial b 8) (maskPartial 64 8)).read : Except (Runtime.Error Empty) (BitVec 64)) = .ok (bswap64 x)
    exact read_mk _ _ (by decide) hmask
  · intro i _ hi
    have h1 : (i:Int)*8+8 ≤ 64 := by omega
    have h2 : 0 ≤ (i:Int)*8 := by omega
    have h3 : ((7:Int)-i)*8+8 ≤ 64 := by omega
    have h4 : 0 ≤ ((7:Int)-i)*8 := by omega
    have h5 : (((7:Int)-i)*8).toNat = (7-i)*8 := by omega
    have h6 : ((i:Int)*8).toNat = 8*i := by omega
    simp only [Int.zero_add, show (8:Int)-1 = 7 from rfl,
      h2, h4, decide_true, assert_of_true rfl, pure_bind,
      checkedSliceRead_eq_pure x h4 (by decide) h3, h5]
    simp only [Runtime.InitializedBits.writeSlice, x86_runtime, h1, h2, h3, h6, immPartial,
      maskPartial, b, pure_bind]
    rfl

theorem bswap_operation (x : BitVec 64) :
    X86.Instructions.Operations.BSWAP 64 x = .ok (bswap64 x) := by
  unfold X86.Instructions.Operations.BSWAP
  simp only [Runtime.assertWithProof, Bool.or_false, Bool.false_or, Int.reduceBEq,
    ↓reduceDIte, pure_bind, Bool.false_eq_true, ↓reduceIte]
  simp [Runtime.remember, Std.Integer.Positive_Divide, Runtime.Positive_Divide,
    liftM, monadLift, Runtime.assert, pure, Except.pure, bind, Except.bind,
    byteReverse64]

theorem bswap_operation_run {σ : Type} (s : X86.State σ) (x : BitVec 64) :
    (liftM (X86.Instructions.Operations.BSWAP 64 x) :
      X86.Runtime.SpecM X86.Exception (X86.State σ) (BitVec 64)).run s =
      (.ok (bswap64 x), s) := by
  rw [bswap_operation]
  rfl

theorem bswap_r64_form {σ : Type} [PhysicalMemory σ] (s : X86.State σ)
    (ip : BitVec 64) (ctx : Instruction_Context) (op : BitVec 8)
    (hmode : In64BitMode s) (hsize : ctx.operand_size = 64)
    (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.BSWAP_GPRv ip ctx op).run s =
      let dst : Operand 64 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 (op.extractLsb' 0 3))
      (.ok (), writeResult s dst (bswap64 (dst.read s)) ip) := by
  have hcontext : {ctx with operand_size := 64, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.BSWAP_GPRv
  simp only [Operand.read_reg64, writeResult, Operand.write_reg64]
  spec_run [Read_GPR => readGPR64_run _ _ hmode,
    liftM => bswap_operation_run _ _,
    Write_GPR => writeGPR64_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]

set_option maxHeartbeats 800000 in
theorem decodeLegacy1_bswap_dispatch [Bindings] (s u : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (op : BitVec 8) (hop : op ∈ bswapOpcodes)
    (hrex2 : ctx.rex2_prefix_present = false) (hmode : In64BitMode u)
    (hfetch : (Mem_Fetch ip 8).run s = (.ok op, u)) :
    (Decode_Legacy_1 ip ctx).run s =
      some ((Decode_Legacy_1_Opcode_C8 ip ctx op).run u) := by
  simp only [bswapOpcodes, List.mem_cons, List.not_mem_nil, or_false] at hop
  rcases hop with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    (unfold Decode_Legacy_1
     rw [ite_eq_right (fun h => Bool.false_ne_true (hrex2.symm.trans h))]
     rw [partialSpecM_liftTotal_bind_run _ _ hfetch]
     repeat erw [decodeLegacy0_modeGuard_run _ _ hmode]
     repeat erw [decodeLegacy1_modeGuard_run _ _ _ _ hmode]
     rfl)

theorem decodeLegacy1Opcode_bswap [Bindings] (s : RamState) (ip : BitVec 64)
    (ctx : Instruction_Context) (op : BitVec 8)
    (hmode : In64BitMode s) (hf : DecoderFeatures s) :
    (Decode_Legacy_1_Opcode_C8 ip ctx op).run s =
      (X86.Instructions.BSWAP_GPRv (BitVec.add ip 1#64) ctx op).run s := by
  unfold Decode_Legacy_1_Opcode_C8
  refine (decoderSelect_run_noModRM s (fun mode a b c d e f z =>
    Select_Legacy_1_Opcode_C8 ctx mode a b c d e f z) _ 1 hmode hf
    (fun _ _ _ _ _ _ => rfl)).trans ?_
  refine (specM_bind_run (liftM (Std.Bits.Add_int (n := 64) ip 1)) _ (s := s) rfl).trans ?_
  exact specM_bind_pure_unit_run _ s

theorem bswap_r64_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (rex op : UInt8) (hrex : RexWPrefix rex.toBitVec)
    (hop : op.toBitVec ∈ bswapOpcodes)
    (hcode : BytesAt s s.RIP [rex, 0x0f, op]) (hlow : s.RIP.toNat+3 ≤ 2^32) :
    let dst : Operand 64 := .reg (gprNumber 0 (rexB rex.toBitVec) (op.toBitVec.extractLsb' 0 3))
    X86.Machine.step s = some (.next (afterStep s 3 fun t =>
      writeResult t dst (bswap64 (dst.read t)) (BitVec.add s.RIP 3#64))) := by
  have hf : (Mem_Fetch (BitVec.add s.RIP 2#64) 8).run (afterFetches (beforeFetch s) 3) =
      (.ok op.toBitVec, afterFetches (beforeFetch s) 4) :=
    memFetch_run_of_bytesAt (beforeFetch s) 3 h.fetchReady hcode hlow 2 (by simp) (by decide)
  have hmode : In64BitMode (afterFetches (beforeFetch s) 4) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) 4) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ h.features
  have hd := decodeLegacy1_bswap_dispatch _ _ _ (rexContext s.DS rex.toBitVec)
    op.toBitVec hop rfl hmode hf
  rw [decodeLegacy1Opcode_bswap _ _ _ _ hmode hfeatures,
    bswap_r64_form _ _ _ _ hmode (hrex.operand_size s.DS) rfl,
    show BitVec.add (BitVec.add s.RIP 2#64) 1#64 = BitVec.add s.RIP 3#64 from
      BitVec.add_assoc s.RIP 2#64 1#64] at hd
  have hop' : op ≠ 0x38 ∧ op ≠ 0x3a := by
    simp only [bswapOpcodes, List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with h | h | h | h | h | h | h | h <;>
      (have hh := congrArg UInt8.ofBitVec h
       simp only [UInt8.ofBitVec_toBitVec] at hh
       rw [hh]
       decide +kernel)
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_rex_legacy1 s _ h rex op [] hrex.rexPrefix hop' hcode hlow hd
    (hmode.of_cs_lma_eq rfl rfl)

def encodeBswapR64 (dst : BitVec 4) : List UInt8 :=
  [UInt8.ofNat (0x48+dst.toNat/8), 0x0f, UInt8.ofNat (0xc8+dst.toNat%8)]

theorem encodeBswapR64_spec (dst : BitVec 4) : ∃ rex op,
    encodeBswapR64 dst = [rex,0x0f,op] ∧ RexWPrefix rex.toBitVec ∧
      op.toBitVec ∈ bswapOpcodes ∧
      gprNumber 0 (rexB rex.toBitVec) (op.toBitVec.extractLsb' 0 3) = dst.setWidth 5 := by
  refine ⟨_, _, rfl, ?_⟩
  unfold RexWPrefix
  revert dst
  decide +kernel

def bswapR64Effect (p : BitVec 64) (dst : BitVec 5) (s : RamState) : Effect :=
  { rip := p+3
    writes := [⟨(Operand.reg dst : Operand 64), bswap64 ((Operand.reg dst : Operand 64).read s)⟩] }

theorem bswap_r64_effect_step_of_bytes [Bindings] (p : BitVec 64) (rex op : UInt8)
    (hrex : RexWPrefix rex.toBitVec) (hop : op.toBitVec ∈ bswapOpcodes) :
    StepEffect (fun s => s.RIP=p) (codeRange p [rex,0x0f,op])
      (bswapR64Effect p (gprNumber 0 (rexB rex.toBitVec) (op.toBitVec.extractLsb' 0 3))) := by
  rintro s h hc rfl
  refine ⟨_, bswap_r64_step s h rex op hrex hop hc.bytesAt (hc.low (by simp) (by simp)),
    ReadyToStep.afterStep_writeResult h 3 _ _ _,
    ⟨afterStep_writeResult_rip h 3 _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s 3 _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self, Operand.read_afterFetches, Operand.read_beforeFetch]

theorem bswap_r64_effect_step [Bindings] (p : BitVec 64) (dst : BitVec 4) :
    StepEffect (fun s => s.RIP=p) (codeRange p (encodeBswapR64 dst))
      (bswapR64Effect p (dst.setWidth 5)) := by
  obtain ⟨rex,op,hcode,hrex,hop,hdst⟩ := encodeBswapR64_spec dst
  rw [hcode, ← hdst]
  exact bswap_r64_effect_step_of_bytes p rex op hrex hop

theorem bswap_r64_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) :
    Triple (fun s => s.RIP=p) (codeRange p (encodeBswapR64 dst))
      (Effect.post (bswapR64Effect p (dst.setWidth 5))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by simp [bswapR64Effect, Effect.components, Component.Covers]) _)
    (bswap_r64_effect_step p dst)

attribute [x86_compose] bswapR64Effect

@[x86_local] theorem bswapR64Effect_local (p : BitVec 64) (dst : BitVec 5) :
    Effect.Local (bswapR64Effect p dst) := by
  refine ⟨fun t t' h => ?_, fun t t' h => ?_, fun t t' h => ?_, fun t t' h i hi => ?_,
    fun t => ?_⟩
  · rfl
  · simp [bswapR64Effect, h.read_reg]
  · rfl
  · exact congrArg some hi
  · simp [bswapR64Effect, Write.Full, Operand.Full]

end Hkdf.Proofs.Common.Instructions
