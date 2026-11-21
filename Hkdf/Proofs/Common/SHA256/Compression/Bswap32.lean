import Hkdf.Proofs.Common.Instructions.Bswap

set_option autoImplicit false

namespace Hkdf.Proofs.Common.SHA256.Compression

open X86 X86.Machine X86.UserProcess X86.Helpers X86Proofs
open Hkdf.Proofs.Common.Instructions

def bswap32 (x : BitVec 32) : BitVec 32 :=
  immPartial (fun i => x.extractLsb' ((3-i)*8) 8) 4

theorem bswap32_byte (x : BitVec 32) (j : Nat) (hj : j < 4) :
    (bswap32 x).extractLsb' (8*j) 8 = x.extractLsb' (8*(3-j)) 8 := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  rw [BitVec.getLsbD_extractLsb', BitVec.getLsbD_extractLsb']
  have hkj : 8*j+k < 32 := by omega
  rw [bswap32, immPartial_getLsbD _ _ _ hkj]
  simp only [show 8*j+k < 4*8 from hkj, decide_true, Bool.true_and,
    show (8*j+k)/8 = j by omega, show (8*j+k)%8 = k by omega,
    BitVec.getLsbD_extractLsb', hk, Nat.mul_comm (3-j) 8]

theorem bswap32_bswap32 (x : BitVec 32) : bswap32 (bswap32 x) = x := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have h := bswap32_byte (bswap32 x) (k/8) (by omega)
  rw [bswap32_byte x (3-k/8) (by omega), show 3-(3-k/8)=k/8 by omega] at h
  have hb := congrArg (fun v => v.getLsbD (k%8)) h
  simpa only [BitVec.getLsbD_extractLsb', show k%8 < 8 by omega, decide_true,
    Bool.true_and, show 8*(k/8)+k%8=k by omega] using hb

theorem bswap32_bytes (b0 b1 b2 b3 : BitVec 8) :
    bswap32 (b3 ++ b2 ++ b1 ++ b0) = b0 ++ b1 ++ b2 ++ b3 := by
  apply BitVec.eq_of_getLsbD_eq
  intro k hk
  have h := congrArg (fun v : BitVec 8 => v.getLsbD (k % 8))
    (bswap32_byte (b3 ++ b2 ++ b1 ++ b0) (k / 8) (by omega))
  simp only [BitVec.getLsbD_extractLsb', show k % 8 < 8 by omega,
    decide_true, Bool.true_and, show 8 * (k / 8) + k % 8 = k by omega] at h
  rw [h]
  rcases (by omega : k / 8 = 0 ∨ k / 8 = 1 ∨ k / 8 = 2 ∨ k / 8 = 3) with h0 | h0 | h0 | h0 <;>
    simp only [h0, Nat.reduceSub, Nat.reduceMul, BitVec.getLsbD_append] <;>
    (repeat' first | rw [ite_eq_left (by omega)] | rw [ite_eq_right (by omega)]) <;>
    congr 1 <;> omega

theorem byteReverse32 (x : BitVec 32) : Byte_Reverse 4 x = .ok (bswap32 x) := by
  let b := fun i => x.extractLsb' ((3-i)*8) 8
  have hmask : maskPartial 32 4 = 0 := by decide +kernel
  unfold Byte_Reverse
  simp only [assert_of_true (by decide : decide ((0:Int) ≤ 4) = true), pure_bind]
  rw [intRange_zero 4 _ (by decide)]
  change (forIn _ (⟨immPartial b 0, maskPartial 32 0⟩ : Runtime.InitializedBits 32) _ >>= _) = _
  rw [except_forIn_range' (ε := Runtime.Error Empty) (fun i : Nat => (0:Int)+i) _
    (fun i => (⟨immPartial b i, maskPartial 32 i⟩ : Runtime.InitializedBits 32)) 4 0 ?_]
  · change ((Runtime.InitializedBits.mk (size := 32) (immPartial b 4) (maskPartial 32 4)).read : Except (Runtime.Error Empty) (BitVec 32)) = .ok (bswap32 x)
    exact read_mk _ _ (by decide) hmask
  · intro i _ hi
    have h1 : (i:Int)*8+8 ≤ 32 := by omega
    have h2 : 0 ≤ (i:Int)*8 := by omega
    have h3 : ((3:Int)-i)*8+8 ≤ 32 := by omega
    have h4 : 0 ≤ ((3:Int)-i)*8 := by omega
    have h5 : (((3:Int)-i)*8).toNat = (3-i)*8 := by omega
    have h6 : ((i:Int)*8).toNat = 8*i := by omega
    simp only [Int.zero_add, show (4:Int)-1 = 3 from rfl,
      h2, h4, decide_true, assert_of_true rfl, pure_bind,
      checkedSliceRead_eq_pure x h4 (by decide) h3, h5]
    simp only [Runtime.InitializedBits.writeSlice, x86_runtime, h1, h2, h3, h6, immPartial,
      maskPartial, b, pure_bind]
    rfl

theorem bswap32_operation (x : BitVec 32) :
    X86.Instructions.Operations.BSWAP 32 x = .ok (bswap32 x) := by
  unfold X86.Instructions.Operations.BSWAP
  simp only [Runtime.assertWithProof, Bool.or_false, Bool.false_or, Int.reduceBEq,
    ↓reduceDIte, pure_bind, Bool.false_eq_true, ↓reduceIte]
  simp [Runtime.remember, Std.Integer.Positive_Divide, Runtime.Positive_Divide,
    liftM, monadLift, Runtime.assert, pure, Except.pure, bind, Except.bind,
    byteReverse32]

theorem bswap32_operation_run {σ : Type} (s : X86.State σ) (x : BitVec 32) :
    (liftM (X86.Instructions.Operations.BSWAP 32 x) :
      X86.Runtime.SpecM X86.Exception (X86.State σ) (BitVec 32)).run s =
      (.ok (bswap32 x), s) := by
  rw [bswap32_operation]
  rfl

theorem bswap_r32_form {σ : Type} [PhysicalMemory σ] (s : X86.State σ)
    (ip : BitVec 64) (ctx : Instruction_Context) (op : BitVec 8)
    (hmode : In64BitMode s) (hsize : ctx.operand_size = 32)
    (hlock : ctx.lock_prefix_present = false) :
    (X86.Instructions.BSWAP_GPRv ip ctx op).run s =
      let dst : Operand 32 := .reg (gprNumber ctx.rex_b4 ctx.rex_b3 (op.extractLsb' 0 3))
      (.ok (), writeResult s dst (bswap32 (dst.read s)) ip) := by
  have hcontext : {ctx with operand_size := 32, lock_prefix_present := false} = ctx := by
    cases ctx
    simp_all
  rw [← hcontext]
  unfold X86.Instructions.BSWAP_GPRv
  simp only [Operand.read_reg32, writeResult, Operand.write_reg32]
  spec_run [Read_GPR => readGPR32_run _ _ hmode,
    liftM => bswap32_operation_run _ _,
    Write_GPR => writeGPR32_run _ _ _ (hmode.of_cs_lma_eq rfl rfl)]

theorem bswap_r32_rex_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (rex op : UInt8) (hrex : RexNoWPrefix rex.toBitVec)
    (hop : op.toBitVec ∈ bswapOpcodes)
    (hcode : BytesAt s s.RIP [rex, 0x0f, op]) (hlow : s.RIP.toNat+3 ≤ 2^32) :
    let dst : Operand 32 := .reg (gprNumber 0 (rexB rex.toBitVec) (op.toBitVec.extractLsb' 0 3))
    X86.Machine.step s = some (.next (afterStep s 3 fun t =>
      writeResult t dst (bswap32 (dst.read t)) (BitVec.add s.RIP 3#64))) := by
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
    bswap_r32_form _ _ _ _ hmode (hrex.operand_size s.DS) rfl,
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

theorem bswap_r32_step [Bindings] (s : RamState) (h : ReadyToStep s)
    (op : UInt8)
    (hop : op.toBitVec ∈ bswapOpcodes)
    (hcode : BytesAt s s.RIP [0x0f, op]) (hlow : s.RIP.toNat+2 ≤ 2^32) :
    let dst : Operand 32 := .reg (gprNumber 0 0 (op.toBitVec.extractLsb' 0 3))
    X86.Machine.step s = some (.next (afterStep s 2 fun t =>
      writeResult t dst (bswap32 (dst.read t)) (BitVec.add s.RIP 2#64))) := by
  have hf : (Mem_Fetch (BitVec.add s.RIP 1#64) 8).run (afterFetches (beforeFetch s) 2) =
      (.ok op.toBitVec, afterFetches (beforeFetch s) 3) :=
    memFetch_run_of_bytesAt (beforeFetch s) 2 h.fetchReady hcode hlow 1 (by simp) (by decide)
  have hmode : In64BitMode (afterFetches (beforeFetch s) 3) :=
    in64BitMode_of_userCodeSegment h.cpu.cs h.cpu.efer.lma
  have hfeatures : DecoderFeatures (afterFetches (beforeFetch s) 3) :=
    DecoderFeatures.of_sameControls (s := s) ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl⟩ h.features
  have hd := decodeLegacy1_bswap_dispatch _ _ _ (legacyContext s.DS)
    op.toBitVec hop rfl hmode hf
  rw [decodeLegacy1Opcode_bswap _ _ _ _ hmode hfeatures,
    bswap_r32_form _ _ _ _ hmode (legacyContext_operand_size s.DS) rfl,
    show BitVec.add (BitVec.add s.RIP 1#64) 1#64 = BitVec.add s.RIP 2#64 from
      BitVec.add_assoc s.RIP 1#64 1#64] at hd
  have hop' : op ≠ 0x38 ∧ op ≠ 0x3a := by
    simp only [bswapOpcodes, List.mem_cons, List.not_mem_nil, or_false] at hop
    rcases hop with h | h | h | h | h | h | h | h <;>
      (have hh := congrArg UInt8.ofBitVec h
       simp only [UInt8.ofBitVec_toBitVec] at hh
       rw [hh]
       decide +kernel)
  apply eq_of_finishDecoded (fun t : RamState => some (StepResult.next (finishStep t)))
  · exact h.ready.repeatClear
  exact step_none_legacy1 s _ h op [] hop' hcode hlow hd
    (hmode.of_cs_lma_eq rfl rfl)

def encodeBswapR32 (dst : BitVec 4) : List UInt8 :=
  let op := UInt8.ofNat (0xc8 + dst.toNat % 8)
  if dst.toNat < 8 then [0x0f, op] else [0x41, 0x0f, op]

theorem encodeBswapR32_spec (dst : BitVec 4) :
    (∃ op, encodeBswapR32 dst = [0x0f, op] ∧ op.toBitVec ∈ bswapOpcodes ∧
      gprNumber 0 0 (op.toBitVec.extractLsb' 0 3) = dst.setWidth 5) ∨
    (∃ rex op, encodeBswapR32 dst = [rex, 0x0f, op] ∧ RexNoWPrefix rex.toBitVec ∧
      op.toBitVec ∈ bswapOpcodes ∧
      gprNumber 0 (rexB rex.toBitVec) (op.toBitVec.extractLsb' 0 3) = dst.setWidth 5) := by
  by_cases hlow : dst.toNat < 8
  · refine .inl ⟨_, ite_eq_left hlow, ?_⟩
    revert dst
    decide +kernel
  · refine .inr ⟨_, _, ite_eq_right hlow, ?_⟩
    unfold RexNoWPrefix
    revert dst
    decide +kernel

def bswapR32Effect (p : BitVec 64) (len : Nat) (dst : BitVec 5) (s : RamState) : Effect :=
  { rip := p + BitVec.ofNat 64 len
    writes := [⟨(Operand.reg dst : Operand 64),
      (bswap32 ((Operand.reg dst : Operand 32).read s)).setWidth 64⟩] }

theorem bswapR32Effect_components (p : BitVec 64) (len : Nat) (dst : BitVec 5)
    (s : RamState) : (bswapR32Effect p len dst s).components = [.reg dst, .rip] := rfl

theorem bswap_r32_effect_step_of_bytes [Bindings] (p : BitVec 64) (op : UInt8)
    (hop : op.toBitVec ∈ bswapOpcodes) :
    StepEffect (fun s => s.RIP = p) (codeRange p [0x0f, op])
      (bswapR32Effect p 2 (gprNumber 0 0 (op.toBitVec.extractLsb' 0 3))) := by
  rintro s h hc rfl
  refine ⟨_, bswap_r32_step s h op hop hc.bytesAt (hc.low (by simp) (by simp)),
    ReadyToStep.afterStep_writeResult h 2 _ _ _,
    ⟨afterStep_writeResult_rip h 2 _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s 2 _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self32, Operand.read_afterFetches,
    Operand.read_beforeFetch]

theorem bswap_r32_rex_effect_step_of_bytes [Bindings] (p : BitVec 64) (rex op : UInt8)
    (hrex : RexNoWPrefix rex.toBitVec) (hop : op.toBitVec ∈ bswapOpcodes) :
    StepEffect (fun s => s.RIP = p) (codeRange p [rex, 0x0f, op])
      (bswapR32Effect p 3 (gprNumber 0 (rexB rex.toBitVec) (op.toBitVec.extractLsb' 0 3))) := by
  rintro s h hc rfl
  refine ⟨_, bswap_r32_rex_step s h rex op hrex hop hc.bytesAt (hc.low (by simp) (by simp)),
    ReadyToStep.afterStep_writeResult h 3 _ _ _,
    ⟨afterStep_writeResult_rip h 3 _ _ _, ?_, trivial,
      AgreesExcept.afterStep_writeResult s 3 _ _ _⟩⟩
  show Operand.read _ _ = _
  rw [Operand.read_afterStep]
  simp only [Operand.read_writeResult_self32, Operand.read_afterFetches,
    Operand.read_beforeFetch]

theorem bswap_r32_effect_step [Bindings] (p : BitVec 64) (dst : BitVec 4) :
    StepEffect (fun s => s.RIP = p) (codeRange p (encodeBswapR32 dst))
      (bswapR32Effect p (encodeBswapR32 dst).length (dst.setWidth 5)) := by
  rcases encodeBswapR32_spec dst with ⟨op, hcode, hop, hdst⟩ |
    ⟨rex, op, hcode, hrex, hop, hdst⟩
  · rw [hcode, ← hdst]
    exact bswap_r32_effect_step_of_bytes p op hop
  · rw [hcode, ← hdst]
    exact bswap_r32_rex_effect_step_of_bytes p rex op hrex hop

theorem bswap_r32_triple [Bindings] (p : BitVec 64) (dst : BitVec 4) :
    Triple (fun s => s.RIP = p) (codeRange p (encodeBswapR32 dst))
      (Effect.post (bswapR32Effect p (encodeBswapR32 dst).length (dst.setWidth 5))) :=
  Triple.of_effect (fun s _ => Effect.Avoids.of_noMem
    (by simp [bswapR32Effect_components, Component.Covers]) _)
    (bswap_r32_effect_step p dst)

attribute [x86_compose] bswapR32Effect

@[x86_local] theorem bswapR32Effect_local (p : BitVec 64) (len : Nat) (dst : BitVec 5) :
    Effect.Local (bswapR32Effect p len dst) := by
  refine ⟨fun t t' h => ?_, fun t t' h => ?_, fun t t' h => ?_, fun t t' h i hi => ?_,
    fun t => ?_⟩
  · rfl
  · simp [bswapR32Effect, h.read_reg]
  · rfl
  · exact congrArg some hi
  · simp [bswapR32Effect, Write.Full, Operand.Full]
end Hkdf.Proofs.Common.SHA256.Compression
