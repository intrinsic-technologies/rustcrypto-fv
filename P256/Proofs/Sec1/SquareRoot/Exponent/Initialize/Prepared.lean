import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.Prefix
import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.ExponentMemory
import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.ParameterValues

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.ExponentInitialize

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open SecretKeyFromBytes.Scalar (Nat256At)
open P256.Proofs.Common.Field.Montgomery.Schoolbook (memLoad_memStore_rangeApart)

def preparedMemory (s : RamState) : Ram :=
  parameterCopiesMemory s initialParameterCopies (exponentSaveCopyMemory s (prefixMemory s))

theorem preparedMemory_output (s : RamState) :
    memLoad (preparedMemory s) (exponentFrameBase s+0x2a0#64) 64 = s.regValue .rdi := by
  unfold preparedMemory
  rw [initialParameterCopies_preserves_word s _ 0x2a0 (by decide) (by decide) (by decide),
    exponentSaveCopyMemory_preserves_word s _ 0x2a0 (by decide)]
  exact memLoad_memStore _ _ (by decide) (by decide) _

theorem preparedMemory_exponent (s : RamState) (j : Nat) (hj : j<4) :
    memLoad (preparedMemory s) (exponentFrameBase s+0x538#64+BitVec.ofNat 64 (8*j)) 64 =
      BitVec.ofNat 64 (sqrtExponent / 2^(64*j)) := by
  unfold preparedMemory
  rw [BitVec.add_assoc,← BitVec.ofNat_add,
    initialParameterCopies_preserves_word s _ (0x538+8*j) (by omega)
      (by omega) (by omega)]
  simpa only [BitVec.ofNat_add,← BitVec.add_assoc,BitVec.ofNat_eq_ofNat] using
    exponentSaveCopyMemory_word s (prefixMemory s) j hj

set_option maxRecDepth 2048 in
theorem preparedMemory_input (s : RamState) (j : Nat) (hj : j<4) :
    memLoad (preparedMemory s) (exponentFrameBase s+0x2f8#64+BitVec.ofNat 64 (8*j)) 64 =
      memLoad s.external (s.regValue .rsi+BitVec.ofNat 64 (8*j)) 64 := by
  unfold preparedMemory
  rw [BitVec.add_assoc,← BitVec.ofNat_add,
    initialParameterCopies_preserves_word s _ (0x2f8+8*j) (by omega) (by omega) (by omega),
    exponentSaveCopyMemory_preserves_word s _ (0x2f8+8*j) (by omega)]
  unfold prefixMemory
  change memLoad (memStore _ (exponentFrameBase s+BitVec.ofNat 64 0x2a0) _) _ 64 = _
  rw [memLoad_memStore_rangeApart _ _ _ _ 64
    (RangeApart.offsets (exponentFrameBase s) (by omega) (by omega) (by omega))]
  simp only [exponentCopyMemory,List.foldl_cons,List.foldl_nil]
  repeat rw [memLoad_memStore_rangeApart _ _ _ _ 64
    (RangeApart.offsets (exponentFrameBase s) (by omega) (by omega) (by omega))]
  simpa only [BitVec.ofNat_add,← BitVec.add_assoc,BitVec.ofNat_eq_ofNat] using
    inputCopyMemory_word s (saveMemory s) j hj

theorem initialize_copies [Bindings] {s : RamState} {boundary : ReturnBoundary} {x : Nat}
    (ctx : ExponentPre s boundary x) :
    ∃ u, Advances boundary 160 s u ∧ ExponentFrame s u ∧ u.RIP=0x114f3a ∧
      u.regValue .rax=exponentFrameBase s+0xc0 ∧ u.regValue .r14=254 ∧
      u.regValue .r15=s.regValue .rsi+32 ∧ u.regValue .rsi=s.regValue .rsi ∧
      u.external=preparedMemory s ∧ Field.MontgomeryAt u (exponentFrameBase s+0x2f8) x ∧
      Nat256At u (exponentFrameBase s+0x538) sqrtExponent ∧
      (∀ i<16, i≠1 → Field.MontgomeryAt u
        (exponentFrameBase s+BitVec.ofNat 64 (0xa0+32*i)) 1) := by
  obtain ⟨t,runT,pfx⟩ := initialize_prefix ctx
  obtain ⟨v,runV,frameV,ripV,agreeV,memV⟩ := copy_saved_exponent ctx pfx.frame.scalarFrame
    pfx.rip pfx.exponent
  have parameterV : v.regValue .r15=s.regValue .rsi+32 :=
    (agreeV.read (n := 64) (r := 15) (by simp [exponentSaveCopyComponents])).trans pfx.parameter
  obtain ⟨u,runU,frameU,ripU,agreeU,memU⟩ := initialize_parameter_slots ctx frameV ripV parameterV
  have memory : u.external=preparedMemory s := by rw [memU,memV,pfx.memory]; rfl
  have frame : ExponentFrame s u := ExponentFrame.of_scalarFrame frameU (by
    change memLoad u.external _ 64=_
    rw [memory]
    exact preparedMemory_output s)
  have registers (r : BitVec 5) (hr : r≠1) :
      (Operand.reg r : Operand 64).read u=(Operand.reg r : Operand 64).read t := by
    apply (agreeV.trans agreeU).read
    simpa [exponentSaveCopyComponents,parameterCopiesComponents] using hr
  refine ⟨u,(runT.trans runV).trans runU,frame,ripU,
    (registers 0 (by decide)).trans pfx.firstTable,
    (registers 14 (by decide)).trans pfx.count,
    (registers 15 (by decide)).trans pfx.parameter,
    (registers 6 (by decide)).trans pfx.input,memory,?_,?_,
    initialize_parameter_values ctx frameU _ memU⟩
  · apply Field.montgomeryAt_of_memLoad_limbs ctx.residue.1.1
    · have read := ScalarFrame.stack_readable ctx.toCalleePre frameU
        (offset := 0x2f8) (len := 32) (by decide) (by decide)
      have sp : stackPtr u=exponentFrameBase s := frameU.rsp
      rw [sp] at read
      exact read.mem
    · intro j hj
      rw [memory]
      exact (preparedMemory_input s j hj).trans (ctx.residue.1.memLoad_limb j hj)
  · apply SecretKeyFromBytes.Scalar.nat256At_of_memLoad_limbs (by decide +kernel)
    · have read := ScalarFrame.stack_readable ctx.toCalleePre frameU
        (offset := 0x538) (len := 32) (by decide) (by decide)
      have sp : stackPtr u=exponentFrameBase s := frameU.rsp
      rw [sp] at read
      exact read.mem
    · intro j hj
      rw [memory]
      exact preparedMemory_exponent s j hj

end P256.Proofs.Sec1.SquareRoot.ExponentInitialize
