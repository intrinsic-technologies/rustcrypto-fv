import P256.Proofs.SecretKeyFromBytes.Encoding
import P256.Proofs.SignatureFromDer.Fixed.Scalar.Entry
import P256.Proofs.SignatureFromDer.Fixed.Scalar.Decode.ReadBeCall
import P256.Proofs.ReadBe.Correct

set_option autoImplicit false

open P256.Proofs.Program (CalleePre inProgram_of_textOffset)

namespace P256.Proofs.SignatureFromDer.Fixed.Scalar

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure DecodedState [Bindings] (s t : RamState) (boundary : ReturnBoundary)
    (input : ByteArray) : Prop extends FrameState s t where
  execution : ∃ fuel, Advances boundary fuel s t
  rip : t.RIP = 0x10faaf
  output : t.regValue .rbx = s.regValue .rdi
  tag : t.regValue .r14 = 1
  status : (Operand.reg 0 : Operand 8).read t = 255
  value : P256.Proofs.SecretKeyFromBytes.Scalar.Nat256At t (stackPtr s - 112) (Arith.uint input)
  inputSize : input.size = 32

theorem scalar_decode [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {input : ByteArray} (pre : CalleePre s boundary 0x10fa20 32 40 288)
    (length : s.regValue .rdx = 32)
    (bytes : (registerRegion s .rsi 32).HasBytes s.external input) :
    ∃ t, DecodedState s t boundary input := by
  obtain ⟨u, stateU⟩ := scalar_entry pre length bytes
  have target : branchTarget (Extracted.textAddress + BitVec.ofNat 64 0xfaaa) 5
      ((0x95e1 : BitVec 32).signExtend 64) = 0x119090 := by decide +kernel
  obtain ⟨v, runV, readyV, effectV⟩ := Program.ScalarFrame.scalar_call (frameOffset := 152) pre (by decide) (by decide) stateU.toFrameState 0xfaaa 0x95e1
    (by decide +kernel) (by decide +kernel) (by rw [target]; decide +kernel)
    (by rw [target]; exact inProgram_of_textOffset 0x19090 (by decide)) stateU.rip
  have stateV := Program.ScalarFrame.FrameState.after_call (frameOffset := 152) pre (by decide) (by decide) stateU.toFrameState readyV effectV
  have srcV : v.regValue .rdi = stackPtr s - 80 :=
    (effectV.agrees.read (n := 64) (r := 7) (by simp)).trans stateU.source
  have dstV : v.regValue .rdx = stackPtr s - 112 :=
    (effectV.agrees.read (n := 64) (r := 2) (by simp)).trans stateU.destination
  have ret : (returnBoundary v).rip = 0x10faaf := (callEffect_stack effectV).1
  have cp := readBe_pre pre stateV (effectV.rip.trans target) srcV dstV
    ((effectV.agrees.read (n := 64) (r := 6) (by simp)).trans stateU.count)
    ((effectV.agrees.read (n := 64) (r := 1) (by simp)).trans stateU.limbs)
    ((effectV.agrees.read (n := 64) (r := 8) (by simp)).trans stateU.bits)
    (by rw [ret]; exact inProgram_of_textOffset 0xfaaf (by decide))
  have inputV : (registerRegion v .rdi 32).HasBytes v.external input := by
    refine ⟨stateU.bytes.1, ?_⟩
    intro i
    have hi : i.val < 32 := by have := i.isLt; have size : input.size = 32 := stateU.bytes.1; omega
    change v.external[BitVec.ofNat 64 ((v.regValue .rdi).toNat + i.val)]? = _
    rw [srcV, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    have preserved := Program.ScalarFrame.scalar_call_byte (frameOffset := 152) (by decide) stateU.toFrameState effectV (offset := 80) (len := 32)
      (by decide) (by decide) hi
    change v.external[stackPtr s - 80 + BitVec.ofNat 64 i.val]? =
      u.external[stackPtr s - 80 + BitVec.ofNat 64 i.val]? at preserved
    rw [preserved]
    have h := stateU.bytes.2 i
    change u.external[BitVec.ofNat 64 ((stackPtr s - 80).toNat + i.val)]? = _ at h
    simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using h
  obtain ⟨t, result⟩ := P256.Proofs.ReadBe.read_be_correct cp inputV
  have stateT := readBe_result_frame pre stateV result dstV
  obtain ⟨n, runU⟩ := stateU.execution
  obtain ⟨m, runT⟩ := result.execution
  refine ⟨t, ⟨stateT, ⟨n + 1 + m, (runU.trans runV).trans runT⟩,
    result.rip.trans ret, ?_, ?_, result.status, ?_, bytes.1⟩⟩
  · exact (result.calleeSaved .rbx (by simp)).trans
      ((effectV.agrees.read (n := 64) (r := 3) (by simp)).trans stateU.output)
  · exact (result.calleeSaved .r14 (by simp)).trans
      ((effectV.agrees.read (n := 64) (r := 14) (by simp)).trans stateU.tag)

  · apply P256.Proofs.SecretKeyFromBytes.Scalar.nat256At_of_memLoad_limbs
    · have hsize : input.size = 32 := bytes.1
      simpa only [Arith.uint, Arith.decodeBigEndian, hsize, show (256:Nat)^32 = 2^256 by decide +kernel] using
        P256.Proofs.SecretKeyFromBytes.Encoding.octetsToNat_lt input
    · intro i hi
      apply stateT.allocated
      exact (P256.Proofs.Program.stack_sub_readable pre.stack (offset := 112) (len := 32)
        (by decide) (by decide)).mem i hi
    · exact dstV ▸ result.value

end P256.Proofs.SignatureFromDer.Fixed.Scalar
