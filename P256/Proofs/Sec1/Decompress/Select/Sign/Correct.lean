import P256.Proofs.Sec1.Decompress.Select.Parity.Correct
import P256.Proofs.Sec1.Decompress.Select.Sign.Bit
import P256.Proofs.Sec1.Decompress.Select.Sign.Setup
import P256.Proofs.Sec1.Decompress.Select.State
import P256.Proofs.Sec1.Decompress.Select.Model
import P256.Proofs.PublicPoint.Normalize.Invert.SelectCall
import P256.Proofs.Projective.Multiply.Machine.Lookup.Select.Correct
import P256.Proofs.Field.Inverse.Tail.Support

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decompress.Select.Sign
open P256.Proofs.Program P256.Proofs.Program.FieldCall P256.Proofs.Field
open P256.Proofs.Sec1.Decompress.Cubic (input_stack_address montgomeryAt_of_copy)
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def selectSite : BinaryCallSite 2592 408 0x114380 128 where
  codeOffset := 0x1005a
  disp := 0x4321
  codeBound := by decide
  bytes := by decide +kernel
  target := by decide +kernel
  entryLow := by decide
  entryProgram := inProgram_of_textOffset 0x14380 (by decide)
  layout := {
    stackOffset := 416
    inputOffset := 112
    outputOffset := 376
    aligned := by decide
    capacity := by decide
    inputAbove := by decide
    outputAbove := by decide
    inputEnd := by decide
    outputEnd := by decide
    separation := .inr (by decide) }
  stack := rfl
  outputSaved := by decide
  rightOffset := 256
  rightAbove := by decide
  rightEnd := by decide
  rightApart := .inr (by decide)

theorem correct [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {x : Nat} {sign : Bool}
    (pre : CalleePre s boundary 0x10fc00 32 80 2592)
    (state : CandidateState s t x sign) :
    ∃ fuel u, Advances boundary fuel t u ∧ SelectedState s u x sign := by
  obtain ⟨np,p,rp,readyp,framep,ipp,parity,ap⟩ := Parity.correct pre state.toFrameState
    state.rip state.root state.r14
  have memoryp := ap.external (by simp [Parity.registers,Component.Covers])
  have signp : (Operand.mem (stackPtr s-332) : Operand 8).read p = BitVec.ofNat 8 sign.toNat := by
    have h := congrArg (fun x : BitVec 32 => x.setWidth 8) state.parity
    change (memLoad t.external (stackPtr s-332) 32).setWidth 8 =
      (BitVec.ofNat 32 sign.toNat).setWidth 8 at h
    rw [P256.Proofs.Field.Inverse.memLoad32_lowByte] at h
    change memLoad p.external (stackPtr s-332) 8 = _
    rw [memoryp,memLoad_8]
    simpa only [BitVec.setWidth_ofNat_of_le (by decide : 8 ≤ 32)] using h
  obtain ⟨nb,b,rb,frameb,ipb,bit,ab⟩ := selection_bit pre framep (candidateRoot x) sign ipp parity signp
  obtain ⟨ns,w,rs,readyw,_,es⟩ := setup boundary pre.outerBoundary b
    (readyToStep frameb.machine frameb.bindingsSupported)
    (programText_slice (programLoaded_codeIn frameb.loaded) 0x1004c setupBytes
      (by decide) (by decide +kernel)) ipb
  have as : AgreesExcept [.reg 7,.reg 1,.reg 6,.reg 2,.rip] b w := es.agrees
  have framew := frameb.after_registers readyw as (by simp [Component.Covers]) (by simp)
  have apw : AgreesExcept (components s) p w :=
    (ab.trans as).mono (by simp [components])
  have vout : w.regValue .rdi=stackPtr s-376 :=
    es.writes.1.trans (input_stack_address frameb.rsp (by decide))
  have vin : w.regValue .rsi=stackPtr s-112 :=
    es.writes.2.2.1.trans ((ab.read (n := 64) (r := 13) (by simp [components])).trans
      ((ap.read (n := 64) (r := 13) (by simp [Parity.registers])).trans state.negativeBase))
  have vright : w.regValue .rdx=stackPtr s-256 :=
    es.writes.2.2.2.trans ((ab.read (n := 64) (r := 12) (by simp [components])).trans
      ((ap.read (n := 64) (r := 12) (by simp [Parity.registers])).trans state.base))
  have choose : w.regValue .rcx = if candidateRoot x%2 == sign.toNat then 1 else 0 := by
    have h : w.regValue .rcx = ((Operand.reg 0 : Operand 8).read b).setWidth 64 := es.writes.2.1
    rw [bit] at h
    split at h <;> simp_all
  have copy {offset x : Nat} (ho : offset ≤ 408) (hl : 32 ≤ offset+8)
      (h : MontgomeryAt t (stackPtr s-BitVec.ofNat 64 offset) x) :
      MontgomeryAt w (stackPtr s-BitVec.ofNat 64 offset) x := by
    apply montgomeryAt_of_copy h
    intro i hi
    exact (byte_preserved apw ho hl hi).trans (by rw [memoryp])
  have negw := copy (offset := 112) (by decide) (by decide) state.negative
  have rootw := copy (offset := 256) (by decide) (by decide) state.root
  obtain ⟨nc,u,rc,frameu,ipu,value,abi,bytes,_⟩ := PublicPoint.Normalize.select_binary_call pre framew selectSite
    (op := fun a b => if candidateRoot x%2 == sign.toNat then b else a)
    (fun v cp hrcx hx hy => Projective.Multiply.Machine.Lookup.Select.field_select_correct cp hx hy (hrcx.trans choose))
    es.rip vin vright vout negw rootw
  refine ⟨np+nb+ns+nc,u,((rp.trans rb).trans rs).trans rc,
    { toFrameState := frameu, rip := ipu, valid := ?_, rootValid := ?_, coordinates := ?_, output := ?_ }⟩
  · have preserved : (Operand.mem (stackPtr s-224) : Operand 64).read u =
        (Operand.mem (stackPtr s-224) : Operand 64).read w := by
      apply memLoad_congr
      intro i hi
      exact congrArg (fun x : Option UInt8 => x.getD 0)
        (bytes 224 8 (by decide) (by decide) (.inl (by decide)) i hi)
    change (Operand.mem (stackPtr s-224) : Operand 64).read u = _
    rw [preserved]
    have hread := read_preserved apw (offset := 224) (n := 64) (by decide) (by decide)
    change (Operand.mem (stackPtr s-224) : Operand 64).read w =
      (Operand.mem (stackPtr s-224) : Operand 64).read p at hread
    rw [hread]
    change memLoad p.external _ _ = _
    rw [memoryp]
    exact state.output
  · exact (abi .rbp (by simp)).trans ((apw.read (n := 64) (r := 5) (by simp [components])).trans
      ((ap.read (n := 64) (r := 5) (by simp [Parity.registers])).trans state.valid))
  · have h : u.regValue .r15=t.regValue .r15 :=
      (abi .r15 (by simp)).trans ((apw.read (n := 64) (r := 15) (by simp [components])).trans
        (ap.read (n := 64) (r := 15) (by simp [Parity.registers])))
    rw [h]
    exact state.rootValid
  · intro y hy
    obtain ⟨hx, hyvalue⟩ := decompress_coordinates hy
    have xw := copy (offset := 288) (by decide) (by decide) state.xCoordinate
    refine ⟨?_, ?_⟩
    · have xu := xw.of_bytes_eq
        (bytes 288 32 (by decide) (by decide) (.inl (by decide)))
      simpa only [checkedX, hx, ↓reduceIte, BitVec.ofNat_eq_ofNat] using xu
    · rw [hyvalue]
      exact value

end P256.Proofs.Sec1.Decompress.Select.Sign
