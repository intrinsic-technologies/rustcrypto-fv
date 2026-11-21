import P256.Proofs.Sec1.Wrapper.Success.Tail.Dispatch
import P256.Proofs.Sec1.Wrapper.Success.Tail.Length
import P256.Proofs.Sec1.Wrapper.Success.Tail.Capacity
import P256.Proofs.Sec1.Wrapper.Success.Tail.Arguments
import P256.Proofs.Sec1.Wrapper.Success.Tail.Memory
import P256.Proofs.HashToCurve.Wrapper.Finish.Encoding

set_option autoImplicit false

namespace P256.Proofs.Sec1.Wrapper.Success.Tail

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem output_capacity [Bindings] {initial : RamState} {input : ByteArray}
    {slices : Array Input} {x y : Nat}
    (valid : ValidCallWithSlices publicKeyFromSec1Bytes initial [input] slices)
    (model : Points.decodePublicKey input = some (.affine x y)) :
    73 ≤ (initial.regValue .r8).toNat := by
  have h := valid.outputSufficesIfAccepted (accepted_of_model model)
  change 8 + resultBytes ((Points.decodePublicKey input).map Keys.uncompressed) ≤ _ at h
  rw [model] at h
  change 8 + (Points.encode (.affine x y)).size ≤ _ at h
  rwa [Sec1Serialize.Prepare.encodePoint_uncompressed_size] at h

theorem prepare [Bindings] {initial s : RamState} {input : ByteArray}
    {slices : Array Input} {x y : Nat}
    (valid : ValidCallWithSlices publicKeyFromSec1Bytes initial [input] slices)
    (model : Points.decodePublicKey input = some (.affine x y))
    (state : ReturnState initial s) (outside : ¬ InProgram (returnBoundary initial).rip)
    (rip : s.RIP = 0x101870) (output : s.regValue .rbx = initial.regValue .rcx)
    (capacity : s.regValue .r14 = initial.regValue .r8)
    (bytes : (MemoryRegion.mk (stackPtr initial - 232).toNat 65).HasBytes s.external
      (Points.encode (.affine x y))) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ ReturnState initial t ∧
      t.RIP = 0x1018cd ∧ t.regValue .rdi = initial.regValue .rcx + 8 ∧
      t.regValue .rsi = stackPtr initial - 232 ∧ t.regValue .rdx = 65 ∧
      t.regValue .r15 = 65 ∧
      AgreesExcept [.reg 0,.reg 1,.reg 2,.reg 6,.reg 7,.reg 15,.flags,.rip] s t := by
  have ready := readyToStep state.machine state.bindingsSupported
  have readable : MemReadable s (stackPtr s) 1 := by
    rw [state.rsp]
    exact readable_of_grow (stack_sub_readable valid.stackAvailable.1
      (offset := 232) (by decide) (by decide)) state.allocated
  have tag : memLoad s.external (stackPtr s) 8 = 4 := by
    rw [state.rsp]
    exact HashToCurve.Wrapper.Finish.encodedPoint_tag
      (point := .affine x y) bytes
  obtain ⟨a, ha, ra, ipa, cx, fa⟩ := tag_dispatch ready state.loaded outside rip readable (.inr tag)
  have sa := state.after_registers ra fa (by simp [Component.Covers]) (by simp) (by simp)
  obtain ⟨b, hb, rb, ipb, len, fb⟩ := length_lookup ra sa.loaded outside ipa 4 (.inr rfl)
    (by rw [cx, tag])
  have sb := sa.after_registers rb fb (by simp [Component.Covers]) (by simp) (by simp)
  have count : b.regValue .r15 = 65 := len
  have capB : b.regValue .r14 = initial.regValue .r8 :=
    ((fa.trans fb).read (n := 64) (r := 14) (by simp)).trans capacity
  obtain ⟨c, hc, rc, ipc, fc⟩ := capacity_branch rb sb.loaded outside ipb (by
    rw [count,capB]
    exact output_capacity valid model)
  have sc := sb.after_registers rc fc (by simp [Component.Covers]) (by simp) (by simp)
  obtain ⟨n,t,ht,rt,_,et⟩ := prepare_arguments (returnBoundary initial) outside c rc
    (programText_slice (programLoaded_codeIn sc.loaded) 0x18c3 argumentsBytes
      (by decide) (by decide +kernel)) ipc
  have ft : AgreesExcept [.reg 7,.reg 6,.reg 2,.rip] c t := et.agrees
  have st := sc.after_registers rt ft (by simp [Component.Covers]) (by simp) (by simp)
  have outC : c.regValue .rbx = initial.regValue .rcx :=
    (((fa.trans fb).trans fc).read (n := 64) (r := 3) (by simp)).trans output
  have lenC : c.regValue .r15 = 65 :=
    (fc.read (n := 64) (r := 15) (by simp)).trans count
  refine ⟨_,t,((ha.trans hb).trans hc).trans ht,st,et.rip,?_,?_,?_,?_,
    (((fa.trans fb).trans fc).trans ft).mono (by simp)⟩
  · exact et.writes.1.trans (congrArg (fun v : BitVec 64 => v+8) outC)
  · exact et.writes.2.1.trans sc.rsp
  · exact et.writes.2.2.trans lenC
  · exact (ft.read (n := 64) (r := 15) (by simp)).trans lenC

end P256.Proofs.Sec1.Wrapper.Success.Tail
