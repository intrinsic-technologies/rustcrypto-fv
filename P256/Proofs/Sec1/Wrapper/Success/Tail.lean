import P256.Proofs.Sec1.Wrapper.Success.Tail.Prepare
import P256.Proofs.Sec1.Wrapper.Success.Tail.Copy
import P256.Proofs.Sec1.Wrapper.Success.Tail.Control
import P256.Proofs.Sec1.Wrapper.Success.Tail.LengthGuard
import P256.Proofs.Sec1.Wrapper.Success.Tail.Store
import P256.Proofs.Sec1.Wrapper.Success.Tail.State
import P256.Proofs.Sec1.Wrapper.Restore
import P256.Proofs.Program.Output

set_option autoImplicit false

namespace P256.Proofs.Sec1.Wrapper.Success.Tail

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem correct [bindings : Bindings] {initial s : RamState} {input : ByteArray}
    {slices : Array Input} {x y : Nat}
    (valid : ValidCallWithSlices publicKeyFromSec1Bytes initial [input] slices)
    (model : Points.decodePublicKey input = some (.affine x y))
    (state : ReturnState initial s) (outside : ¬ InProgram (returnBoundary initial).rip)
    (low : (returnBoundary initial).rip.toNat < 2^32)
    (rip : s.RIP = 0x101870) (output : s.regValue .rbx = initial.regValue .rcx)
    (capacity : s.regValue .r14 = initial.regValue .r8)
    (bytes : (MemoryRegion.mk (stackPtr initial - 232).toNat 65).HasBytes s.external
      (Points.encode (.affine x y))) :
    ∃ fuel final, Returns (returnBoundary initial) fuel s final ∧
      SupportedIntegerMachineState bindings.processor final ∧
      MachineRamUnitStrideDecodable bindings final ∧
      CalleeSavedRegistersUnchanged initial final ∧ DirectionFlagUnset final ∧
      SuccessfulStatus final ∧
      MemoryWriteFrame s final #v[outputRegion publicKeyFromSec1Bytes initial [input],
        allocatorStateRegion,randomSourceRegion,callStack publicKeyFromSec1Bytes initial] ∧
      readOutput publicKeyFromSec1Bytes initial final = .ok (Points.encode (.affine x y)) := by
  obtain ⟨na,a,ha,sa,ipa,dst,src,count,length,fa⟩ :=
    prepare valid model state outside rip output capacity bytes
  have memoryA := fa.external (by simp [Component.Covers])
  obtain ⟨nb,b,hb,rb,lb,ipb,spb,fb,payload⟩ := copy valid model sa outside ipa src dst count
    (by simpa only [memoryA] using bytes)
  have sb := state_after_write valid model sa rb lb spb
    (fb.mono (by simp [copyChanges,tailChanges]))
  have outD : b.regValue .rbx = initial.regValue .rcx :=
    ((fa.trans fb).read (n := 64) (r := 3) (by simp [copyChanges])).trans output
  have lenD : b.regValue .r15 = 65 :=
    (fb.read (n := 64) (r := 15) (by simp [copyChanges])).trans length
  obtain ⟨e,he,re,le,ipe,statusE,lengthE,fe⟩ := store valid model
    (readyToStep sb.machine sb.bindingsSupported) sb.loaded sb.allocated outside ipb outD lenD
  have se := state_after_write valid model sb re le
    ((fe.read (n := 64) (r := 4) (by simp)).trans sb.rsp)
    (fe.mono (by simp [tailChanges]))
  obtain ⟨final,returned,machine,supported,savedRegs,direction,memory,status⟩ :=
    restore se valid.stackAvailable.1 outside low ipe
  have agrees : AgreesExcept (tailChanges initial) s e :=
    ((fa.trans fb).trans fe).mono (by simp [copyChanges,tailChanges])
  refine ⟨_,final,((ha.trans hb).trans he).returns returned,
    machine,supported,savedRegs,direction,?_,?_,?_⟩
  · change (final.regValue .rax).setWidth 32 = 0
    rw [status,statusE]
    rfl
  · intro addr apart
    rw [memory]
    exact tail_frame valid model agrees addr apart
  · have size := Sec1Serialize.Prepare.encodePoint_uncompressed_size x y
    apply readOutput_of_bytes (by rw [size]; decide)
    · change Bytes final.external (initial.regValue .rcx) 8
        (storedByte (BitVec.ofNat 64 (Points.encode (.affine x y)).size))
      simpa only [size,memory] using lengthE
    · intro i hi
      change final.external[initial.regValue .rcx + 8 + BitVec.ofNat 64 i]? = _
      rw [memory]
      apply fe.byte ?_ |>.trans (payload i (by rwa [size] at hi))
      intro comp member covers
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl | rfl
      all_goals try exact covers.elim
      obtain ⟨j,hj,eq⟩ := covers
      apply RangeApart.offsets (initial.regValue .rcx) (a := 0) (b := 8)
        (len := 8) (count := 65) (by decide) (by decide) (.inl (by decide)) j hj i
        (by rwa [size] at hi)
      simpa only [BitVec.ofNat_eq_ofNat,BitVec.add_zero] using eq.symm

end P256.Proofs.Sec1.Wrapper.Success.Tail
