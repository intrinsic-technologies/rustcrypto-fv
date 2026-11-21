import P256.Proofs.Sec1.Wrapper.Success.Tail.Memory

set_option autoImplicit false

namespace P256.Proofs.Sec1.Wrapper.Success.Tail

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def tailChanges (initial : RamState) : List Component :=
  [.reg 0,.reg 1,.reg 2,.reg 4,.reg 6,.reg 7,.reg 8,.reg 15,.flags,.rip,
    .mem (initial.regValue .rcx + 8) 65,.mem (stackPtr initial - 240) 8,
    .mem (initial.regValue .rcx) 8]

theorem state_after_write [Bindings] {initial s t : RamState} {input : ByteArray}
    {slices : Array Input} {x y : Nat}
    (valid : ValidCallWithSlices publicKeyFromSec1Bytes initial [input] slices)
    (model : Points.decodePublicKey input = some (.affine x y))
    (state : ReturnState initial s) (ready : ReadyToStep t) (loaded : ProgramLoaded t)
    (rsp : stackPtr t = stackPtr initial - 232)
    (agrees : AgreesExcept (tailChanges initial) s t) : ReturnState initial t := by
  have saved (off : Nat) (bound : off ≤ 24) :
      memLoad t.external (stackPtr initial - BitVec.ofNat 64 off) 64 =
        memLoad s.external (stackPtr initial - BitVec.ofNat 64 off) 64 := by
    apply memLoad_agrees_apart agrees
    intro address n member
    simp only [tailChanges, List.mem_cons, List.not_mem_nil, or_false,
      Component.mem.injEq, reduceCtorEq, false_or] at member
    rcases member with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    · exact output_apart_stack valid model (off := off) (len := 8)
        (outOff := 8) (outLen := 65) (by omega) (by omega) (by decide)
    · exact stack_sub_apart valid.stackAvailable.1 (a := 240) (b := off) (na := 8) (nb := 8)
        (by decide) (by change off ≤ 4048; omega) (by decide) (by omega) (.inl (by omega))
    · simpa only [BitVec.add_zero] using output_apart_stack valid model
        (off := off) (len := 8) (outOff := 0) (outLen := 8)
        (by omega) (by omega) (by decide)
  refine ⟨bindingsSupported_of_ready_agrees state.bindingsSupported ready agrees,
    supportedMachine_of_ready_agrees state.machine ready agrees, loaded,
    agrees.directionFlagClear (by simp [tailChanges]) state.directionFlag,rsp,
    (saved 24 (by decide)).trans state.savedRbx,
    (saved 16 (by decide)).trans state.savedR14,
    (saved 8 (by decide)).trans state.savedR15,?_,?_,
    fun a ha => agrees.grow a (state.allocated a ha)⟩
  · have eq := saved 0 (by decide)
    simp only [BitVec.sub_zero] at eq
    exact eq.trans state.returnAddress
  · intro r hr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl
    · exact (agrees.read (n := 64) (r := 5) (by simp [tailChanges])).trans
        (state.otherRegisters .rbp (by simp))
    · exact (agrees.read (n := 64) (r := 12) (by simp [tailChanges])).trans
        (state.otherRegisters .r12 (by simp))
    · exact (agrees.read (n := 64) (r := 13) (by simp [tailChanges])).trans
        (state.otherRegisters .r13 (by simp))

theorem tail_frame [Bindings] {initial s t : RamState} {input : ByteArray}
    {slices : Array Input} {x y : Nat}
    (valid : ValidCallWithSlices publicKeyFromSec1Bytes initial [input] slices)
    (model : Points.decodePublicKey input = some (.affine x y))
    (agrees : AgreesExcept (tailChanges initial) s t) :
    MemoryWriteFrame s t #v[outputRegion publicKeyFromSec1Bytes initial [input],
      allocatorStateRegion, randomSourceRegion,callStack publicKeyFromSec1Bytes initial] := by
  apply agrees.memoryWriteFrame
  intro comp member addr covers
  simp only [tailChanges,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl
  all_goals try exact covers.elim
  · exact ⟨_,by simp,output_contains valid model (off := 8) (len := 65) (by decide) covers⟩
  · exact ⟨_,by simp,stack_component_within valid.stackAvailable.1
      (offset := 240) (by decide) (by decide) covers⟩
  · exact ⟨_,by simp,output_contains valid model (off := 0) (len := 8) (by decide)
      (by simpa only [BitVec.add_zero] using covers)⟩

end P256.Proofs.Sec1.Wrapper.Success.Tail
