import P256.Proofs.Signing.Wrapper.Entry.Decode.Entry
import P256.Proofs.ReadBe.Interface
import P256.Proofs.Program.Call

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Entry.Decode

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [bindings : Bindings] {initial s t : RamState} {input message : ByteArray}

theorem readBe_pre (hc : ValidCall signingKeyTrySign initial [input,message])
    (hb : MachineRamUnitStrideDecodable bindings initial)
    (hm : SupportedIntegerMachineState bindings.processor initial)
    (state : ReadEntry initial s input) (ready : ReadyToStep t) (loaded : ProgramLoaded t)
    (effect : (callEffect (fun _ => 0x119090) 0x102466 s).Holds s t) :
    ReadBe.Pre t (returnBoundary initial) := by
  obtain ⟨slices,call⟩ := hc
  have hs : Stack.Valid initial 5112 := call.stackAvailable.1
  have bounds := stack_bounds hs
  have rsp : stackPtr t = stackPtr initial-528 := by
    have h := effect.writes.1
    change stackPtr t = stackPtr s-8 at h
    rw [h,state.rsp,BitVec.sub_sub]
    rfl
  have src : t.regValue .rdi = stackPtr initial-184 :=
    (effect.agrees.read (n:=64) (r:=7) (by simp)).trans state.source
  have dst : t.regValue .rdx = stackPtr initial-520 :=
    (effect.agrees.read (n:=64) (r:=2) (by simp)).trans state.destination
  have spn : (stackPtr t).toNat = (stackPtr initial).toNat-528 := by
    rw [rsp]; exact stack_sub_toNat hs (by decide)
  have sn : (t.regValue .rdi).toNat = (stackPtr initial).toNat-184 := by
    rw [src]; exact stack_sub_toNat hs (by decide)
  have dn : (t.regValue .rdx).toNat = (stackPtr initial).toNat-520 := by
    rw [dst]; exact stack_sub_toNat hs (by decide)
  have lo : (Stack.region t 128).start = (stackPtr initial).toNat-656 := by
    change (stackPtr t).toNat-128 = _
    rw [spn]; omega
  have hi : (Stack.region t 128).start+(Stack.region t 128).size =
      (stackPtr initial).toNat-520 := by
    rw [stack_region_end]
    change (stackPtr t).toNat+8 = _
    rw [spn]; omega
  have sub (region : MemoryRegion) (a : (stackPtr initial).toNat-5112 ≤ region.start)
      (b : region.start+region.size ≤ (stackPtr initial).toNat+8) :
      ∀ x, region.Contains x → (Stack.region initial 5112).Contains x := by
    intro x hx
    change region.start ≤ x ∧ x < region.start+region.size at hx
    change (stackPtr initial).toNat-5112 ≤ x ∧
      x < (Stack.region initial 5112).start+(Stack.region initial 5112).size
    rw [stack_region_end]
    constructor <;> omega
  have srcSub := sub (registerRegion t .rdi 32)
    (by change _ ≤ (t.regValue .rdi).toNat; rw [sn]; omega)
    (by change (t.regValue .rdi).toNat+32 ≤ _; rw [sn]; omega)
  have dstSub := sub (registerRegion t .rdx 32)
    (by change _ ≤ (t.regValue .rdx).toNat; rw [dn]; omega)
    (by change (t.regValue .rdx).toNat+32 ≤ _; rw [dn]; omega)
  have stackSub := sub (Stack.region t 128) (by rw [lo]; omega) (by rw [hi]; omega)
  have allocated (region : MemoryRegion)
      (within : ∀ x,region.Contains x → (Stack.region initial 5112).Contains x) :
      region.Allocated t.external := by
    intro a ha
    exact Option.isSome_iff_exists.mp (effect.agrees.grow a (state.allocated a
      (Option.isSome_iff_exists.mpr (hs.2.1 a (within a.toNat ha)))))
  refine ⟨bindingsSupported_of_ready_agrees state.bindingsSupported ready effect.agrees,
    supportedMachine_of_ready_agrees state.machine ready effect.agrees,
    effect.agrees.directionFlagClear (by simp) state.directionFlag, loaded, effect.rip,
    (effect.agrees.read (n:=64) (r:=6) (by simp)).trans state.count,
    (effect.agrees.read (n:=64) (r:=1) (by simp)).trans state.limbs,
    (effect.agrees.read (n:=64) (r:=8) (by simp)).trans state.bits,
    ?_,allocated _ srcSub,?_,allocated _ dstSub,?_,?_,?_,outer_boundary call hm hb,?_⟩
  · change (t.regValue .rdi).toNat+32 < 2^32
    rw [sn]; omega
  · change (t.regValue .rdx).toNat+32 < 2^32
    rw [dn]; omega
  · refine ⟨?_,allocated _ stackSub,?_,?_⟩
    · change (Stack.region t 128).start+(Stack.region t 128).size < 2^32
      rw [hi]; omega
    · change 128 ≤ (stackPtr t).toNat
      rw [spn]; omega
    · change (stackPtr t).toNat%16=8
      rw [spn]
      have hm' : (stackPtr initial).toNat%16=8 := hs.2.2.2
      omega
  · intro i j hij a ha hb'
    have ii := i.isLt
    have jj := j.isLt
    have pairs : (i.val=0 ∧ j.val=1) ∨ (i.val=0 ∧ j.val=2) ∨ (i.val=1 ∧ j.val=2) := by
      change i.val < j.val at hij
      omega
    rcases pairs with ⟨ei,ej⟩ | ⟨ei,ej⟩ | ⟨ei,ej⟩
    all_goals have ie : i = ⟨_,ei ▸ i.isLt⟩ := Fin.ext ei
    all_goals have je : j = ⟨_,ej ▸ j.isLt⟩ := Fin.ext ej
    all_goals rw [ie] at ha
    all_goals rw [je] at hb'
    · change (t.regValue .rdi).toNat ≤ a ∧ a < (t.regValue .rdi).toNat+32 at ha
      change (t.regValue .rdx).toNat ≤ a ∧ a < (t.regValue .rdx).toNat+32 at hb'
      rw [sn] at ha
      rw [dn] at hb'
      omega
    · change (t.regValue .rdi).toNat ≤ a ∧ a < (t.regValue .rdi).toNat+32 at ha
      change (Stack.region t 128).start ≤ a ∧ a < (Stack.region t 128).start+(Stack.region t 128).size at hb'
      rw [sn] at ha
      rw [hi] at hb'
      omega
    · change (t.regValue .rdx).toNat ≤ a ∧ a < (t.regValue .rdx).toNat+32 at ha
      change (Stack.region t 128).start ≤ a ∧ a < (Stack.region t 128).start+(Stack.region t 128).size at hb'
      rw [dn] at ha
      rw [hi] at hb'
      omega
  · intro region hr a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · exact call_stack_avoids call a (dstSub a.toNat ha)
    · exact call_stack_avoids call a (stackSub a.toNat ha)
  · change InProgram (stackTop t)
    rw [(callEffect_stack effect).1]
    exact inProgram_of_textOffset 0x2466 (by decide)

end P256.Proofs.Signing.Wrapper.Entry.Decode
