import P256.Proofs.Generate.Wrapper.Tail.Call
import P256.Proofs.Sec1Serialize

set_option autoImplicit false

namespace P256.Proofs.Generate.Wrapper

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program

def serializeLayout : StackCallLayout 4024 72 65 328 :=
  ⟨272, 152, 256, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide⟩

theorem serialize_call [bindings : Bindings]
    {initial s : RamState} {input : ByteArray} {slices : Array Input}
    {written : Option MemoryRegion}
    {point : Standards.SECG.ECC.Curve.Point}
    (call : ValidCallWithSlices signingKeyGenerateFromRng initial [input] slices)
    (state : State initial s 264 written) (outside : ¬ InProgram (returnBoundary initial).rip)
    (rip : s.RIP = 0x106df4) (src : s.regValue .rsi = stackPtr initial - 152)
    (dst : s.regValue .rdi = stackPtr initial - 256) (rdx : s.regValue .rdx = 0)
    (affine : Sec1.AffineAt s (stackPtr initial - 152) point) :
    ∃ t, State initial t 264 written ∧ t.RIP = 0x106df9 ∧
      (MemoryRegion.mk (stackPtr initial - 256).toNat 65).HasBytes t.external
        (Sec1Serialize.encodedPoint point) ∧ MemoryWriteFrame s t #v[workRegion initial] := by
  obtain ⟨v, stateV, effect, _⟩ := state.call_rel32 call outside 0x6df4 0x9f77 rip
    (by decide) (by decide) (by decide) (by decide) (by decide +kernel)
    (inProgram_of_textOffset 0x10d70 (by decide))
  have push : pushAddr s = stackPtr initial - 272 := by
    rw [pushAddr, state.rsp, BitVec.sub_sub]
    rfl
  have ag : AgreesExcept [.reg 4, .mem (stackPtr initial - 272) 8, .rip] s v := by
    simpa only [pushEffect_components, push] using effect.agrees
  have srcV : v.regValue .rsi = stackPtr initial - 152 :=
    (ag.read (n := 64) (r := 6) (by simp)).trans src
  have dstV : v.regValue .rdi = stackPtr initial - 256 :=
    (ag.read (n := 64) (r := 7) (by simp)).trans dst
  have rdxV : v.regValue .rdx = 0 := (ag.read (n := 64) (r := 2) (by simp)).trans rdx
  have ret : (returnBoundary v).rip = 0x106df9 := (callEffect_stack effect).1
  have pre := CalleePre.of_stack_region call.stackAvailable.1 (call_stack_avoids call)
    outside serializeLayout stateV.bindingsSupported stateV.machine stateV.directionFlag
    stateV.loaded stateV.allocated effect.rip stateV.rsp srcV dstV
    (by rw [ret]; exact inProgram_of_textOffset 0x6df9 (by decide))
  have affineV : Sec1.AffineAt v (v.regValue .rsi) point := by
    rw [srcV]
    exact affine.of_bytes_eq (push_bytes call.stackAvailable.1 ag (by decide) (by decide))
  obtain ⟨t, result, _, encoded⟩ := Sec1Serialize.serializer_correct bindings v (returnBoundary initial) point pre affineV rdxV
  refine ⟨t, stateV.after_callee call result dstV (by decide) (by decide) (by decide)
    (by decide), result.rip.trans ret, ?_⟩
  refine ⟨by simpa only [registerRegion, dstV] using encoded, ?_⟩
  have mem : MemoryWriteFrame v t #v[workRegion initial] :=
    result.stack_frame call.stackAvailable.1 stateV.rsp dstV (by decide) (by decide) (by decide) (by decide)
  apply memoryWriteFrame_trans (ag.memoryWriteFrame ?_) mem
  intro c hc a ha
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl | rfl | rfl <;> try exact ha.elim
  exact ⟨workRegion initial,by simp,work_contains call.stackAvailable.1 (by decide) (by decide) ha⟩

end P256.Proofs.Generate.Wrapper
