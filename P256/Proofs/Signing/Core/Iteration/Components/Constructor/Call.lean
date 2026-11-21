import P256.Proofs.Signing.Core.Iteration.Components.Constructor.Frame
import P256.Proofs.Program.ScalarFrame.CallStep
import X86Proofs.Instructions.Call.Triple

set_option autoImplicit false

open P256.Proofs.Program

namespace P256.Proofs.Signing.Core.Iteration.Components.Constructor

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem constructor_call_address [Bindings] {s t : RamState} (state : Frame s t) :
    pushAddr t = stackPtr s - 224 := by
  rw [pushAddr, state.rsp, BitVec.sub_sub]
  rfl

theorem constructor_call_writes [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {target : RamState → BitVec 64} {ret : BitVec 64}
    (pre : CalleePre s boundary 0x109890 32 72 512) (state : Frame s t) :
    WritesWithin (callEffect target ret t).components #v[Stack.region s 512] := by
  intro c hc a hv
  simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact hv.elim
  · refine ⟨Stack.region s 512, by simp, ?_⟩
    rw [constructor_call_address state] at hv
    exact Program.ScalarFrame.stack_contains pre (offset := 224)
      (by decide) (by decide) hv
  · exact hv.elim

theorem constructor_call_loaded [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {target : RamState → BitVec 64} {ret : BitVec 64}
    (pre : CalleePre s boundary 0x109890 32 72 512) (state : Frame s t)
    (effect : (callEffect target ret t).Holds t u) : ProgramLoaded u := by
  intro a b hb
  rw [effect.agrees.memoryWriteFrame (constructor_call_writes pre state) a]
  · exact state.loaded a b hb
  · intro region hr hin
    have he : region = Stack.region s 512 := by simpa using hr
    subst region
    exact pre.avoids _ (by simp) a hin (.inl ⟨b, hb⟩)

end P256.Proofs.Signing.Core.Iteration.Components.Constructor
