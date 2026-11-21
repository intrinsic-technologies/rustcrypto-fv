import P256.Proofs.EcdhWrapper.Peer.Pad.Memory
import P256.Proofs.Sec1.Representation

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Peer.Result

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def components (initial : RamState) : List Component :=
  [.reg 0,.reg 1,.reg 2,.reg 6,.reg 7,.flags,.rip,.mem (stackPtr initial-336) 1,.mem (stackPtr initial-336) 72]

variable [Bindings] {initial s t : RamState} {secret peer : ByteArray} {slices : Array Input}

omit [Bindings] in
theorem exact_frame (stack : Stack.Valid initial 4104) (g : AgreesExcept (components initial) s t) :
    MemoryWriteFrame s t #v[MemoryRegion.mk (stackPtr initial-336).toNat 72] := by
  apply g.memoryWriteFrame
  intro c hc a ha
  simp only [components,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> try exact ha.elim
  all_goals
  obtain ⟨i,hi,rfl⟩ := ha
  all_goals
  have bounds := stack_bounds stack
  all_goals
  have low : (stackPtr initial-336).toNat=(stackPtr initial).toNat-336 :=
    stack_sub_toNat stack (offset := 336) (by decide)
  all_goals
  refine ⟨MemoryRegion.mk (stackPtr initial-336).toNat 72,by simp,?_⟩
  all_goals
  change (stackPtr initial-336).toNat≤_ ∧ _<(stackPtr initial-336).toNat+72
  all_goals
  rw [toNat_add_ofNat _ _ (by rw [low]; omega)]
  all_goals constructor <;> omega

omit [Bindings] in
theorem work_frame (stack : Stack.Valid initial 4104) (g : AgreesExcept (components initial) s t) :
    MemoryWriteFrame s t #v[Pad.work initial] := by
  have frame := exact_frame stack g
  have bounds := stack_bounds stack
  have low : (stackPtr initial-336).toNat=(stackPtr initial).toNat-336 :=
    stack_sub_toNat stack (offset := 336) (by decide)
  intro a ha
  apply frame a
  intro r hr hin
  have eq : r=MemoryRegion.mk (stackPtr initial-336).toNat 72 := by simpa using hr
  subst r
  apply ha (Pad.work initial) (by simp)
  change (stackPtr initial-336).toNat≤a.toNat ∧ a.toNat<(stackPtr initial-336).toNat+72 at hin
  rw [low] at hin
  change (stackPtr initial).toNat-4104≤a.toNat ∧ a.toNat<(stackPtr initial).toNat-4104+(4104-264)
  constructor <;> omega

theorem loaded_after (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices)
    (g : AgreesExcept (components initial) s t) (loaded : ProgramLoaded s) : ProgramLoaded t :=
  Pad.loaded_after call (work_frame call.stackAvailable.1 g) loaded

omit [Bindings] in
theorem affine_preserved (stack : Stack.Valid initial 4104) (g : AgreesExcept (components initial) s t)
    {point : Standards.SECG.ECC.Curve.Point} (affine : Sec1.AffineAt s (stackPtr initial-128) point) :
    Sec1.AffineAt t (stackPtr initial-128) point := by
  apply affine.of_bytes_eq
  intro i hi
  apply g.byte
  intro c hc cover
  simp only [components,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> try exact cover.elim
  all_goals obtain ⟨j,hj,eq⟩ := cover
  all_goals
  exact stack_sub_apart stack (a := 336) (b := 128) (na := 72) (nb := 65)
    (by decide) (by decide) (by decide) (by decide) (.inl (by decide)) j (by omega) i hi eq.symm

end P256.Proofs.EcdhWrapper.Peer.Result
