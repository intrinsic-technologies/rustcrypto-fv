import P256.Proofs.Verifying.Core.Combine.Interface
import P256.Proofs.Verifying.Core.Digest.Memory
import P256.Proofs.Projective.Preserve

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Combine

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame
open Digest (base_add_toNat)
open SecretKeyFromBytes.Scalar (Nat256At)

theorem byte_of_copy {s t u : RamState} {dst count offset len : Nat}
    (agrees : AgreesExcept [.reg 6,.reg 7,.reg 1,
      .mem (frameBase s+BitVec.ofNat 64 dst) (8*count),.rip] t u)
    (hd : dst+8*count ≤ 1128) (ho : offset+len ≤ 1176)
    (apart : dst+8*count ≤ offset ∨ offset+len ≤ dst)
    {i : Nat} (hi : i < len) :
    u.external[frameBase s+BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? =
      t.external[frameBase s+BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? := by
  apply agrees.byte
  intro c hc covered
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl <;> try exact covered.elim
  obtain ⟨j,hj,eq⟩ := covered
  exact RangeApart.offsets (frameBase s) (a := dst) (b := offset)
    (len := 8*count) (count := len) (by omega) (by omega) apart j hj i hi eq.symm

theorem input_readable [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Core.Pre s boundary) (state : Frame s t) :
    MemReadable t (frameBase s+1000) 96 := by
  have h := stack_readable pre.toCalleePre state (offset := 1000) (len := 96)
    (by decide) (by decide)
  simpa only [state.rsp,frameBase,BitVec.ofNat_eq_ofNat] using h

theorem point_disjoint [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : Core.Pre s boundary) :
    (frameBase s+1000).toNat+96 ≤ (frameBase s).toNat ∨
      (frameBase s).toNat+96 ≤ (frameBase s+1000).toNat := by
  have hn : (frameBase s).toNat = (stackPtr s).toNat-1176 :=
    stack_sub_toNat pre.stack (by decide)
  have ha : (frameBase s+1000).toNat = (stackPtr s).toNat-1176+1000 :=
    base_add_toNat pre (by decide)
  exact .inr (by omega)

theorem key_after_stack [Bindings] {s t u : RamState} {boundary : ReturnBoundary} {point : Projective}
    (pre : Core.Pre s boundary) (key : ProjectiveAt t (frameBase s+1000) point)
    (memory : MemoryWriteFrame t u (prefixRegions s)) :
    ProjectiveAt u (frameBase s+1000) point := by
  apply key.of_bytes_eq
  intro i hi
  exact prefix_byte pre memory (offset := 1000) (len := 96) (by decide) (by decide) hi

theorem nat256_of_bytes {t u : RamState} {src dst : BitVec 64} {x : Nat}
    (input : Nat256At t src x)
    (bytes : ∀ i < 32, u.external[dst+BitVec.ofNat 64 i]? =
      t.external[src+BitVec.ofNat 64 i]?) : Nat256At u dst x :=
  ⟨input.1,fun i hi => (bytes i hi).trans (input.2 i hi)⟩

theorem copy_memory [Bindings] {s t u : RamState} {boundary : ReturnBoundary} {dst count : Nat}
    (pre : Core.Pre s boundary) (state : Frame s t)
    (agrees : AgreesExcept [.reg 6,.reg 7,.reg 1,
      .mem (frameBase s+BitVec.ofNat 64 dst) (8*count),.rip] t u)
    (bound : dst+8*count ≤ 384 ∨ 576 ≤ dst ∧ dst+8*count ≤ 1000) :
    MemoryWriteFrame t u (prefixRegions s) := by
  apply agrees.memoryWriteFrame
  intro c hc a ha
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl <;> try exact ha.elim
  have sp : stackPtr t = frameBase s := state.rsp
  rw [← sp] at ha
  exact prefix_local_contains pre state bound ha

end P256.Proofs.Verifying.Core.Combine
