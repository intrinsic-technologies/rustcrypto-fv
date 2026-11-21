import P256.Proofs.Signing.Core.Iteration.Point.Normalize.SelectSetup
import P256.Proofs.Signing.Core.Iteration.Point.State
import P256.Proofs.SecretKeyFromBytes.Encoding
import P256.Proofs.Common.Field.SquareRoot.Exponent.ReadDigit.State

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Point.Normalize.SelectSetup

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program
open SecretKeyFromBytes.Encoding

theorem writes [Bindings] {s t : RamState} (frame : Frame s t) :
    WordWrites (frameBase s) [392,384,376,368] (effect t).components := by
  intro c hc address ha
  simp only [effect,Effect.components,List.map_cons,List.map_nil,
    Write.component_reg,Write.component_mem,List.cons_append,List.nil_append,
    List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals try exact ha.elim
  all_goals obtain ⟨i,hi,rfl⟩ := ha
  · exact ⟨392,by simp,i,hi,congrArg (fun b => b+392+BitVec.ofNat 64 i) frame.rsp⟩
  · exact ⟨384,by simp,i,hi,congrArg (fun b => b+384+BitVec.ofNat 64 i) frame.rsp⟩
  · exact ⟨376,by simp,i,hi,congrArg (fun b => b+376+BitVec.ofNat 64 i) frame.rsp⟩
  · exact ⟨368,by simp,i,hi,congrArg (fun b => b+368+BitVec.ofNat 64 i) frame.rsp⟩

theorem prepared [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : SignPre s boundary) (frame : Frame s t) (rip : t.RIP = 0x10cf82) : Pre t := by
  refine ⟨rip,?_,?_,?_⟩
  · rw [frame.rsp]
    exact local_readable pre frame (by decide)
  · intro k hk
    rw [frame.rsp]
    exact local_writable8 pre frame (by omega) (by omega)
  · intro k hk offset len bound
    rw [frame.rsp]
    exact local_code_apart pre frame (by omega) bound

theorem after [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    (pre : SignPre s boundary) (frame : Frame s t) (ready : ReadyToStep u)
    (ef : (effect t).Holds t u) : Frame s u :=
  after_effect pre frame ready ef.agrees (writes frame)
    (by intro off ho; simp only [List.mem_cons,List.not_mem_nil,or_false] at ho; omega)
    (by simp [effect,Effect.components]) (by simp [effect,Effect.components])
    (by simp [effect,Effect.components]) (by simp [effect,Effect.components])

theorem byte [Bindings] {s t u : RamState} {offset : Nat}
    (frame : Frame s t) (ef : (effect t).Holds t u) (bound : offset < 2^64)
    (apart : offset < 368 ∨ 400 ≤ offset) :
    u.external[frameBase s+BitVec.ofNat 64 offset]? =
      t.external[frameBase s+BitVec.ofNat 64 offset]? := by
  apply word_writes_byte (writes frame) ef.agrees bound
  intro off ho
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
  omega

theorem zero [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    (pre : SignPre s boundary) (frame : Frame s t) (next : Frame s u)
    (ef : (effect t).Holds t u) : Field.MontgomeryAt u (frameBase s+368) 0 := by
  refine ⟨by decide,?_⟩
  simp only [Nat.zero_mul,Nat.zero_mod]
  apply SecretKeyFromBytes.Scalar.nat256At_of_memLoad_limbs (by decide)
  · exact (local_readable pre next (offset := 368) (len := 32) (by decide)).mem
  · intro j hj
    have values := ef.writes
    simp only [effect,Write.AllHold,frame.rsp] at values
    rcases (show j=0 ∨ j=1 ∨ j=2 ∨ j=3 by omega) with rfl|rfl|rfl|rfl
    all_goals simp only [Nat.reduceMul,BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd,BitVec.add_zero]
    · exact values.2.2.2.1
    · exact values.2.2.1
    · exact values.2.1
    · exact values.1

theorem choice {t u : RamState} {flag : UInt8}
    (ef : (effect t).Holds t u) (value : t.external[stackPtr t+464]? = some flag) :
    (u.regValue .r12).setWidth 8 = flag.toBitVec ∧
      (u.regValue .rcx).setWidth 8 = flag.toBitVec := by
  have values := ef.writes
  simp only [effect,Write.AllHold] at values
  have hv : ((memLoad t.external (stackPtr t+464) 32).setWidth 64).setWidth 8 = flag.toBitVec := by
    rw [BitVec.setWidth_setWidth_of_le _ (by decide),
      Common.Field.SquareRoot.memLoad_setWidth_of_le _ _ (by decide) (by decide)]
    have hb := storedByte_memLoad t.external (stackPtr t+464) 0 (by decide : 0 < 8/8)
    have hb' : memLoad t.external (stackPtr t+464) 8 =
        (t.external[stackPtr t+464]?.getD 0).toBitVec := by
      simpa [storedByte,memByte,PhysicalMemory.read] using congrArg UInt8.toBitVec hb
    rw [value] at hb'
    exact hb'
  exact ⟨(congrArg (BitVec.setWidth 8) values.2.2.2.2.1).trans hv,
    (congrArg (BitVec.setWidth 8) values.2.2.2.2.2.2.2.2.2).trans hv⟩

end P256.Proofs.Signing.Core.Iteration.Point.Normalize.SelectSetup
