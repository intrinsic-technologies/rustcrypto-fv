import P256.Proofs.Signing.Core.Iteration.Point.State
import P256.Proofs.Program.ScalarFrame.Copy32Bytes
import P256.Proofs.Common.Field.Operations.Run.Compose
import P256.Proofs.Common.Memory.Readable

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Point.Normalize.Copy

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program
open P256.Proofs.Common.Field (AdvanceTriple)
open NextNonce (scalarFrame coreFrame base_add)

theorem prepared [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {sourceOffset destinationOffset : Nat} {ip : BitVec 64}
    {source destination : RamState → BitVec 64}
    (pre : SignPre s boundary) (frame : Frame s t) (rip : t.RIP = ip)
    (sourceBound : sourceOffset+32 ≤ 2280) (destinationBound : destinationOffset+32 ≤ 2232)
    (apart : sourceOffset+32 ≤ destinationOffset ∨ destinationOffset+32 ≤ sourceOffset)
    (src : source t = frameBase s+BitVec.ofNat 64 sourceOffset)
    (dst : destination t = frameBase s+BitVec.ofNat 64 destinationOffset) :
    ScalarFrame.Copy32.Pre ip source destination t := by
  have read := local_readable pre frame sourceBound
  rw [← src] at read
  refine ⟨rip,?_,?_,?_,?_⟩
  · intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl
    all_goals exact Common.Memory.memReadable_sub read _ 8 (by decide)
  · intro i hi
    rw [dst,← frame.rsp]
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl
    all_goals first
    | simpa only [BitVec.ofNat_add,BitVec.ofNat_eq_ofNat,BitVec.add_assoc] using
        ScalarFrame.stack_writable (frameOffset := 2280) pre.toCalleePre (scalarFrame frame) (by decide)
          (offset := destinationOffset+0) (len := 8) (by omega) (by decide)
    | simpa only [BitVec.ofNat_add,BitVec.ofNat_eq_ofNat,BitVec.add_assoc] using
        ScalarFrame.stack_writable (frameOffset := 2280) pre.toCalleePre (scalarFrame frame) (by decide)
          (offset := destinationOffset+8) (len := 8) (by omega) (by decide)
    | simpa only [BitVec.ofNat_add,BitVec.ofNat_eq_ofNat,BitVec.add_assoc] using
        ScalarFrame.stack_writable (frameOffset := 2280) pre.toCalleePre (scalarFrame frame) (by decide)
          (offset := destinationOffset+16) (len := 8) (by omega) (by decide)
    | simpa only [BitVec.ofNat_add,BitVec.ofNat_eq_ofNat,BitVec.add_assoc] using
        ScalarFrame.stack_writable (frameOffset := 2280) pre.toCalleePre (scalarFrame frame) (by decide)
          (offset := destinationOffset+24) (len := 8) (by omega) (by decide)
  · rw [src,dst]
    intro i hi j hj eq
    rw [BitVec.add_assoc,← BitVec.ofNat_add,BitVec.add_assoc,← BitVec.ofNat_add] at eq
    have h := congrArg BitVec.toNat ((BitVec.add_right_inj (frameBase s)).mp eq)
    simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : destinationOffset+i < 2^64),
      Nat.mod_eq_of_lt (by omega : sourceOffset+j < 2^64)] at h
    omega
  · intro i hi off len bound
    rw [dst]
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl
    all_goals first
    | simpa only [BitVec.ofNat_add,BitVec.ofNat_eq_ofNat,BitVec.add_assoc] using
        local_code_apart pre frame (offset := destinationOffset+0) (len := 8) (by omega) bound
    | simpa only [BitVec.ofNat_add,BitVec.ofNat_eq_ofNat,BitVec.add_assoc] using
        local_code_apart pre frame (offset := destinationOffset+8) (len := 8) (by omega) bound
    | simpa only [BitVec.ofNat_add,BitVec.ofNat_eq_ofNat,BitVec.add_assoc] using
        local_code_apart pre frame (offset := destinationOffset+16) (len := 8) (by omega) bound
    | simpa only [BitVec.ofNat_add,BitVec.ofNat_eq_ofNat,BitVec.add_assoc] using
        local_code_apart pre frame (offset := destinationOffset+24) (len := 8) (by omega) bound

theorem execute [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {codeOffset sourceOffset destinationOffset x : Nat} {endIP : BitVec 64}
    {source destination : RamState → BitVec 64} {bytes : List UInt8}
    (pre : SignPre s boundary) (frame : Frame s t)
    (block : AdvanceTriple boundary
      (ScalarFrame.Copy32.Pre (Extracted.textAddress+BitVec.ofNat 64 codeOffset) source destination)
      (codeRange (Extracted.textAddress+BitVec.ofNat 64 codeOffset) bytes)
      (Effect.post (ScalarFrame.Copy32.effect endIP source destination)))
    (codeBound : codeOffset+bytes.length ≤ 118431)
    (code : Extracted.textBytes.toListFrom codeOffset bytes.length = bytes)
    (rip : t.RIP = Extracted.textAddress+BitVec.ofNat 64 codeOffset)
    (sourceBound : sourceOffset+32 ≤ 2280) (destinationBound : destinationOffset+32 ≤ 2232)
    (apart : sourceOffset+32 ≤ destinationOffset ∨ destinationOffset+32 ≤ sourceOffset)
    (src : source t = frameBase s+BitVec.ofNat 64 sourceOffset)
    (dst : destination t = frameBase s+BitVec.ofNat 64 destinationOffset)
    (value : Field.MontgomeryAt t (source t) x) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = endIP ∧
      Field.MontgomeryAt u (destination t) x ∧
      AgreesExcept (ScalarFrame.Copy32.components (destination t)) t u := by
  have read := local_readable pre frame sourceBound
  rw [← src] at read
  have input := prepared pre frame rip sourceBound destinationBound apart src dst
  obtain ⟨fuel,u,run,ready,_,ef⟩ := block t
    (readyToStep frame.machine frame.bindingsSupported)
    (programText_slice (programLoaded_codeIn frame.loaded) codeOffset bytes codeBound code) input
  have ag := ScalarFrame.Copy32.frame ef
  have next : Frame s u := by
    apply after_agrees pre frame ready ag
    · intro c hc address ha
      simp only [ScalarFrame.Copy32.components,List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl|rfl|rfl|rfl
      all_goals try exact ha.elim
      rw [dst,base_add s (by omega)] at ha
      exact ⟨ScalarFrame.workRegion s 4584,by simp,
        ScalarFrame.work_contains pre.toCalleePre (by omega) (by omega) ha⟩
    · exact ag.read (n := 64) (r := 4) (by simp [ScalarFrame.Copy32.components])
    · simp [ScalarFrame.Copy32.components]
    · simp [ScalarFrame.Copy32.components]
    · simp [ScalarFrame.Copy32.components]
  refine ⟨fuel,u,run,next,ef.rip,value.of_bytes_eq (ScalarFrame.Copy32.copy_bytes ef read ?_),ag⟩
  rw [dst]
  exact local_readable pre next (by omega)

end P256.Proofs.Signing.Core.Iteration.Point.Normalize.Copy
