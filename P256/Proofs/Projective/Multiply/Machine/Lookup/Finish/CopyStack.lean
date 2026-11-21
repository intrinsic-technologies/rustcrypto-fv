import P256.Proofs.Common.Memory.Readable
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Projective.Multiply.Machine.Lookup.Finish.Copy32

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)

namespace P256.Proofs.Projective.Multiply.Machine.Lookup.Finishing

open Program Field ProjectiveLookup P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem stack_pre [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {entry : BitVec 64} {source destination : RamState → BitVec 64} {offset : Nat}
    (pre : CalleePre s boundary 0x1044a0 768 96 496) (state : FrameState s t)
    (bound : offset + 32 ≤ 360) (dst : destination t = stackPtr t + BitVec.ofNat 64 offset)
    (rip : t.RIP = entry) (readable : MemReadable t (source t) 32)
    (apart : RangeApart (destination t) 32 (source t) 32) : CopyPre entry source destination t := by
  refine ⟨rip, ?_, ?_, apart, ?_⟩
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    all_goals exact P256.Proofs.Common.Memory.memReadable_sub readable _ 8 (by decide)
  · intro i hi
    rw [dst]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    all_goals
      first
      | simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using
          stack_writable pre state (offset := offset + 0) (len := 8) (by omega) (by decide)
      | simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using
          stack_writable pre state (offset := offset + 8) (len := 8) (by omega) (by decide)
      | simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using
          stack_writable pre state (offset := offset + 16) (len := 8) (by omega) (by decide)
      | simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using
          stack_writable pre state (offset := offset + 24) (len := 8) (by omega) (by decide)
  · intro i hi off len hc
    rw [dst]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    all_goals
      first
      | simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using
          stack_code pre state (offset := offset + 0) (len := 8) (by omega) hc
      | simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using
          stack_code pre state (offset := offset + 8) (len := 8) (by omega) hc
      | simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using
          stack_code pre state (offset := offset + 16) (len := 8) (by omega) hc
      | simpa only [BitVec.ofNat_add, BitVec.ofNat_eq_ofNat, BitVec.add_assoc] using
          stack_code pre state (offset := offset + 24) (len := 8) (by omega) hc

theorem execute_copy [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {entryOffset src dst finalA x : Nat} {endIP : BitVec 64} {copyB : Bool} {bytes : List UInt8}
    (pre : CalleePre s boundary 0x1044a0 768 96 496) (state : FrameState s t)
    (block : AdvanceTriple boundary
      (CopyPre (Extracted.textAddress + BitVec.ofNat 64 entryOffset)
        (fun t => stackPtr t + BitVec.ofNat 64 src) (fun t => stackPtr t + BitVec.ofNat 64 dst))
      (codeRange (Extracted.textAddress + BitVec.ofNat 64 entryOffset) bytes)
      (Effect.post (copyEffect endIP src dst finalA copyB)))
    (codeBound : entryOffset + bytes.length ≤ 118431)
    (code : Extracted.textBytes.toListFrom entryOffset bytes.length = bytes)
    (srcBound : src+32≤360) (dstBound : dst+32≤312)
    (apart : OffsetsApart (BitVec.ofNat 64 dst) 32 (BitVec.ofNat 64 src) 32)
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 entryOffset)
    (input : MontgomeryAt t (stackPtr s - BitVec.ofNat 64 (360-src)) x) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u ∧ u.RIP = endIP ∧
      MontgomeryAt u (stackPtr s - BitVec.ofNat 64 (360-dst)) x ∧
      AgreesExcept [.reg 0,.reg 1,.mem (stackPtr s - BitVec.ofNat 64 (360-dst)) 32,.rip] t u := by
  have start : CopyPre (Extracted.textAddress + BitVec.ofNat 64 entryOffset)
      (fun t => stackPtr t + BitVec.ofNat 64 src) (fun t => stackPtr t + BitVec.ofNat 64 dst) t := by
    apply stack_pre pre state (by omega) rfl rip (stack_readable pre state srcBound)
    intro i hi j hj he
    exact OffsetsApart.ne apart (stackPtr t) hi hj (by decide) he
  obtain ⟨n,u,run,ready,_,effect⟩ := block t (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) entryOffset bytes codeBound code) start
  have agr := copy_frame effect
  have addr := stack_address state.rsp (offset := dst) (by omega)
  rw [addr] at agr
  have writes : WritesWithin [.reg 0,.reg 1,.mem (stackPtr s - BitVec.ofNat 64 (360-dst)) 32,.rip]
      #v[registerRegion s .rdi 96, workRegion s] := by
    intro c hc a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    exact ⟨workRegion s,by simp,work_contains pre (by omega) (by omega) ha⟩
  have next := after pre state ready agr writes (by simp)
  refine ⟨n,u,run,next,effect.rip,?_,agr⟩
  rw [← addr]
  apply copy_payload effect
  · rw [stack_address state.rsp (by omega)]
    exact input
  · have h := stack_readable pre next (offset := dst) (len := 32) (by omega)
    have sp : stackPtr u = stackPtr t := agr.read (n := 64) (r := 4) (by simp)
    rw [sp] at h
    exact h

end P256.Proofs.Projective.Multiply.Machine.Lookup.Finishing
