import ChaCha20Poly1305.Proofs.Encrypt.Append.Body

namespace ChaCha20Poly1305.Proofs.Encrypt

open ChaCha20Poly1305.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Wrapper

structure AppendAtCopy [Bindings] (s t : RamState) (buffer : BitVec 64) (length : Nat) : Prop where
  ready : ReadyToStep t
  code : CodeIn Extracted.programImage t
  rip : t.RIP = 0x101fdc
  rsp : stackPtr t = stackPtr s - BitVec.ofNat 64 40
  rdi : rd t 7 = buffer + BitVec.ofNat 64 length
  rsi : rd t 6 = s.regValue .rsi
  rdx : rd t 2 = 16
  rbx : rd t 3 = 16
  r14 : rd t 14 = s.regValue .rdi
  r15 : rd t 15 = BitVec.ofNat 64 length
  agrees : AgreesExcept (appendPushChanges s ++ appendBodyChanges) s t
  frame : MemoryWriteFrame s t #v[Stack.region s 48]
  saved15 : wd t (stackPtr s - BitVec.ofNat 64 8) = rd s 15
  saved14 : wd t (stackPtr s - BitVec.ofNat 64 16) = rd s 14
  saved12 : wd t (stackPtr s - BitVec.ofNat 64 24) = rd s 12
  saved3 : wd t (stackPtr s - BitVec.ofNat 64 32) = rd s 3

theorem append_to_copy [Bindings] {s : RamState} {buffer : BitVec 64}
    {length : Nat} {tag : Vector UInt8 16} {boundary : ReturnBoundary}
    (pre : AppendPre s buffer length tag) (outside : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 17 s t ∧ AppendAtCopy s t buffer length := by
  obtain ⟨u, au, ru, cu, ipu, spu, hu, s15, s14, s12, s3⟩ := append_prologue pre outside
  have fu := append_push_frame pre.stack hu
  have du : rd u 7 = s.regValue .rdi := hu.read (by simp [appendPushChanges])
  have nu : rd u 2 = 16 := (hu.read (by simp [appendPushChanges])).trans pre.count
  obtain ⟨v, av, Tv, ipv, bv, dv, cv, lv, nv⟩ := append_loads pre outside fu ru cu ipu du nu
  obtain ⟨w, aw, Tw, ipw, hw⟩ := append_capacity outside Tv ipv cv lv nv bv
  have bw : rd w 3 = 16 := (hw.read (by simp)).trans bv
  have dw : rd w 14 = s.regValue .rdi := (hw.read (by simp)).trans dv
  have lw : rd w 15 = BitVec.ofNat 64 length := (hw.read (by simp)).trans lv
  have fw : MemoryWriteFrame s w #v[Stack.region s 48] := by
    intro a ha
    exact (Tw.agrees.memory a (by simp [appendBodyChanges, Component.Covers])).trans (fu a ha)
  obtain ⟨t, advt, Tt, ipt, dt, nt, ht⟩ := append_copy_setup pre outside fw Tw ipw dw lw bw
  refine ⟨t, au.trans (av.trans (aw.trans advt)), ?_⟩
  refine ⟨Tt.ready, Tt.code, ipt, ?_, dt, ?_, nt, ?_, ?_, ?_, hu.trans Tt.agrees, ?_,
    ?_, ?_, ?_, ?_⟩
  · exact sp_keep Tt.agrees (by simp [appendBodyChanges]) spu
  · exact (Tt.agrees.read (by simp [appendBodyChanges])).trans
      (hu.read (by simp [appendPushChanges]))
  · exact (ht.read (by simp)).trans bw
  · exact (ht.read (by simp)).trans dw
  · exact (ht.read (by simp)).trans lw
  · intro a ha
    exact (Tt.agrees.memory a (by simp [appendBodyChanges, Component.Covers])).trans (fu a ha)
  · exact (gload Tt.agrees (by simp [appendBodyChanges, Component.Covers])).trans s15
  · exact (gload Tt.agrees (by simp [appendBodyChanges, Component.Covers])).trans s14
  · exact (gload Tt.agrees (by simp [appendBodyChanges, Component.Covers])).trans s12
  · exact (gload Tt.agrees (by simp [appendBodyChanges, Component.Covers])).trans s3

end ChaCha20Poly1305.Proofs.Encrypt
