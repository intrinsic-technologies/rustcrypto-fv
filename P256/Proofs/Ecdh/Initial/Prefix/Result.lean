import P256.Proofs.Ecdh.Initial.Prefix.Pre

set_option autoImplicit false

namespace P256.Proofs.Ecdh.Initial.Prefix

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame Field Standards.SECG.ECC

set_option maxHeartbeats 800000 in
theorem block_frame [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    (pre : Ecdh.Pre s boundary) (state : Ecdh.Frame s t) (ready : ReadyToStep u)
    (effect : (Block.effect t).Holds t u) : Ecdh.Frame s u := by
  have lift (offset : Nat) (bound : offset+56 ≤ 2056) (a : BitVec 64)
      (hc : (Component.mem (rspOf t+BitVec.ofNat 64 offset) 8).Covers a) :
      ∃ region ∈ #v[registerRegion s .rdi 32,workRegion s 3464], region.Contains a.toNat := by
    have address : rspOf t+BitVec.ofNat 64 offset = stackPtr s-BitVec.ofNat 64 (2056-offset) :=
      scalar_stack_address (frameOffset := 2056) state.rsp (by decide) (by omega)
    rw [address] at hc
    exact ⟨workRegion s 3464,by simp,work_contains pre.toCalleePre (by omega) (by omega) hc⟩
  apply state.after_effect (frameOffset := 2056) pre.toCalleePre (by decide) ready effect.agrees
  · intro c hc a ha
    simp only [Block.effect,Effect.components,List.map_cons,List.map_nil,Write.component,
      Operand.component,List.append_nil,List.cons_append,List.nil_append,Nat.reduceDiv,
      List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    · exact lift 8 (by decide) a ha
    · exact lift 248 (by decide) a ha
    · exact lift 256 (by decide) a ha
    · exact lift 264 (by decide) a ha
    · exact lift 272 (by decide) a ha
    · exact lift 280 (by decide) a ha
    · exact lift 288 (by decide) a ha
    · exact lift 296 (by decide) a ha
    · exact lift 304 (by decide) a ha
    · exact lift 312 (by decide) a ha
    · exact lift 320 (by decide) a ha
    · exact lift 328 (by decide) a ha
    · exact lift 336 (by decide) a ha
  all_goals simp [Block.effect,Effect.components]

theorem montgomery_of_limbs {s t : RamState} {source destination : BitVec 64} {x : Nat}
    (input : MontgomeryAt s source x) (readable : MemReadable t destination 32)
    (limbs : ∀ k < 4, memLoad t.external (destination+BitVec.ofNat 64 (8*k)) 64 =
      memLoad s.external (source+BitVec.ofNat 64 (8*k)) 64) : MontgomeryAt t destination x := by
  refine ⟨input.1,SecretKeyFromBytes.Scalar.nat256At_of_memLoad_limbs input.2.1 readable.mem ?_⟩
  intro k hk
  exact (limbs k hk).trans (input.2.memLoad_limb k hk)

set_option maxHeartbeats 800000 in
theorem block_result [Bindings] {s t u : RamState} {boundary : ReturnBoundary} {point : Curve.Point}
    (pre : Ecdh.Pre s boundary) (state : Ecdh.Frame s t) (ready : ReadyToStep u)
    (effect : (Block.effect t).Holds t u)
    (rsi : t.regValue .rsi = s.regValue .rsi)
    (rdi : t.regValue .rdi = s.regValue .rdi)
    (rdx : t.regValue .rdx = s.regValue .rdx)
    (peer : Sec1.AffineAt s (s.regValue .rdx) point) : Prepared s u point := by
  have frame := block_frame pre state ready effect
  have sp : rspOf t = frameBase s := state.rsp
  obtain ⟨ax,bx,r14,r12,r13,count,dst,src,scalar,w0,w1,w2,w3,w4,w5,w6,w7,w8,w9,w10,w11⟩ := effect.writes
  change memLoad u.external (rspOf t+248) 64 = memLoad t.external (t.regValue .rdx+0) 64 at w0
  change memLoad u.external (rspOf t+256) 64 = memLoad t.external (t.regValue .rdx+8) 64 at w1
  change memLoad u.external (rspOf t+264) 64 = memLoad t.external (t.regValue .rdx+16) 64 at w2
  change memLoad u.external (rspOf t+272) 64 = memLoad t.external (t.regValue .rdx+24) 64 at w3
  change memLoad u.external (rspOf t+280) 64 = memLoad t.external (t.regValue .rdx+32) 64 at w4
  change memLoad u.external (rspOf t+288) 64 = memLoad t.external (t.regValue .rdx+40) 64 at w5
  change memLoad u.external (rspOf t+296) 64 = memLoad t.external (t.regValue .rdx+48) 64 at w6
  change memLoad u.external (rspOf t+304) 64 = memLoad t.external (t.regValue .rdx+56) 64 at w7
  change memLoad u.external (rspOf t+312) 64 = memLoad t.external (0x202580) 64 at w8
  change memLoad u.external (rspOf t+320) 64 = memLoad t.external (0x202588) 64 at w9
  change memLoad u.external (rspOf t+328) 64 = memLoad t.external (0x202590) 64 at w10
  change memLoad u.external (rspOf t+336) 64 = memLoad t.external (0x202598) 64 at w11
  rw [sp] at w0 w1 w2 w3 w4 w5 w6 w7 w8 w9 w10 w11
  have readable (offset : Nat) (bound : offset+32 ≤ 2056) :
      MemReadable u (frameBase s+BitVec.ofNat 64 offset) 32 := by
    rw [frame_address s offset (by omega)]
    exact readable_of_grow (stack_sub_readable pre.stack (by omega) (by omega)) frame.allocated
  have peerX : MontgomeryAt t (t.regValue .rdx) (lifted point).x := by
    rw [rdx]
    have hx : MontgomeryAt s (s.regValue .rdx) (lifted point).x := by
      cases point <;> exact peer.1
    exact hx.of_bytes_eq (fun i hi => peer_byte pre state (by omega))
  have peerY : MontgomeryAt t (t.regValue .rdx+32) (lifted point).y := by
    rw [rdx]
    have hy : MontgomeryAt s (s.regValue .rdx+32) (lifted point).y := by
      cases point <;> exact peer.2.1
    apply hy.of_bytes_eq
    intro i hi
    have eq := peer_byte pre state (i := 32+i) (by omega)
    simp only [BitVec.ofNat_add,←BitVec.add_assoc] at eq
    exact eq
  have x : MontgomeryAt u (frameBase s+248) (lifted point).x := by
    apply montgomery_of_limbs peerX (readable 248 (by decide))
    intro k hk
    have cases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    · simpa [BitVec.add_assoc,BitVec.ofNat_eq_ofNat] using w0
    · simpa [BitVec.add_assoc,BitVec.ofNat_eq_ofNat] using w1
    · simpa [BitVec.add_assoc,BitVec.ofNat_eq_ofNat] using w2
    · simpa [BitVec.add_assoc,BitVec.ofNat_eq_ofNat] using w3
  have y : MontgomeryAt u (frameBase s+280) (lifted point).y := by
    apply montgomery_of_limbs peerY (readable 280 (by decide))
    intro k hk
    have cases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    · simpa [BitVec.add_assoc,BitVec.ofNat_eq_ofNat] using w4
    · simpa [BitVec.add_assoc,BitVec.ofNat_eq_ofNat] using w5
    · simpa [BitVec.add_assoc,BitVec.ofNat_eq_ofNat] using w6
    · simpa [BitVec.add_assoc,BitVec.ofNat_eq_ofNat] using w7
  have z : MontgomeryAt u (frameBase s+312) 1 := by
    apply montgomery_of_limbs (one_at state.loaded) (readable 312 (by decide))
    intro k hk
    have cases : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    · simpa [BitVec.add_assoc,BitVec.ofNat_eq_ofNat] using w8
    · simpa [BitVec.add_assoc,BitVec.ofNat_eq_ofNat] using w9
    · simpa [BitVec.add_assoc,BitVec.ofNat_eq_ofNat] using w10
    · simpa [BitVec.add_assoc,BitVec.ofNat_eq_ofNat] using w11
  have source : ProjectiveAt u (frameBase s+248) (lifted point) := by
    refine ⟨x,?_,?_⟩
    · simpa [BitVec.add_assoc,BitVec.ofNat_eq_ofNat] using y
    · have hz : (lifted point).z = 1 := by cases point <;> rfl
      rw [hz]
      simpa [BitVec.add_assoc,BitVec.ofNat_eq_ofNat] using z
  refine ⟨frame,effect.rip,bx.trans rdi,?_,source,?_,?_,?_,?_,src,count,?_⟩
  · have h := scalar
    change memLoad u.external (rspOf t+8) 64 = t.regValue .rsi at h
    rw [sp] at h
    exact h.trans rsi
  · exact r14.trans (congrArg (fun a : BitVec 64 => a+280) sp)
  · exact r12.trans (congrArg (fun a : BitVec 64 => a+312) sp)
  · exact r13.trans (congrArg (fun a : BitVec 64 => a+1016) sp)
  · exact dst.trans (congrArg (fun a : BitVec 64 => a+1016) sp)
  · exact (effect.agrees.read (n := 64) (r := 2) (by simp [Block.effect,Effect.components])).trans rdx

end P256.Proofs.Ecdh.Initial.Prefix
