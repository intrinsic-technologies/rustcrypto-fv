import P256.Proofs.Verifying.Core.Finish.Tail.EncodeBlock
import P256.Proofs.Verifying.Core.Memory
import P256.Proofs.SecretKeyFromBytes.Encoding
import P256.Proofs.Projective.Multiply.Machine.Radix.Serialize.Encoding

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Finish.Tail

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame
open SecretKeyFromBytes.Scalar SecretKeyFromBytes.Encoding
open Projective.Multiply.Machine.Radix.Serialize
open Common.Instructions (bswap64)

theorem encode [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x r : Nat}
    (hp : Core.Pre s boundary) (state : Frame s t) (rip : t.RIP = 0x10e04c)
    (input : Nat256At t (frameBase s+128) x)
    (saved : Nat256At t (frameBase s+704) r) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x10e098 ∧
      memLoad u.external (frameBase s+384) 64 = memLoad t.external (frameBase s+384) 64 ∧
      (⟨(frameBase s+392).toNat,32⟩ : MemoryRegion).HasBytes u.external
        (Standards.SECG.ECC.Encoding.natToOctets 32 x) ∧
      Nat256At u (frameBase s+704) r := by
  have pre : Encode.Pre t := by
    refine ⟨rip,?_,?_,?_⟩
    · intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl
      all_goals exact stack_readable (frameOffset := 1176) hp.toCalleePre state (by decide) (by decide)
    · intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl
      all_goals exact local_writable8 hp state (by decide) (by decide)
    · intro i hi off len hl
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl|rfl|rfl|rfl
      all_goals exact stack_code (frameOffset := 1176) hp.toCalleePre state (by decide) (by decide) hl
  obtain ⟨n,u,run,ready,_,effect⟩ := Encode.block boundary hp.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0xe04c Encode.bytes
      (by decide) (by decide +kernel)) pre
  have writes : WritesWithin (Encode.effect t).components
      #v[registerRegion s .rdi 24,workRegion s 9992] := by
    intro c hc a ha
    simp only [Encode.effect,Effect.components,List.map_cons,List.map_nil,
      Write.component_reg,Write.component_mem,List.cons_append,List.nil_append,
      List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals try exact ha.elim
    all_goals exact ⟨_,by simp,local_work_contains hp state (by decide) ha⟩
  have next := state.after_effect hp.toCalleePre (by decide) ready effect.agrees writes
    (by simp [Encode.effect,Effect.components])
  have sp : rspOf t = frameBase s := state.rsp
  have words (j : Nat) (hj : j < 4) :
      memLoad t.external (rspOf t+128+BitVec.ofNat 64 (8*j)) 64 = canonicalLimb x j := by
    rw [sp]
    exact input.memLoad_limb j hj
  have bytes := canonical_bigEndian_bytes (value := x) (a := frameBase s+392)
    (by
      have h := (stack_readable (frameOffset := 1176) hp.toCalleePre next
        (offset := 392) (len := 32) (by decide) (by decide)).mem
      rwa [next.rsp] at h) (by
      intro j hj
      rcases (show j=0 ∨ j=1 ∨ j=2 ∨ j=3 by omega) with rfl|rfl|rfl|rfl
      all_goals simp only [Nat.reduceSub,Nat.reduceMul,BitVec.ofNat_eq_ofNat,
        BitVec.add_assoc,BitVec.reduceAdd,BitVec.add_zero]
      · exact (sp ▸ effect.writes.2.2.2.2.1).trans (congrArg bswap64 (by
          simpa only [sp,Nat.reduceMul,BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd]
            using words 3 (by decide)))
      · exact (sp ▸ effect.writes.2.2.2.2.2.1).trans (congrArg bswap64 (by
          simpa only [sp,Nat.reduceMul,BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd]
            using words 2 (by decide)))
      · exact (sp ▸ effect.writes.2.2.2.2.2.2.1).trans (congrArg bswap64 (by
          simpa only [sp,Nat.reduceMul,BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd]
            using words 1 (by decide)))
      · exact (sp ▸ effect.writes.2.2.2.2.2.2.2).trans (congrArg bswap64 (by
          simpa only [sp,Nat.reduceMul,BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd,BitVec.add_zero]
            using words 0 (by decide))))
  refine ⟨n,u,run,next,effect.rip,?_,?_,?_⟩
  · apply memLoad_congr (n := 64)
    intro i hi
    change (u.external[_]?).getD 0 = (t.external[_]?).getD 0
    congr 1
    apply effect.agrees.byte
    intro c hc ha
    simp only [Encode.effect,Effect.components,List.map_cons,List.map_nil,
      Write.component_reg,Write.component_mem,List.cons_append,List.nil_append,
      List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals try exact ha.elim
    all_goals obtain ⟨j,hj,eq⟩ := ha
    all_goals rw [sp] at eq
    all_goals bv_omega
  · refine ⟨natToOctets_size 32 x,?_⟩
    intro i
    have hi : i.val < 32 := by simpa only [natToOctets_size] using i.isLt
    change u.external[BitVec.ofNat 64 ((frameBase s+392).toNat+i.val)]? = _
    rw [BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq,
      ByteArray.getElem_eq_getElem_data,natToOctets_getElem 32 x i.val hi]
    simpa only [show 32-1-i.val=31-i.val by omega] using bytes i.val hi
  · refine ⟨saved.1,fun i hi => ?_⟩
    rw [effect.agrees.byte]
    · exact saved.2 i hi
    · intro c hc ha
      simp only [Encode.effect,Effect.components,List.map_cons,List.map_nil,
        Write.component_reg,Write.component_mem,List.cons_append,List.nil_append,
        List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
      all_goals try exact ha.elim
      all_goals obtain ⟨j,hj,eq⟩ := ha
      all_goals rw [sp] at eq
      all_goals bv_omega

end P256.Proofs.Verifying.Core.Finish.Tail
