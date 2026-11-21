import P256.Proofs.Signing.Core.Iteration.Point.Encode.Block
import P256.Proofs.Signing.Core.Iteration.Point.State
import P256.Proofs.SecretKeyFromBytes.Encoding
import P256.Proofs.Projective.Multiply.Machine.Radix.Serialize.Encoding

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Point.Encode

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program
open SecretKeyFromBytes.Encoding Projective.Multiply.Machine.Radix.Serialize
open Common.Instructions (bswap64)

theorem writes [Bindings] {s t : RamState} (frame : Frame s t) :
    WordWrites (frameBase s) [432,440,448,456] (Block.effect t).components := by
  intro c hc address ha
  simp only [Block.effect,Effect.components,List.map_cons,List.map_nil,
    Write.component_reg,Write.component_mem,List.cons_append,List.nil_append,
    List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals try exact ha.elim
  all_goals obtain ⟨i,hi,rfl⟩ := ha
  · exact ⟨432,by simp,i,hi,congrArg (fun b => b+432+BitVec.ofNat 64 i) frame.rsp⟩
  · exact ⟨440,by simp,i,hi,congrArg (fun b => b+440+BitVec.ofNat 64 i) frame.rsp⟩
  · exact ⟨448,by simp,i,hi,congrArg (fun b => b+448+BitVec.ofNat 64 i) frame.rsp⟩
  · exact ⟨456,by simp,i,hi,congrArg (fun b => b+456+BitVec.ofNat 64 i) frame.rsp⟩

theorem correct [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x y : Nat}
    (hp : SignPre s boundary) (input : Converted s t x y) (rip : t.RIP = 0x10d153) :
    ∃ fuel u, Advances boundary fuel t u ∧ u.RIP = 0x10d19f ∧
      Encoded s u x y ∧ Preserved s t u := by
  have pre : Block.Pre t := by
    refine ⟨rip,?_,?_,?_⟩
    · intro off ho
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
      rw [input.frame.rsp]
      exact local_readable hp input.frame (by omega)
    · intro off ho
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
      rw [input.frame.rsp]
      exact local_writable8 hp input.frame (by omega) (by omega)
    · intro off ho codeOffset len hl
      simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
      rw [input.frame.rsp]
      exact local_code_apart hp input.frame (by omega) hl
  obtain ⟨n,u,run,ready,_,effect⟩ := Block.correct boundary hp.outerBoundary t
    (readyToStep input.frame.machine input.frame.bindingsSupported)
    (programText_slice (programLoaded_codeIn input.frame.loaded) 0xd153 Block.bytes
      (by decide) (by decide +kernel)) pre
  have next := after_effect hp input.frame ready effect.agrees (writes input.frame)
    (by intro off ho; simp only [List.mem_cons,List.not_mem_nil,or_false] at ho; omega)
    (by simp [Block.effect,Effect.components]) (by simp [Block.effect,Effect.components])
    (by simp [Block.effect,Effect.components]) (by simp [Block.effect,Effect.components])
  have sp : stackPtr t = frameBase s := input.frame.rsp
  have keep (offset : Nat) (bound : offset < 2^64) (apart : offset < 432 ∨ 464 ≤ offset) :
      u.external[frameBase s+BitVec.ofNat 64 offset]? =
        t.external[frameBase s+BitVec.ofNat 64 offset]? := by
    apply word_writes_byte (writes input.frame) effect.agrees bound
    intro off ho
    simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
    omega
  have words (j : Nat) (hj : j < 4) :
      memLoad t.external (stackPtr t+528+BitVec.ofNat 64 (8*j)) 64 = canonicalLimb x j := by
    rw [sp]
    exact input.value.memLoad_limb j hj
  have bytes := canonical_bigEndian_bytes (value := x) (a := frameBase s+432)
    (by
      exact (local_readable hp next (offset := 432) (len := 32) (by decide)).mem) (by
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
  refine ⟨n,u,run,effect.rip,⟨next,?_,?_,?_,?_,?_⟩,?_⟩
  · apply input.point.of_bytes_eq
    intro i hi
    have h := keep (104+i) (by omega) (by omega)
    simpa only [BitVec.ofNat_add,BitVec.ofNat_eq_ofNat,BitVec.add_assoc] using h
  · refine ⟨natToOctets_size 32 x,?_⟩
    intro i
    have hi : i.val < 32 := by simpa only [natToOctets_size] using i.isLt
    change u.external[BitVec.ofNat 64 ((frameBase s+432).toNat+i.val)]? = _
    rw [BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq,
      ByteArray.getElem_eq_getElem_data,natToOctets_getElem 32 x i.val hi]
    simpa only [show 32-1-i.val=31-i.val by omega] using bytes i.val hi
  · exact (effect.agrees.read (n := 64) (r := 5) (by simp [Block.effect,Effect.components])).trans input.rbp
  · exact (effect.agrees.read (n := 64) (r := 13) (by simp [Block.effect,Effect.components])).trans input.r13
  · exact (effect.agrees.read (n := 64) (r := 15) (by simp [Block.effect,Effect.components])).trans input.r15
  · intro off live
    exact keep off (by rcases live with h|h|h|h <;> omega)
      (by rcases live with h|h|h|h <;> omega)

end P256.Proofs.Signing.Core.Iteration.Point.Encode
