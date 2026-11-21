import P256.Proofs.Ecdh.Normalize.Finish.Output.Blocks
import P256.Proofs.Program.ScalarFrame.Memory
import P256.Proofs.Program.ScalarFrame.Output
import P256.Proofs.SecretKeyFromBytes.Scalar.Representation
import P256.Proofs.SecretKeyFromBytes.Encoding
import P256.Proofs.Projective.Multiply.Machine.Radix.Serialize.Encoding

set_option autoImplicit false

namespace P256.Proofs.Ecdh.Normalize.Finish.Output

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At)
open P256.Proofs.SecretKeyFromBytes.Encoding (natToOctets_size natToOctets_getElem)
open P256.Proofs.Projective.Multiply.Machine.Radix.Serialize
open P256.Proofs.Common.Instructions (bswap64)

theorem serialize [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x : Nat}
    (pre : CalleePre s boundary 0x100000 32 32 3464)
    (state : FrameState s t 32 3464 2056) (rip : t.RIP = 0x10052f)
    (output : t.regValue .rbx = s.regValue .rdi)
    (value : Nat256At t (stackPtr s - 1040) x) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u 32 3464 2056 ∧
      u.RIP = 0x10056a ∧ (registerRegion s .rdi 32).HasBytes u.external
        (Standards.SECG.ECC.Encoding.natToOctets 32 x) := by
  have writable := output_writable pre (by decide) state.allocated
  have input : OutputPre t := by
    refine ⟨rip,?_,output.symm ▸ writable,?_⟩
    · intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl
      all_goals exact stack_readable (frameOffset := 2056) pre state (by decide) (by decide)
    · rw [output]
      exact output_code pre (offset := 0x52f) (by decide)
  obtain ⟨fuel,u,run,ready,_,effect⟩ := output_block boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x52f outputBytes
      (by decide) (by decide +kernel)) input
  have writes : WritesWithin (outputEffect t).components
      #v[registerRegion s .rdi 32,workRegion s 3464] := by
    intro c hc a ha
    simp only [outputEffect,Effect.components,List.map_cons,List.map_nil,
      Write.component,Operand.component,Nat.reduceDiv,List.append_nil,
      List.cons_append,List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    all_goals
      refine ⟨registerRegion s .rdi 32,by simp,?_⟩
      rw [output] at ha
      exact output_contains pre (by decide) ha
  have next := state.after_effect pre (by decide) ready effect.agrees writes
    (by simp [outputEffect,Effect.components])
  have words (j : Nat) (hj : j < 4) :
      memLoad t.external (stackPtr t + 1016 + BitVec.ofNat 64 (8*j)) 64 =
        canonicalLimb x j := by
    have addr : stackPtr t + 1016 = stackPtr s - 1040 :=
      scalar_stack_address state.rsp (by decide) (by decide)
    rw [addr]
    exact value.memLoad_limb j hj
  have bytes := canonical_bigEndian_bytes (value := x)
    (fun i hi => effect.agrees.grow _ (writable.mem i hi)) (by
      intro j hj
      rcases (show j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 by omega) with rfl | rfl | rfl | rfl
      · change (Operand.mem (s.regValue .rdi + 0) : Operand 64).read u = bswap64 (canonicalLimb x 3)
        rw [← output]
        exact effect.writes.2.2.2.2.1.trans (congrArg bswap64 (by
          change memLoad t.external (stackPtr t + 1040) 64 = canonicalLimb x 3
          simpa only [Nat.reduceMul,BitVec.add_assoc,BitVec.ofNat_eq_ofNat,BitVec.reduceAdd] using words 3 (by decide)))
      · change (Operand.mem (s.regValue .rdi + 8) : Operand 64).read u = bswap64 (canonicalLimb x 2)
        rw [← output]
        exact effect.writes.2.2.2.2.2.1.trans (congrArg bswap64 (by
          change memLoad t.external (stackPtr t + 1032) 64 = canonicalLimb x 2
          simpa only [Nat.reduceMul,BitVec.add_assoc,BitVec.ofNat_eq_ofNat,BitVec.reduceAdd] using words 2 (by decide)))
      · change (Operand.mem (s.regValue .rdi + 16) : Operand 64).read u = bswap64 (canonicalLimb x 1)
        rw [← output]
        exact effect.writes.2.2.2.2.2.2.1.trans (congrArg bswap64 (by
          change memLoad t.external (stackPtr t + 1024) 64 = canonicalLimb x 1
          simpa only [Nat.reduceMul,BitVec.add_assoc,BitVec.ofNat_eq_ofNat,BitVec.reduceAdd] using words 1 (by decide)))
      · change (Operand.mem (s.regValue .rdi + 24) : Operand 64).read u = bswap64 (canonicalLimb x 0)
        rw [← output]
        exact effect.writes.2.2.2.2.2.2.2.trans (congrArg bswap64 (by
          change memLoad t.external (stackPtr t + 1016) 64 = canonicalLimb x 0
          simpa only [Nat.reduceMul,BitVec.add_assoc,BitVec.ofNat_eq_ofNat,BitVec.reduceAdd,BitVec.add_zero] using words 0 (by decide))))
  refine ⟨fuel,u,run,next,effect.rip,natToOctets_size 32 x,?_⟩
  intro i
  have hi : i.val < 32 := by simpa only [natToOctets_size] using i.isLt
  change u.external[BitVec.ofNat 64 ((s.regValue .rdi).toNat + i.val)]? = _
  rw [BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq,
    ByteArray.getElem_eq_getElem_data,natToOctets_getElem 32 x i.val hi]
  exact bytes i.val hi

end P256.Proofs.Ecdh.Normalize.Finish.Output
