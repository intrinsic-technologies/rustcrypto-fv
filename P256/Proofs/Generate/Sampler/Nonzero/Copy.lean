import P256.Proofs.Generate.Sampler.Nonzero.CopyBlock
import P256.Proofs.Program.ScalarFrame.Copy32Bytes

set_option autoImplicit false

namespace P256.Proofs.Generate.Sampler.Nonzero

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Program Program.ScalarFrame SecretKeyFromBytes.Scalar

def copyClobbers (t : RamState) : List Component :=
  [.reg 0,.reg 1,.reg 2,.reg 6,.rip,.mem (stackPtr t+8) 32,.mem (stackPtr t+184) 32]

theorem copy_byte {t u : RamState} {src : BitVec 64} {len : Nat}
    (agrees : AgreesExcept (copyClobbers t) t u)
    (apart : OffsetsApart 8 32 src len) (apartDuplicate : OffsetsApart 184 32 src len)
    (bound : 32 + len < 2^64)
    (i : Nat) (hi : i < len) :
    u.external[stackPtr t + src + BitVec.ofNat 64 i]? =
      t.external[stackPtr t + src + BitVec.ofNat 64 i]? := by
  apply agrees.byte
  intro c hc cover
  simp only [copyClobbers,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> try exact cover.elim
  · obtain ⟨j,hj,eq⟩ := cover
    exact apart.ne (stackPtr t) hj hi bound eq.symm
  · obtain ⟨j,hj,eq⟩ := cover
    exact apartDuplicate.ne (stackPtr t) hj hi bound eq.symm

theorem copy [Bindings] {s t : RamState} {boundary : ReturnBoundary} {input : ByteArray} {d : Nat}
    (pre : Pre s boundary input) (state : State s t)
    (rip : t.RIP = 0x100c00)
    (scalar : Nat256At t (stackPtr t+80) d) :
    ∃ n u, Advances boundary n t u ∧ State s u ∧ u.RIP = 0x100c48 ∧
      (∀ off ∈ ([8,184] : List (BitVec 64)), Nat256At u (stackPtr u+off) d) ∧
      AgreesExcept (copyClobbers t) t u := by
  have hp : CopyBlock.Pre t := by
    refine ⟨rip,?_,?_,?_⟩
    · intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl
      all_goals exact state.stack_readable pre (by decide)
    · intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals exact (state.stack_writable pre (by decide)).crossPage (by decide)
    · intro i hi off len bound
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals exact state.stack_code pre (by decide) bound
  obtain ⟨n,u,run,ready,_,effect⟩ := CopyBlock.run boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0xc00 CopyBlock.bytes
      (by decide) (by decide +kernel)) hp
  have g : AgreesExcept (copyClobbers t) t u := by
    apply effect.agrees.widen
    · intro c hc hm
      simp only [CopyBlock.effect,Effect.components,List.map_cons,List.map_nil,
        Write.component,Operand.component,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
      all_goals try simp [copyClobbers]
      all_goals simp [Component.isMem] at hm
    · intro a c hc ha
      simp only [CopyBlock.effect,Effect.components,List.map_cons,List.map_nil,
        Write.component,Operand.component,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
      all_goals try exact ha.elim
      all_goals
        obtain ⟨i,hi,rfl⟩ := ha
      · refine ⟨.mem (stackPtr t+8) 32,by simp [copyClobbers],?_⟩
        exact ⟨0+i,by omega,by
          simp only [stackPtr,Operand.read_reg64,BitVec.ofNat_eq_ofNat,BitVec.ofNat_add,BitVec.add_assoc]
          rw [←BitVec.add_assoc (8#64) (0#64) (BitVec.ofNat 64 i)]
          rfl⟩
      · refine ⟨.mem (stackPtr t+8) 32,by simp [copyClobbers],?_⟩
        exact ⟨8+i,by omega,by
          simp only [stackPtr,Operand.read_reg64,BitVec.ofNat_eq_ofNat,BitVec.ofNat_add,BitVec.add_assoc]
          rw [←BitVec.add_assoc (8#64) (8#64) (BitVec.ofNat 64 i)]
          rfl⟩
      · refine ⟨.mem (stackPtr t+8) 32,by simp [copyClobbers],?_⟩
        exact ⟨16+i,by omega,by
          simp only [stackPtr,Operand.read_reg64,BitVec.ofNat_eq_ofNat,BitVec.ofNat_add,BitVec.add_assoc]
          rw [←BitVec.add_assoc (8#64) (16#64) (BitVec.ofNat 64 i)]
          rfl⟩
      · refine ⟨.mem (stackPtr t+8) 32,by simp [copyClobbers],?_⟩
        exact ⟨24+i,by omega,by
          simp only [stackPtr,Operand.read_reg64,BitVec.ofNat_eq_ofNat,BitVec.ofNat_add,BitVec.add_assoc]
          rw [←BitVec.add_assoc (8#64) (24#64) (BitVec.ofNat 64 i)]
          rfl⟩
      · refine ⟨.mem (stackPtr t+184) 32,by simp [copyClobbers],?_⟩
        exact ⟨0+i,by omega,by
          simp only [stackPtr,Operand.read_reg64,BitVec.ofNat_eq_ofNat,BitVec.ofNat_add,BitVec.add_assoc]
          rw [←BitVec.add_assoc (184#64) (0#64) (BitVec.ofNat 64 i)]
          rfl⟩
      · refine ⟨.mem (stackPtr t+184) 32,by simp [copyClobbers],?_⟩
        exact ⟨8+i,by omega,by
          simp only [stackPtr,Operand.read_reg64,BitVec.ofNat_eq_ofNat,BitVec.ofNat_add,BitVec.add_assoc]
          rw [←BitVec.add_assoc (184#64) (8#64) (BitVec.ofNat 64 i)]
          rfl⟩
      · refine ⟨.mem (stackPtr t+184) 32,by simp [copyClobbers],?_⟩
        exact ⟨16+i,by omega,by
          simp only [stackPtr,Operand.read_reg64,BitVec.ofNat_eq_ofNat,BitVec.ofNat_add,BitVec.add_assoc]
          rw [←BitVec.add_assoc (184#64) (16#64) (BitVec.ofNat 64 i)]
          rfl⟩
      · refine ⟨.mem (stackPtr t+184) 32,by simp [copyClobbers],?_⟩
        exact ⟨24+i,by omega,by
          simp only [stackPtr,Operand.read_reg64,BitVec.ofNat_eq_ofNat,BitVec.ofNat_add,BitVec.add_assoc]
          rw [←BitVec.add_assoc (184#64) (24#64) (BitVec.ofNat 64 i)]
          rfl⟩
  have rsp : stackPtr u = stackPtr t := g.read (n := 64) (r := 4) (by simp [copyClobbers])
  have next := state.after pre ready g (by
    intro c hc a ha
    simp only [copyClobbers,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> try exact ha.elim
    all_goals exact ⟨workRegion s 3624,by simp [bodyWrites],state.work_writes pre (by decide) ha⟩) rsp
  refine ⟨n,u,run,next,effect.rip,?_,g⟩
  intro off ho
  simp only [List.mem_cons,List.not_mem_nil,or_false] at ho
  have values := effect.writes
  change _ ∧ _ ∧ _ ∧ _ ∧
    memLoad u.external (stackPtr t+8) 64 = memLoad t.external (stackPtr t+80) 64 ∧
    memLoad u.external (stackPtr t+16) 64 = memLoad t.external (stackPtr t+88) 64 ∧
    memLoad u.external (stackPtr t+24) 64 = memLoad t.external (stackPtr t+96) 64 ∧
    memLoad u.external (stackPtr t+32) 64 = memLoad t.external (stackPtr t+104) 64 ∧
    memLoad u.external (stackPtr t+184) 64 = memLoad t.external (stackPtr t+80) 64 ∧
    memLoad u.external (stackPtr t+192) 64 = memLoad t.external (stackPtr t+88) 64 ∧
    memLoad u.external (stackPtr t+200) 64 = memLoad t.external (stackPtr t+96) 64 ∧
    memLoad u.external (stackPtr t+208) 64 = memLoad t.external (stackPtr t+104) 64 at values
  rcases ho with rfl | rfl
  all_goals
    apply nat256At_of_memLoad_limbs scalar.1 (next.stack_readable pre (by decide)).mem
    intro j hj
    have h := scalar.memLoad_limb j hj
    have cases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    all_goals simp only [rsp,Nat.mul_zero,Nat.mul_one,Nat.reduceMul,BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd,BitVec.add_zero] at h ⊢
  · exact (values.2.2.2.2.1).trans h
  · exact (values.2.2.2.2.2.1).trans h
  · exact (values.2.2.2.2.2.2.1).trans h
  · exact (values.2.2.2.2.2.2.2.1).trans h
  · exact (values.2.2.2.2.2.2.2.2.1).trans h
  · exact (values.2.2.2.2.2.2.2.2.2.1).trans h
  · exact (values.2.2.2.2.2.2.2.2.2.2.1).trans h
  · exact (values.2.2.2.2.2.2.2.2.2.2.2).trans h

end P256.Proofs.Generate.Sampler.Nonzero
