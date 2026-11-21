import P256.Proofs.Signing.Core.Iteration.Output.Memory
import P256.Proofs.Signing.Core.Iteration.Output.Blocks.Copy
import P256.Proofs.Sec1.Representation

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Output

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Program SecretKeyFromBytes.Scalar
open NextNonce (base_add)

variable [Bindings] {s t : RamState} {boundary : ReturnBoundary} {r scalarS x y : Nat}

theorem copy_signature (pre : SignPre s boundary) (frame : Frame s t)
    (output : (Operand.mem (frameBase s+72) : Operand 64).read t = s.regValue .rdi)
    (rip : t.RIP = 0x10d377)
    (first : Nat256At t (frameBase s+536) r) (second : Nat256At t (frameBase s+568) scalarS)
    (lo : t.regValue .r12 = BitVec.ofNat 64 r)
    (next : t.regValue .rbx = BitVec.ofNat 64 (r/2^64)) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ Payload s u r scalarS ∧
      u.RIP = 0x10d3c4 ∧
      (∀ offset, offset < 2280 → u.external[frameBase s+BitVec.ofNat 64 offset]? =
        t.external[frameBase s+BitVec.ofNat 64 offset]?) := by
  have dst : Blocks.Copy.destination t = s.regValue .rdi := by
    change (Operand.mem (stackPtr t+72) : Operand 64).read t = _
    rw [frame.rsp]
    exact output
  have raw : Blocks.Copy.Pre t := by
    refine ⟨rip,?_,?_,?_,?_⟩
    · intro off ho
      change MemReadable t (stackPtr t+BitVec.ofNat 64 off) 8
      rw [frame.rsp]
      exact local_readable pre frame (by simp only [List.mem_cons,List.not_mem_nil,or_false] at ho; omega)
    · intro off ho
      rw [dst]
      exact (ScalarFrame.output_writable pre.toCalleePre (by decide) frame.allocated).add off
        (by simp only [List.mem_cons,List.not_mem_nil,or_false] at ho; omega)
    · change RangeApart (Blocks.Copy.destination t) 64 (stackPtr t) 600
      rw [dst,frame.rsp]
      exact fun i hi j hj => output_stack_apart pre i (by omega) j (by omega)
    · intro off ho co cl hc
      rw [dst]
      intro i hi j hj eq
      apply ScalarFrame.output_code pre.toCalleePre hc (off+i) (by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at ho; omega) j hj
      simpa only [BitVec.ofNat_add,BitVec.add_assoc] using eq
  obtain ⟨n,u,run,ready,_,effect⟩ := Blocks.Copy.correct boundary pre.outerBoundary t
    (readyToStep frame.machine frame.bindingsSupported)
    (programText_slice (programLoaded_codeIn frame.loaded) 0xd377 Blocks.Copy.bytes
      (by decide) (by decide +kernel)) raw
  have writes : ∀ c ∈ (Blocks.Copy.effect t).components, ∀ a, c.Covers a →
      ∃ off ∈ ([16,24,32,40,48,56] : List Nat), ∃ i < 8,
        a = s.regValue .rdi+BitVec.ofNat 64 off+BitVec.ofNat 64 i := by
    intro c hc a ha
    simp only [Blocks.Copy.effect,Effect.components,List.map_cons,List.map_nil,
      Write.component_reg,Write.component_mem,List.cons_append,List.nil_append,
      List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> try exact ha.elim
    all_goals obtain ⟨i,hi,eq⟩ := ha; rw [dst] at eq
    · exact ⟨56,by simp,i,hi,eq⟩
    · exact ⟨48,by simp,i,hi,eq⟩
    · exact ⟨40,by simp,i,hi,eq⟩
    · exact ⟨32,by simp,i,hi,eq⟩
    · exact ⟨24,by simp,i,hi,eq⟩
    · exact ⟨16,by simp,i,hi,eq⟩
  have fu := after_agrees pre frame ready effect.agrees (by
      intro c hc a ha
      obtain ⟨off,ho,i,hi,rfl⟩ := writes c hc a ha
      refine ⟨registerRegion s .rdi 65,by simp,?_⟩
      exact ScalarFrame.output_contains pre.toCalleePre
        (by simp only [List.mem_cons,List.not_mem_nil,or_false] at ho; omega) ⟨i,hi,rfl⟩)
    (effect.agrees.read (n:=64) (r:=4) (by simp [Blocks.Copy.effect,Effect.components]))
    (by simp [Blocks.Copy.effect,Effect.components]) (by simp [Blocks.Copy.effect,Effect.components])
    (by simp [Blocks.Copy.effect,Effect.components])
  have mem (offset : Nat) (bound : offset < 2280) :
      u.external[frameBase s+BitVec.ofNat 64 offset]? = t.external[frameBase s+BitVec.ofNat 64 offset]? := by
    apply effect.agrees.byte
    intro c hc ha
    obtain ⟨off,ho,i,hi,eq⟩ := writes c hc _ ha
    apply output_stack_apart pre (off+i) (by simp only [List.mem_cons,List.not_mem_nil,or_false] at ho; omega) offset bound
    simpa only [BitVec.ofNat_add,BitVec.add_assoc] using eq.symm
  have hw := effect.writes
  change _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _ at hw
  rcases hw with ⟨_,dest,_,s3,s2,s1,s0,r3,r2⟩
  have limbR (j : Nat) (hj : j < 4) := first.memLoad_limb j hj
  have limbS (j : Nat) (hj : j < 4) := second.memLoad_limb j hj
  have payload : Payload s u r scalarS := by
    refine ⟨first.1,
      (effect.agrees.read (n:=64) (r:=12) (by simp [Blocks.Copy.effect,Effect.components])).trans lo,
      (effect.agrees.read (n:=64) (r:=3) (by simp [Blocks.Copy.effect,Effect.components])).trans next,
      ?_,?_,?_,?_⟩
    · have h : memLoad u.external (Blocks.Copy.destination t+16) 64 = memLoad t.external (stackPtr t+552) 64 := r2
      rw [dst,frame.rsp] at h
      exact h.trans (by simpa [BitVec.add_assoc] using limbR 2 (by decide))
    · have h : memLoad u.external (Blocks.Copy.destination t+24) 64 = memLoad t.external (stackPtr t+560) 64 := r3
      rw [dst,frame.rsp] at h
      exact h.trans (by simpa [BitVec.add_assoc] using limbR 3 (by decide))
    · apply nat256At_of_memLoad_limbs second.1
      · intro i hi
        exact fu.allocated _ (Option.isSome_iff_exists.mpr (pre.outputAllocated _
          (by simpa only [BitVec.add_assoc,BitVec.ofNat_add,BitVec.ofNat_eq_ofNat] using
            memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) (show 32+i<65 by omega))))
      · intro j hj
        rcases (show j=0 ∨ j=1 ∨ j=2 ∨ j=3 by omega) with rfl|rfl|rfl|rfl
        all_goals simp only [Nat.reduceMul,BitVec.ofNat_eq_ofNat,BitVec.add_assoc,BitVec.reduceAdd,BitVec.add_zero]
        · have h : memLoad u.external (Blocks.Copy.destination t+32) 64 = memLoad t.external (stackPtr t+568) 64 := s0
          rw [dst,frame.rsp] at h
          exact h.trans (by simpa [BitVec.add_assoc] using limbS 0 (by decide))
        · have h : memLoad u.external (Blocks.Copy.destination t+40) 64 = memLoad t.external (stackPtr t+576) 64 := s1
          rw [dst,frame.rsp] at h
          exact h.trans (by simpa [BitVec.add_assoc] using limbS 1 (by decide))
        · have h : memLoad u.external (Blocks.Copy.destination t+48) 64 = memLoad t.external (stackPtr t+584) 64 := s2
          rw [dst,frame.rsp] at h
          exact h.trans (by simpa [BitVec.add_assoc] using limbS 2 (by decide))
        · have h : memLoad u.external (Blocks.Copy.destination t+56) 64 = memLoad t.external (stackPtr t+592) 64 := s3
          rw [dst,frame.rsp] at h
          exact h.trans (by simpa [BitVec.add_assoc] using limbS 3 (by decide))
    · exact dest.trans dst
  exact ⟨n,u,run,fu,payload,effect.rip,mem⟩

end P256.Proofs.Signing.Core.Iteration.Output
