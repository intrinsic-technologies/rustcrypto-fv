import P256.Proofs.Signing.Wrapper.Entry.Decode.ReadResult
import P256.Proofs.Signing.Wrapper.Entry.Decode.Saved
import P256.Proofs.Signing.Wrapper.Entry.Decode.Load
import P256.Proofs.Signing.Wrapper.Entry.Decode.Branch
import P256.Proofs.Signing.Wrapper.Entry.Decode.Compare.Correct

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Entry.Decode

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program Prelude
open X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.SecretKeyFromBytes.Scalar (Nat256At limbs_ofNat_toNat)

structure LimbsAt (s : RamState) (d : Nat) : Prop where
  word0 : s.regValue .rbp = BitVec.ofNat 64 d
  word1 : s.regValue .r14 = BitVec.ofNat 64 (d/2^64)
  word2 : s.regValue .rbx = BitVec.ofNat 64 (d/2^128)
  word3 : s.regValue .r15 = BitVec.ofNat 64 (d/2^192)

structure Compared [Bindings] (initial s : RamState) (secret : ByteArray) : Prop extends
    State initial s 520, Saved initial s, LimbsAt s (Arith.uint secret) where
  rip : s.RIP = 0x10255d
  valid : s.regValue .rdi = 1

theorem scalar_range [Bindings] {initial s : RamState} {secret message : ByteArray}
    (context : Context initial secret message) (state : ReadState initial s secret) :
    ∃ fuel t, Advances (returnBoundary initial) fuel s t ∧ Compared initial t secret := by
  obtain ⟨slices,call⟩ := context.call
  have hs : Stack.Valid initial 5112 := call.stackAvailable.1
  have avoids : (Stack.region initial 5112).Avoids (fun a => InProgram a ∨ InPageTables a) :=
    by simpa only [signingKeyTrySign] using call_stack_avoids call
  have outside := outer_boundary call context.machine context.bindingsSupported
  obtain ⟨a,ha,ra,ipa,fa⟩ := read_status
    (readyToStep state.machine state.bindingsSupported) state.loaded state.rip state.status outside
  have sa := after_stack call state.toState ha ra fa (by simp) (by simp) (by simp)
  have ma := fa.external (by simp [Component.Covers])
  obtain ⟨n,b,hb,rb,_,eb⟩ := load_correct (returnBoundary initial) outside a ra
    (programText_slice (programLoaded_codeIn sa.loaded) 0x246e loadBytes
      (by decide) (by decide +kernel)) (block_pre call sa ipa (by simp) (by simp))
  have sb := after_stack call sa hb rb eb.agrees
    (by
      intro p len hp
      simp only [loadEffect,Effect.components,Write.component,Operand.component,List.map_cons,
        List.map_nil,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at hp
      rcases hp with (h | h | h | h | h | h | h) | h
      all_goals cases h
      · exact ⟨328,by decide,rfl⟩
      · exact ⟨320,by decide,rfl⟩
      · exact ⟨312,by decide,rfl⟩)
    (by simp [loadEffect,Effect.components]) (by simp [loadEffect,Effect.components])
  have scalar : Nat256At a (stackPtr a) (Arith.uint secret) := by
    simpa only [sa.rsp,Nat256At,ma,BitVec.ofNat_eq_ofNat] using state.value
  have limbs : LimbsAt b (Arith.uint secret) := by
    refine ⟨?_,?_,?_,?_⟩
    · exact eb.writes.2.2.2.1.trans (by
        simpa only [Nat.mul_zero,Nat.pow_zero,Nat.div_one,BitVec.ofNat_eq_ofNat,BitVec.add_zero] using scalar.memLoad_limb 0 (by decide))
    · exact eb.writes.2.2.2.2.1.trans (by
        simpa only [BitVec.ofNat_eq_ofNat] using scalar.memLoad_limb 1 (by decide))
    · exact eb.writes.2.2.2.2.2.1.trans (by
        simpa only [BitVec.ofNat_eq_ofNat] using scalar.memLoad_limb 2 (by decide))
    · exact eb.writes.2.2.2.2.2.2.trans (by
        simpa only [BitVec.ofNat_eq_ofNat] using scalar.memLoad_limb 3 (by decide))
  have saved : Saved initial b := by
    refine ⟨?_,?_,?_,?_,?_⟩
    · exact ((fa.trans eb.agrees).read (n:=64) (r:=12)
        (by simp [loadEffect,Effect.components])).trans state.pointers
    · exact ((fa.trans eb.agrees).read (n:=64) (r:=13)
        (by simp [loadEffect,Effect.components])).trans state.count
    · have h := eb.writes.1
      change memLoad b.external (stackPtr a+328) 64 = a.regValue .r15 at h
      rw [show stackPtr a+328 = stackPtr initial-192 from stack_address sa (by decide)] at h
      exact h.trans ((fa.read (n:=64) (r:=15) (by simp)).trans state.lengths)
    · have h := eb.writes.2.2.1
      change memLoad b.external (stackPtr a+312) 64 = a.regValue .rbx at h
      rw [show stackPtr a+312 = stackPtr initial-208 from stack_address sa (by decide)] at h
      exact h.trans ((fa.read (n:=64) (r:=3) (by simp)).trans state.output)
    · have h := eb.writes.2.1
      change memLoad b.external (stackPtr a+320) 64 = a.regValue .r14 at h
      rw [show stackPtr a+320 = stackPtr initial-200 from stack_address sa (by decide)] at h
      exact h.trans ((fa.read (n:=64) (r:=14) (by simp)).trans state.capacity)
  have pre : Compare.BorrowSlotPre 0x102499 b := by
    refine ⟨eb.rip,?_,?_⟩
    · rw [show stackPtr b+176 = stackPtr initial-344 from stack_address sb (by decide)]
      exact writable_of_grow (stack_sub_writable8 hs
        (fun a ha hpt => avoids a ha (.inr hpt)) (offset:=344) (by decide) (by decide)) sb.allocated
    · intro a ha hin
      obtain ⟨i,hi,rfl⟩ := ha
      have addr : stackPtr b+176 = stackPtr initial-344 := stack_address sb (by decide)
      rw [addr] at hin
      exact (stack_buffer_avoids hs avoids (offset:=344) (len:=8) (by decide) (by decide)) _
        (memoryRegion_contains_add (stack_buffer_bounded hs (offset:=344) (len:=8)
          (by decide) (by decide)) (Nat.le_refl _) (Nat.le_refl _) hi) (.inl hin)
  obtain ⟨k,t,ht,rt,_,pt,ft,vt⟩ := Compare.compare_correct outside rb sb.loaded pre
  have st := after_stack call sb ht rt ft
    (by intro p len hp; simp only [Compare.compareFrame,List.mem_cons,List.not_mem_nil,or_false] at hp
        rcases hp with h | h | h | h | h | h | h | h
        all_goals cases h
        exact ⟨176,by decide,rfl⟩)
    (by simp [Compare.compareFrame]) (by simp [Compare.compareFrame])
  have sv := saved.preserve sb ft (by simp [Compare.compareFrame])
    (by simp [Compare.compareFrame]) (by
      intro target member p len hp
      simp only [Compare.compareFrame,List.mem_cons,List.not_mem_nil,or_false] at hp
      rcases hp with h | h | h | h | h | h | h | h
      all_goals cases h
      refine ⟨176,by decide,?_,rfl⟩
      simp only [List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with rfl | rfl | rfl <;> decide)
  have number : (Compare.compareInput b).toNat = Arith.uint secret := by
    change (b.regValue .rbp).toNat+2^64*((b.regValue .r14).toNat+
      2^64*((b.regValue .rbx).toNat+2^64*(b.regValue .r15).toNat)) = _
    rw [limbs.word0,limbs.word1,limbs.word2,limbs.word3]
    exact limbs_ofNat_toNat _ scalar.1
  refine ⟨2+n+k,t,(ha.trans hb).trans ht,⟨st,sv,?_,pt.rip,?_⟩⟩
  · refine ⟨?_,?_,?_,?_⟩
    · exact (ft.read (n:=64) (r:=5) (by simp [Compare.compareFrame])).trans limbs.word0
    · exact (ft.read (n:=64) (r:=14) (by simp [Compare.compareFrame])).trans limbs.word1
    · exact (ft.read (n:=64) (r:=3) (by simp [Compare.compareFrame])).trans limbs.word2
    · exact (ft.read (n:=64) (r:=15) (by simp [Compare.compareFrame])).trans limbs.word3
  · simpa only [number,ite_eq_left ((arguments_iff secret message).mp call.argumentsValid).2.2] using vt

end P256.Proofs.Signing.Wrapper.Entry.Decode
