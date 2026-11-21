import P256.Proofs.Signing.Core.Iteration.Output.Memory
import P256.Proofs.Common.Encoding.Parser.ByteStore

set_option autoImplicit false

namespace P256.Proofs.Signing.Core.Iteration.Output

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Program SecretKeyFromBytes.Scalar
open Common.Instructions

variable [Bindings] {s t u : RamState} {boundary : ReturnBoundary} {r scalarS : Nat}

theorem output_store_frame {offset len : Nat}
    (pre : SignPre s boundary) (frame : Frame s t) (ready : ReadyToStep u)
    (ag : AgreesExcept [.mem (s.regValue .rdi+BitVec.ofNat 64 offset) len,.rip] t u)
    (bound : offset+len ≤ 65) : Frame s u := by
  exact after_agrees pre frame ready ag (by
    intro c hc a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl
    · exact ⟨registerRegion s .rdi 65,by simp,ScalarFrame.output_contains pre.toCalleePre bound ha⟩
    · exact ha.elim)
    (ag.read (n:=64) (r:=4) (by simp)) (by simp) (by simp) (by simp)

omit [Bindings] in
theorem output_store_byte {offset len pos : Nat}
    (ag : AgreesExcept [.mem (s.regValue .rdi+BitVec.ofNat 64 offset) len,.rip] t u)
    (bound : offset+len < 2^64) (pbound : pos < 2^64)
    (apart : pos < offset ∨ offset+len ≤ pos) :
    u.external[s.regValue .rdi+BitVec.ofNat 64 pos]? = t.external[s.regValue .rdi+BitVec.ofNat 64 pos]? := by
  apply ag.byte
  intro c hc ha
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl
  · obtain ⟨i,hi,eq⟩ := ha
    rw [BitVec.add_assoc,← BitVec.ofNat_add] at eq
    have h := congrArg BitVec.toNat ((BitVec.add_right_inj (s.regValue .rdi)).mp eq)
    simp only [BitVec.toNat_ofNat,Nat.mod_eq_of_lt pbound,Nat.mod_eq_of_lt (by omega : offset+i<2^64)] at h
    omega
  · exact ha.elim

theorem store_signature (pre : SignPre s boundary) (frame : Frame s t)
    (payload : Payload s t r scalarS) (rip : t.RIP = 0x10d4c2) :
    ∃ u, Advances boundary 3 t u ∧ Frame s u ∧ u.RIP = 0x10d4cd ∧
      Nat256At u (s.regValue .rdi) r ∧ Nat256At u (s.regValue .rdi+32#64) scalarS := by
  have code (off len co cl : Nat) (ho : off+len ≤ 65) (hc : co+cl ≤ 118431) :
      RangeApart (s.regValue .rdi+BitVec.ofNat 64 off) len
        (Extracted.textAddress+BitVec.ofNat 64 co) cl :=
    Common.Instructions.RangeApart.add_left (ScalarFrame.output_code pre.toCalleePre hc) off ho
  obtain ⟨a,runA,readyA,ea⟩ :=
    (CrossPageStore.mov_m64_r64_effect_step_any 0x10d4c2 0x4d (by simp [RexWPrefix]) 4
      (.base 15 .none) (by decide) rfl rfl).advances
      (readyToStep frame.machine frame.bindingsSupported)
      (programText_slice (programLoaded_codeIn frame.loaded) 0xd4c2 _ (by decide) (by decide +kernel))
      ⟨rip,by change CrossPageStore.Writable t (t.regValue .r15+0#64) 8; rw [BitVec.add_zero,payload.destination]
              simpa only [BitVec.add_zero] using (ScalarFrame.output_writable pre.toCalleePre (by decide) frame.allocated).add 0 (by decide),
        by change RangeApart (t.regValue .r15+0#64) 8 0x10d4c2#64 3; rw [BitVec.add_zero,payload.destination]
           simpa only [BitVec.add_zero,Extracted.textAddress,BitVec.reduceAdd] using code 0 8 0xd4c2 3 (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xd4c5 (by decide)))
  have aa : AgreesExcept [.mem (s.regValue .rdi+BitVec.ofNat 64 0) 8,.rip] t a := by
    have h := ea.agrees
    simp only [movM64R64Effect,storeEffect_components] at h
    change AgreesExcept [.mem (t.regValue .r15+0#64) 8,.rip] t a at h
    simpa only [payload.destination,BitVec.add_zero] using h
  have fa := output_store_frame pre frame readyA aa (by decide)
  have da : a.regValue .r15 = s.regValue .rdi := (aa.read (n:=64) (r:=15) (by simp)).trans payload.destination
  obtain ⟨b,runB,readyB,eb⟩ :=
    (CrossPageStore.mov_m64_r64_effect_step_any 0x10d4c5 0x49 (by simp [RexWPrefix]) 3
      (.base 15 (.d8 8)) (by decide) rfl rfl).advances readyA
      (programText_slice (programLoaded_codeIn fa.loaded) 0xd4c5 _ (by decide) (by decide +kernel))
      ⟨ea.rip,by change CrossPageStore.Writable a (a.regValue .r15+8#64) 8; rw [da]
                 exact (ScalarFrame.output_writable pre.toCalleePre (by decide) fa.allocated).add 8 (by decide),
        by change RangeApart (a.regValue .r15+8#64) 8 0x10d4c5 4; rw [da]
           exact code 8 8 0xd4c5 4 (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xd4c9 (by decide)))
  have ab : AgreesExcept [.mem (s.regValue .rdi+BitVec.ofNat 64 8) 8,.rip] a b := by
    have h := eb.agrees
    simp only [movM64R64Effect,storeEffect_components] at h
    change AgreesExcept [.mem (a.regValue .r15+8#64) 8,.rip] a b at h
    simpa only [da] using h
  have fb := output_store_frame pre fa readyB ab (by decide)
  have db : b.regValue .r15 = s.regValue .rdi := (ab.read (n:=64) (r:=15) (by simp)).trans da
  obtain ⟨u,runU,readyU,eu⟩ :=
    (mov_m8_r8_effect_step 0x10d4c9 0x41 (by simp [RexPrefix]) 5
      (.base 15 (.d8 64)) (by decide) rfl rfl).advances readyB
      (programText_slice (programLoaded_codeIn fb.loaded) 0xd4c9 _ (by decide) (by decide +kernel))
      ⟨eb.rip,by
        change MemWritable b (b.regValue .r15+64#64) 1; rw [db]
        have w := (ScalarFrame.output_writable pre.toCalleePre (by decide) fb.allocated).add 64 (len:=1) (by decide)
        exact ⟨w.low,w.mem,w.tables⟩,
        by change RangeApart (b.regValue .r15+64#64) 1 0x10d4c9 4; rw [db]
           exact code 64 1 0xd4c9 4 (by decide) (by decide)⟩
      (boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xd4cd (by decide)))
  have au : AgreesExcept [.mem (s.regValue .rdi+BitVec.ofNat 64 64) 1,.rip] b u := by
    have h := eu.agrees
    simp only [storeEffect_components] at h
    change AgreesExcept [.mem (b.regValue .r15+64#64) 1,.rip] b u at h
    simpa only [db] using h
  have fu := output_store_frame pre fb readyU au (by decide)
  have keepU (off : Nat) (ho : off+8 ≤ 64) :
      memLoad u.external (s.regValue .rdi+BitVec.ofNat 64 off) 64 = memLoad b.external (s.regValue .rdi+BitVec.ofNat 64 off) 64 := by
    apply memLoad_congr
    intro i hi
    change (u.external[_]?).getD 0 = (_[_]?).getD 0
    apply congrArg (fun x : Option UInt8 => x.getD 0)
    simpa only [BitVec.ofNat_add,BitVec.add_assoc] using output_store_byte au (pos:=off+i) (by decide) (by omega) (.inl (by omega))
  have keep (pos : Nat) (lo : 16 ≤ pos) (hi : pos < 64) :
      u.external[s.regValue .rdi+BitVec.ofNat 64 pos]? = t.external[s.regValue .rdi+BitVec.ofNat 64 pos]? :=
    (output_store_byte au (by decide) (by omega) (.inl hi)).trans
      ((output_store_byte ab (by decide) (by omega) (.inr lo)).trans
        (output_store_byte aa (by decide) (by omega) (.inr (by omega))))
  have low : memLoad u.external (s.regValue .rdi) 64 = BitVec.ofNat 64 r := by
    have ha : memLoad a.external (t.regValue .r15+0#64) 64 = t.regValue .r12 := ea.writes
    simp only [BitVec.add_zero] at ha
    rw [payload.destination,payload.low] at ha
    have hb : memLoad b.external (s.regValue .rdi) 64 = memLoad a.external (s.regValue .rdi) 64 := by
      apply memLoad_congr
      intro i hi
      exact congrArg (fun x : Option UInt8 => x.getD 0) (output_store_byte ab (by decide) (by omega) (.inl hi))
    have hu : memLoad u.external (s.regValue .rdi) 64 = memLoad b.external (s.regValue .rdi) 64 := by simpa only [BitVec.add_zero] using keepU 0 (by decide)
    exact hu.trans (hb.trans ha)
  have next : memLoad u.external (s.regValue .rdi+8#64) 64 = BitVec.ofNat 64 (r/2^64) := by
    have hb : memLoad b.external (a.regValue .r15+8#64) 64 = a.regValue .rbx := eb.writes
    have rb : a.regValue .rbx = t.regValue .rbx := aa.read (n:=64) (r:=3) (by simp)
    rw [da,rb,payload.next] at hb
    exact (keepU 8 (by decide)).trans hb
  have high (off : Nat) (ho : off = 16 ∨ off = 24) :
      memLoad u.external (s.regValue .rdi+BitVec.ofNat 64 off) 64 = memLoad t.external (s.regValue .rdi+BitVec.ofNat 64 off) 64 := by
    apply memLoad_congr
    intro i hi
    change (u.external[_]?).getD 0 = (_[_]?).getD 0
    apply congrArg (fun x : Option UInt8 => x.getD 0)
    simpa only [BitVec.ofNat_add,BitVec.add_assoc] using keep (off+i) (by omega) (by omega)
  refine ⟨u,(runA.trans runB).trans runU,fu,eu.rip,?_,?_⟩
  · apply nat256At_of_memLoad_limbs payload.bounded
    · intro i hi
      exact fu.allocated _ (Option.isSome_iff_exists.mpr (pre.outputAllocated _
        (memoryRegion_contains_add pre.outputBounded (Nat.le_refl _) (Nat.le_refl _) (show i<65 by omega))))
    · intro j hj
      rcases (show j=0 ∨ j=1 ∨ j=2 ∨ j=3 by omega) with rfl|rfl|rfl|rfl
      · simpa using low
      · simpa using next
      · exact (high 16 (by simp)).trans payload.third
      · exact (high 24 (by simp)).trans payload.fourth
  · refine ⟨payload.second.1,?_⟩
    intro i hi
    have h := keep (32+i) (by omega) (by omega)
    simp only [BitVec.ofNat_add,← BitVec.add_assoc] at h
    exact h.trans (payload.second.2 i hi)

end P256.Proofs.Signing.Core.Iteration.Output
