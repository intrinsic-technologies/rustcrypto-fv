import Sha3.Proofs.Finalize.Finish.Full
import Sha3.Proofs.Calls
import Sha3.Proofs.Memcpy

namespace Sha3.Proofs.Finalize

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

theorem SavedFrame.after_full_call {boundary : ReturnBoundary}
    {state : Incremental.State} {initial s t : RamState}
    (hp : CallPre boundary .sha256 true state initial true true)
    (h : SavedFrame .sha256 initial s true)
    (ha : AgreesExcept [.reg 4, .mem (initial.regValue .rsp - 32) 8, .rip] s t) :
    SavedFrame .sha256 initial t true := by
  have hslot (k : Nat) (hk : k ≤ 16) :
      (Operand.mem (initial.regValue .rsp - BitVec.ofNat 64 k) : Operand 64).read t =
        (Operand.mem (initial.regValue .rsp - BitVec.ofNat 64 k) : Operand 64).read s := by
    apply read_of_agrees ha
    intro i hi c hc hcover
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> try exact hcover
    obtain ⟨j, hj, he⟩ := hcover
    have hap : RangeApart (initial.regValue .rsp - 32) 8
        (initial.regValue .rsp - BitVec.ofNat 64 k) 8 := by
      rw [frame_offset initial (by omega : k ≤ 296)]
      change RangeApart (initial.regValue .rsp - BitVec.ofNat 64 32) 8 _ 8
      rw [frame_offset initial (by decide : 32 ≤ 296)]
      exact RangeApart.offsets (frameBase initial) (a := 264) (len := 8)
        (b := 296 - k) (count := 8) (by decide) (by omega) (.inl (by omega))
    exact hap j hj i hi he.symm
  refine {
    saved := fun r hr ↦ ?_
    rbx := (hslot 16 (by decide)).trans h.rbx
    r14 := (hslot 8 (by decide)).trans h.r14
    returnSlot := ?_
    memory := memoryWriteFrame_trans h.memory (ha.memoryWriteFrame ?_)
    grows := fun a hx ↦ ha.grow a (h.grows a hx)
    rest := (ha.scalarFrame_eq (by rfl)).trans h.rest }
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl
    · exact (ha.read (n := 64) (r := 5) (by simp)).trans (h.saved .rbp (by simp))
    · exact (ha.read (n := 64) (r := 12) (by simp)).trans (h.saved .r12 (by simp))
    · exact (ha.read (n := 64) (r := 13) (by simp)).trans (h.saved .r13 (by simp))
    · exact (ha.read (n := 64) (r := 15) (by simp)).trans (h.saved .r15 (by simp))
  · have hz := hslot 0 (by decide)
    simp only [BitVec.sub_zero] at hz
    exact hz.trans h.returnSlot
  · intro c hc x hcover
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl <;> try exact hcover.elim
    obtain ⟨i, hi, rfl⟩ := hcover
    refine ⟨Stack.region initial frameBytes, by simp [writeRegions], ?_⟩
    rw [show (32 : BitVec 64) = BitVec.ofNat 64 32 from rfl,
      frame_offset initial (by decide : 32 ≤ 296), BitVec.add_assoc, ← BitVec.ofNat_add]
    exact hp.frameContains (by omega)


 theorem full_reset_call [Bindings] {boundary : ReturnBoundary}
    {state : Incremental.State} {initial s : RamState}
    (hp : CallPre boundary .sha256 true state initial true true)
    (hb : ¬ InProgram boundary.rip)
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s)
    (hf : BodyFrame .sha256 initial s true) (hip : s.RIP = 0x1064be) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      (callEffect (fun _ ↦ 0x106a70) 0x1064c4 s).Holds s t := by
  let pre := fun t ↦ BodyFrame .sha256 initial t true ∧ t.RIP = 0x1064be ∧
    CodeIn Extracted.programImage t
  have hpush (t : RamState) (h : pre t) : pushAddr t = initial.regValue .rsp - 32 := by
    change t.regValue .rsp - 8 = _
    rw [h.1.stack, BitVec.sub_sub]
    rfl
  have hw : ∀ t, pre t → ∀ i < 8, ∃ region ∈ #v[Stack.region initial frameBytes],
      region.Contains (pushAddr t + BitVec.ofNat 64 i).toNat := by
    intro t h i hi
    refine ⟨Stack.region initial frameBytes, by simp, ?_⟩
    rw [hpush t h]
    exact stack_sub_contains (offset := 32) hp.stack (by decide) (by omega)
  have ha : ∀ t, pre t → ∀ region ∈ #v[Stack.region initial frameBytes],
      region.Avoids InPageTables := by
    intro t h region hm
    have he : region = Stack.region initial frameBytes := by simpa using hm
    subst region
    exact fun a hin ht ↦ hp.stackAvoid a hin (.inr ht)
  have htarget (t : RamState) (h : pre t) :
      callMemPtr 0x1064be (.rip 0xf9cbc) t = 0x106a70 := by
    exact Memcpy.memcpyPointer_read (fun a b hm ↦ (h.2.2 (a, b) hm).2)
  have hs := call_m64_rip_effect_step_of_readable
    (p := 0x1064be) (fun _ ↦ #v[Stack.region initial frameBytes]) hw ha 0xf9cbc
    (by
      intro t h
      refine ⟨h.2.1, ?_⟩
      rw [hpush t h, show (32 : BitVec 64) = BitVec.ofNat 64 32 from rfl,
        frame_offset initial (by decide : 32 ≤ 296)]
      exact h.1.toSavedFrame.readable (readable_slice hp.frameRead 264 8 (by decide)))
    (by
      intro t h
      rw [hpush t h, show (32 : BitVec 64) = BitVec.ofNat 64 32 from rfl,
        stack_sub_toNat hp.stack.2.2.1 (by decide : 32 ≤ frameBytes)]
      have ha : (initial.regValue .rsp).toNat % 16 = 8 := hp.stack.2.2.2
      have hb : 296 ≤ (initial.regValue .rsp).toNat := hp.stack.2.2.1
      omega)
    (by
      intro t h
      exact Memcpy.memcpyPointer_readable (fun a b hm ↦ (h.2.2 (a, b) hm).2))
    (by intro t h; rw [htarget t h]; decide)
  have hpre : pre s := ⟨hf, hip, hc⟩
  have hcode : ∀ x ∈ codeRange 0x1064be (encodeCallM64 (.rip 0xf9cbc)),
      x ∈ Extracted.programImage := by
    intro x hx
    obtain ⟨i, rfl⟩ := (mem_codeRange_iff _ _ _).mp hx
    exact imageSections_mem_toCodeMap_of_fetchByte
      ((by decide +kernel : ∀ i : Fin (encodeCallM64 (.rip 0xf9cbc)).length,
        Extracted.programSections.fetchByte (0x1064be + BitVec.ofNat 64 i.val) =
          some (encodeCallM64 (.rip 0xf9cbc))[i.val]) i)
  obtain ⟨t, ht, hrt, he⟩ := hs.advances hr (hc.mono hcode) hpre (by
    change callMemPtr 0x1064be (.rip 0xf9cbc) s ≠ boundary.rip
    rw [htarget s hpre]
    exact fun he ↦ hb (he ▸ Permutation.inProgram_text_offset 0x6a70 (by decide +kernel)))
  have hav : (callEffect (callMemPtr 0x1064be (.rip 0xf9cbc)) (0x1064be + 6) s).Avoids
      Extracted.programImage := by
    intro x hx c hm hcover
    simp only [callEffect, pushEffect_components, List.mem_cons, List.not_mem_nil,
      or_false] at hm
    rcases hm with rfl | rfl | rfl <;> try exact hcover
    obtain ⟨i, hi, heq⟩ := hcover
    obtain ⟨region, hm, hin⟩ := hw s hpre i hi
    have he : region = Stack.region initial frameBytes := by simpa using hm
    subst region
    exact hp.stackAvoid x.1 (heq ▸ hin) (.inl ⟨x.2, hx⟩)
  refine ⟨t, ht, hrt, he.codeIn hav hc, ?_⟩
  exact ⟨(he.rip.trans (htarget s hpre)), he.writes, he.flags, he.agrees⟩


theorem full_finish_reset_advance [bindings : Bindings] (hstride : UnitStringStride bindings)
    {boundary : ReturnBoundary} {state : Incremental.State} {initial : RamState}
    (hp : CallPre boundary .sha256 true state initial true true)
    (hb : ¬ InProgram boundary.rip)
    (hinside : initial.regValue .rsp - 32 ≠ boundary.rsp) :
    AdvanceTriple boundary (56 + Memcpy.memcpy200Steps (initial.regValue .rsi))
      (Permuted .sha256 true state initial · true true) Extracted.programImage
      (fun _ t ↦ CallResult .sha256 true state initial t true true) := by
  intro s hs hc h
  obtain ⟨a, hsa, hra, hca, hf, hip, hd, hsrc, hlen, hbytes⟩ :=
    full_output_advance hp hb s hs hc h
  obtain ⟨b, hab, hrb, hcb, he⟩ := full_reset_call hp hb hra hca hf hip
  have hpush : pushAddr a = initial.regValue .rsp - 32 := by
    change a.regValue .rsp - 8 = _
    rw [hf.stack, BitVec.sub_sub]
    rfl
  have ha : AgreesExcept [.reg 4, .mem (initial.regValue .rsp - 32) 8, .rip] a b := by
    simpa only [callEffect, pushEffect_components, hpush] using he.agrees
  have hbf := hf.toSavedFrame.after_full_call hp ha
  have hsp : stackPtr b = initial.regValue .rsp - 32 := he.writes.1.trans hpush
  have htop : stackTop b = 0x1064c4 := (callEffect_stack he).1
  have hread (r : BitVec 5) (hr : r ≠ 4) :
      (Operand.reg r : Operand 64).read b = (Operand.reg r : Operand 64).read a :=
    ha.read (by simpa using hr)
  have bd := (hread 7 (by decide)).trans hd
  have bs := (hread 6 (by decide)).trans hsrc
  have bl := (hread 2 (by decide)).trans hlen
  have hbpre : Memcpy.Pre boundary b 200 false := by
    refine {
      rip := he.rip
      length := bl
      aligned := trivial
      direction := directionFlagUnset_of_fixedPart hbf.rest hp.direction
      source := ?_
      destination := ?_
      separate := ?_
      tables := ?_
      program := ?_
      stack := ?_
      returnLow := ?_
      disjoint := ?_
      inside := hsp ▸ hinside
      afterReturn := .inr ?_ }
    · rw [bs]
      exact hbf.readable (by simpa only [BitVec.add_zero] using
        (readable_slice hp.stateRead 0 200 (by decide)))
    · rw [bd]; exact hbf.readable hp.outputRead
    · rw [bs, bd]; exact hp.full_memcpy_separate
    · rw [bd]
      intro x hx ht
      obtain ⟨i, hi, rfl⟩ := region_contains_offset hx
      exact hp.outputAvoid i hi (.inr ht)
    · rw [bd]
      intro x hx ht
      obtain ⟨i, hi, rfl⟩ := region_contains_offset hx
      exact hp.outputAvoid i hi (.inl ht)
    · rw [hsp, show (32 : BitVec 64) = BitVec.ofNat 64 32 from rfl,
        frame_offset initial (by decide : 32 ≤ 296)]
      exact hbf.readable (readable_slice hp.frameRead 264 8 (by decide))
    · rw [htop]; decide
    · rw [bd, hsp]
      intro i hi j hj heq
      apply hp.outputStack i hi (264 + j) (by omega)
      rw [show (32 : BitVec 64) = BitVec.ofNat 64 32 from rfl,
        frame_offset initial (by decide : 32 ≤ 296), BitVec.add_assoc,
        ← BitVec.ofNat_add] at heq
      exact heq
    · rw [hsp]
      have hn : initial.regValue .rsp - 32 + 8 = initial.regValue .rsp - 24 := by
        simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
      rw [hn]; exact hp.boundary
  obtain ⟨c, hbc, done⟩ := Memcpy.memcpy200_steps hstride boundary b hrb hcb hbpre
  have hmc : AgreesExcept (Memcpy.clobbers (initial.regValue .rsi) 200) b c :=
    bd ▸ done.agrees
  have hcf : BodyFrame .sha256 initial c true := {
    toSavedFrame := hbf.after_memcpy_frame hp hmc
    stack := by
      change stackPtr c = _
      rw [done.rsp, hsp]
      simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]; rfl
    stateSaved := (hmc.read (n := 64) (r := 3) (by simp [Memcpy.clobbers])).trans
      ((hread 3 (by decide)).trans hf.stateSaved)
    output := (hmc.read (n := 64) (r := 14) (by simp [Memcpy.clobbers])).trans
      ((hread 14 (by decide)).trans hf.output) }
  have hout : ∀ i : Fin (Variant.digestBytes .sha256 true),
      c.external[initial.regValue .rsi + BitVec.ofNat 64 i.val]? =
        some (digest .sha256 state true true)[i] := by
    intro i
    have hcopy := done.copy i.val i.isLt
    rw [bd, bs] at hcopy
    rw [hcopy, ha.byte]
    · have hh := hbytes i.val i.isLt
      change a.external[initial.regValue .rdi + BitVec.ofNat 64 i.val]? =
        some (digest .sha256 state true true)[i.val]! at hh
      rw [getElem!_pos (digest .sha256 state true true) i.val i.isLt] at hh
      exact hh
    · intro component hm hcover
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl <;> try exact hcover
      obtain ⟨j, hj, heq⟩ := hcover
      apply hp.stateStack i.val (by have := i.isLt; change i.val < 200 at this; omega)
        (264 + j) (by omega)
      rw [show (32 : BitVec 64) = BitVec.ofNat 64 32 from rfl,
        frame_offset initial (by decide : 32 ≤ 296), BitVec.add_assoc,
        ← BitVec.ofNat_add] at heq
      exact heq
  obtain ⟨t, htail, ht⟩ := Reset.tail_steps hstride boundary hb .sha256
    (initial.regValue .rdi) (initial.regValue .rsp) (stackTop initial) c
    done.ready done.code (hcf.reset_pre hp (done.rip.trans htop))
  refine ⟨t, ?_, ht.ready, ht.code, reset_result hp hcf hout ht⟩
  have all := hsa.trans (hab.trans (hbc.trans htail))
  rw [bd] at all
  have hn : 56 + Memcpy.memcpy200Steps (initial.regValue .rsi) =
      3 + (1 + (Memcpy.memcpy200Steps (initial.regValue .rsi) + 52)) := by omega
  rw [hn]
  exact all

end Sha3.Proofs.Finalize
