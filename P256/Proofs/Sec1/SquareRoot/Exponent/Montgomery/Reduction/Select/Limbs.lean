import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Reduction.Select.Words
import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Reduction.Stores

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Montgomery.Reduction

open P256.Proofs.Program
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def maskComponents (s : RamState) (dst orig : BitVec 5) : List Component :=
  [.reg dst, .reg orig, .flags, .rip, .mem (stackPtr s+8) 1]

theorem maskWord_frame {s t : RamState} {p : BitVec 64} {len : Nat} {dst orig diff : BitVec 5}
    (h : (maskWordEffect p len dst orig diff s).Holds s t) :
    AgreesExcept (maskComponents s dst orig) s t := by
  exact h.agrees.mono (by simp [maskWordEffect, maskComponents, Effect.components])

theorem mask_wide {s t : RamState} {dst orig : BitVec 5}
    (h : AgreesExcept (maskComponents s dst orig) s t)
    (hd : .reg dst ∈ scratchComponents s) (ho : .reg orig ∈ scratchComponents s) :
    AgreesExcept (scratchComponents s) s t := by
  apply h.widen
  · intro c hc hm
    simp only [maskComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    · exact hd
    · exact ho
    · simp [scratchComponents]
    · simp [scratchComponents]
    · simp [Component.isMem] at hm
  · intro address c hc hv
    refine ⟨.mem (stackPtr s) 112, by simp [scratchComponents], ?_⟩
    simp only [maskComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl
    all_goals try exact hv.elim
    exact scratch_covered (offset := 8) (by decide) hv

theorem mask_word_run [Bindings] {entry : BitVec 64} {boundary : ReturnBoundary} {s : RamState}
    {offset len : Nat} {dst orig diff : BitVec 5} {bytes : List UInt8}
    (he : Entry entry) (ready : ReadyToStep s) (loaded : ProgramLoaded s) (memory : MemoryPre s)
    (rip : s.RIP = entry+BitVec.ofNat 64 offset)
    (hd : .reg dst ∈ scratchComponents s) (ho : .reg orig ∈ scratchComponents s)
    (bound : offset + bytes.length ≤ 1469) (lenBound : offset+len ≤ 1469)
    (hbytes : Extracted.textBytes.toListFrom (0x145e0+offset) bytes.length = bytes)
    (block : AdvanceTriple boundary (MaskWordPre (entry+BitVec.ofNat 64 offset) len)
      (codeRange (entry+BitVec.ofNat 64 offset) bytes)
      (Effect.post (maskWordEffect (entry+BitVec.ofNat 64 offset) len dst orig diff))) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧ MemoryPre t ∧
      t.RIP = entry+BitVec.ofNat 64 (offset+len) ∧
      (maskWordEffect (entry+BitVec.ofNat 64 offset) len dst orig diff s).Holds s t := by
  obtain ⟨fuel,t,run,ready',_,effect⟩ := block s ready (code_slice he loaded offset bytes bound hbytes)
    ⟨rip, memory.scratch 8 1 (by decide) (by decide) (by decide),
      memory.scratch_apart he 8 1 offset len (by decide) lenBound⟩
  have wide := mask_wide (maskWord_frame effect) hd ho
  refine ⟨fuel,t,run,ready',memory.loaded (wide.mono (fun _ hc => List.mem_append_left _ hc)) loaded,
    memory.of_scratch wide, ?_,effect⟩
  have hh := effect.rip
  change t.RIP = (entry+BitVec.ofNat 64 offset)+BitVec.ofNat 64 len at hh
  simpa only [BitVec.add_assoc, BitVec.ofNat_add] using hh

set_option maxHeartbeats 800000 in
set_option maxRecDepth 2048 in
theorem select_limbs_correct [Bindings] {entry : BitVec 64} {boundary : ReturnBoundary}
    {s : RamState} {a r : P256.Proofs.SecretKeyFromBytes.Scalar.Limbs} {high b : BitVec 64} {q : BitVec 8}
    (he : Entry entry) (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (hout : ¬ InProgram boundary.rip) (memory : MemoryPre s)
    (rip : s.RIP = entry+0x543#64) (input : Input s a high) (difference : Difference s r b)
    (byte : (Operand.reg 5 : Operand 8).read s = q) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP = entry+0x59c#64 ∧ StoreInput t (selectLimbs a r (q.setWidth 64)) ∧
      AgreesExcept (scratchComponents s) s t := by
  obtain ⟨n1,s1,run1,ready1,loaded1,memory1,rip1,effect1⟩ :=
    mask_word_run (offset := 0x543) (len := 23) (dst := 10) (orig := 1) (diff := 8)
      (bytes := maskLowBytes) he ready loaded memory rip
      (by simp [scratchComponents]) (by simp [scratchComponents])
      (by decide) (by decide) (by decide +kernel)
      (mask_low_correct (entry+0x543#64) boundary (by
        intro offset hpos hle
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]
        exact instruction_ne_boundary he hout (0x543+offset) (by omega)))
  have frame1 := maskWord_frame effect1
  have wide1 := mask_wide frame1 (by simp [scratchComponents]) (by simp [scratchComponents])
  have read1 (reg : BitVec 5) (hreg : .reg reg ∉ maskComponents s 10 1) :
      (Operand.reg reg : Operand 64).read s1 = (Operand.reg reg : Operand 64).read s :=
    frame1.read hreg
  have limb1 : (Operand.reg 10 : Operand 64).read s1 =
      selectWord a.l0 r.l0 (q.setWidth 64) := by
    have hh := effect1.writes.1
    change (Operand.reg 10 : Operand 64).read s1 =
      selectWord ((Operand.reg 1 : Operand 64).read s)
        ((Operand.reg 8 : Operand 64).read s)
        (((Operand.reg 5 : Operand 8).read s).setWidth 64) at hh
    simpa only [input.l0, difference.l0, byte] using hh
  obtain ⟨n2,s2,run2,ready2,loaded2,memory2,rip2,effect2⟩ :=
    mask_word_run (offset := 0x55a) (len := 22) (dst := 1) (orig := 6) (diff := 9)
      (bytes := maskMiddleLowBytes) he ready1 loaded1 memory1 rip1
      (by simp [scratchComponents]) (by simp [scratchComponents])
      (by decide) (by decide) (by decide +kernel)
      (mask_middleLow_correct (entry+0x55a#64) boundary (by
        intro offset hpos hle
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]
        exact instruction_ne_boundary he hout (0x55a+offset) (by omega)))
  have frame2 := maskWord_frame effect2
  have wide2 := mask_wide frame2 (by simp [scratchComponents]) (by simp [scratchComponents])
  have frames2 := frame1.trans frame2
  have total2 := scratch_trans wide1 wide2
  have read2 (reg : BitVec 5) (hreg : .reg reg ∉ (maskComponents s 10 1 ++ maskComponents s1 1 6)) :
      (Operand.reg reg : Operand 64).read s2 = (Operand.reg reg : Operand 64).read s :=
    frames2.read hreg
  have limb2 : (Operand.reg 1 : Operand 64).read s2 =
      selectWord a.l1 r.l1 (q.setWidth 64) := by
    have hh := effect2.writes.1
    change (Operand.reg 1 : Operand 64).read s2 =
      selectWord ((Operand.reg 6 : Operand 64).read s1)
        ((Operand.reg 9 : Operand 64).read s1)
        (((Operand.reg 5 : Operand 8).read s1).setWidth 64) at hh
    have bp : (Operand.reg 5 : Operand 8).read s1 = q := by
      change ((Operand.reg 5 : Operand 64).read s1).setWidth 8 = q
      rw [read1 5 (by simp [maskComponents])]
      exact byte
    rw [read1 6 (by simp [maskComponents]), read1 9 (by simp [maskComponents]),
      input.l1, difference.l1, bp] at hh
    exact hh
  obtain ⟨n3,s3,run3,ready3,loaded3,memory3,rip3,effect3⟩ :=
    mask_word_run (offset := 0x570) (len := 22) (dst := 6) (orig := 0) (diff := 11)
      (bytes := maskMiddleHighBytes) he ready2 loaded2 memory2 rip2
      (by simp [scratchComponents]) (by simp [scratchComponents])
      (by decide) (by decide) (by decide +kernel)
      (mask_middleHigh_correct (entry+0x570#64) boundary (by
        intro offset hpos hle
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]
        exact instruction_ne_boundary he hout (0x570+offset) (by omega)))
  have frame3 := maskWord_frame effect3
  have wide3 := mask_wide frame3 (by simp [scratchComponents]) (by simp [scratchComponents])
  have frames3 := frames2.trans frame3
  have total3 := scratch_trans total2 wide3
  have read3 (reg : BitVec 5) (hreg : .reg reg ∉ (maskComponents s 10 1 ++ maskComponents s1 1 6 ++ maskComponents s2 6 0)) :
      (Operand.reg reg : Operand 64).read s3 = (Operand.reg reg : Operand 64).read s :=
    frames3.read hreg
  have limb3 : (Operand.reg 6 : Operand 64).read s3 =
      selectWord a.l2 r.l2 (q.setWidth 64) := by
    have hh := effect3.writes.1
    change (Operand.reg 6 : Operand 64).read s3 =
      selectWord ((Operand.reg 0 : Operand 64).read s2)
        ((Operand.reg 11 : Operand 64).read s2)
        (((Operand.reg 5 : Operand 8).read s2).setWidth 64) at hh
    have bp : (Operand.reg 5 : Operand 8).read s2 = q := by
      change ((Operand.reg 5 : Operand 64).read s2).setWidth 8 = q
      rw [read2 5 (by simp [maskComponents])]
      exact byte
    rw [read2 0 (by simp [maskComponents]), read2 11 (by simp [maskComponents]),
      input.l2, difference.l2, bp] at hh
    exact hh
  obtain ⟨n4,s4,run4,ready4,loaded4,memory4,rip4,effect4⟩ :=
    mask_word_run (offset := 0x586) (len := 22) (dst := 0) (orig := 2) (diff := 14)
      (bytes := maskHighBytes) he ready3 loaded3 memory3 rip3
      (by simp [scratchComponents]) (by simp [scratchComponents])
      (by decide) (by decide) (by decide +kernel)
      (mask_high_correct (entry+0x586#64) boundary (by
        intro offset hpos hle
        rw [BitVec.add_assoc, ← BitVec.ofNat_add]
        exact instruction_ne_boundary he hout (0x586+offset) (by omega)))
  have frame4 := maskWord_frame effect4
  have wide4 := mask_wide frame4 (by simp [scratchComponents]) (by simp [scratchComponents])
  have total4 := scratch_trans total3 wide4
  have limb4 : (Operand.reg 0 : Operand 64).read s4 =
      selectWord a.l3 r.l3 (q.setWidth 64) := by
    have hh := effect4.writes.1
    change (Operand.reg 0 : Operand 64).read s4 =
      selectWord ((Operand.reg 2 : Operand 64).read s3)
        ((Operand.reg 14 : Operand 64).read s3)
        (((Operand.reg 5 : Operand 8).read s3).setWidth 64) at hh
    have bp : (Operand.reg 5 : Operand 8).read s3 = q := by
      change ((Operand.reg 5 : Operand 64).read s3).setWidth 8 = q
      rw [read3 5 (by simp [maskComponents])]
      exact byte
    rw [read3 2 (by simp [maskComponents]), read3 14 (by simp [maskComponents]),
      input.l3, difference.l3, bp] at hh
    exact hh
  refine ⟨n1+n2+n3+n4,s4,((run1.trans run2).trans run3).trans run4,
    ready4,loaded4,rip4,?_,total4⟩
  refine ⟨?_,?_,?_,limb4⟩
  · exact ((frame2.trans frame3).trans frame4).read (r := 10) (n := 64)
      (by simp [maskComponents]) |>.trans limb1
  · exact (frame3.trans frame4).read (r := 1) (n := 64)
      (by simp [maskComponents]) |>.trans limb2
  · exact frame4.read (r := 6) (n := 64) (by simp [maskComponents]) |>.trans limb3

end P256.Proofs.Sec1.SquareRoot.Montgomery.Reduction
