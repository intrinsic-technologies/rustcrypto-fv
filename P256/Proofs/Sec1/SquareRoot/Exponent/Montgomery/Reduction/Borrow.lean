import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Reduction.Borrow.Result

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Montgomery.Reduction

open P256.Proofs.Program
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem borrow_correct [Bindings] {entry : BitVec 64} {boundary : ReturnBoundary}
    {s : RamState} {a p : P256.Proofs.SecretKeyFromBytes.Scalar.Limbs} {high : BitVec 64} (he : Entry entry)
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (hout : ¬ InProgram boundary.rip)
    (memory : MemoryPre s) (rip : s.RIP = entry + 0x430#64) (input : Input s a high)
    (modulus : Modulus s p) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP = entry + 0x509#64 ∧ Input t a high ∧
      Difference t (subRaw a p).1 (subRaw a p).2 ∧ MemoryPre t ∧
      AgreesExcept (scratchComponents s) s t ∧
      stackPtr t = stackPtr s ∧ t.regValue .rdi = s.regValue .rdi := by
  have next1 (offset : Nat) (_ : 0 < offset) (h : offset ≤ 54) :
      (entry+0x430#64)+BitVec.ofNat 64 offset ≠ boundary.rip := by
    have hn := instruction_ne_boundary he hout (0x430+offset) (by omega)
    simpa only [BitVec.ofNat_add, ← BitVec.add_assoc] using hn
  have code1 := code_slice he loaded 0x430 borrowLowBytes (by decide) (by decide +kernel)
  have pre1 : s.RIP = entry+0x430#64 ∧ MemoryPre s ∧
      RangeApart (stackPtr s+8#64) 8 (entry+0x430#64) 54 :=
    ⟨rip, memory, memory.scratch_apart he 8 8 0x430 54 (by decide) (by decide)⟩
  obtain ⟨fuel1, s1, run1, ready1, _, effect1⟩ :=
    borrow_low_correct (entry+0x430#64) boundary next1 s ready code1 pre1
  have frame1 := borrowLow_frame effect1
  have scratch1 := borrow_frame frame1
  have memory1 := memory.of_scratch scratch1
  have loaded1 := memory.loaded (scratch1.mono (fun _ hc => List.mem_append_left _ hc)) loaded
  have rip1 : s1.RIP = entry+0x466#64 := by
    simpa only [borrowLowEffect, BitVec.add_assoc, BitVec.reduceAdd] using effect1.rip
  have next2 (offset : Nat) (_ : 0 < offset) (h : offset ≤ 56) :
      (entry+0x466#64)+BitVec.ofNat 64 offset ≠ boundary.rip := by
    have hn := instruction_ne_boundary he hout (0x466+offset) (by omega)
    simpa only [BitVec.ofNat_add, ← BitVec.add_assoc] using hn
  have code2 := code_slice he loaded1 0x466 borrowMiddleBytes (by decide) (by decide +kernel)
  have pre2 : s1.RIP = entry+0x466#64 ∧ MemoryPre s1 ∧
      RangeApart (stackPtr s1+8#64) 8 (entry+0x466#64) 56 :=
    ⟨rip1, memory1, memory1.scratch_apart he 8 8 0x466 56 (by decide) (by decide)⟩
  obtain ⟨fuel2, s2, run2, ready2, _, effect2⟩ :=
    borrow_middle_correct (entry+0x466#64) boundary next2 s1 ready1 code2 pre2
  have frame2 := borrowMiddle_frame effect2
  have scratch2 := borrow_frame frame2
  have memory2 := memory1.of_scratch scratch2
  have loaded2 := memory1.loaded (scratch2.mono (fun _ hc => List.mem_append_left _ hc)) loaded1
  have rip2 : s2.RIP = entry+0x49e#64 := by
    simpa only [borrowMiddleEffect, BitVec.add_assoc, BitVec.reduceAdd] using effect2.rip
  have next3 (offset : Nat) (_ : 0 < offset) (h : offset ≤ 56) :
      (entry+0x49e#64)+BitVec.ofNat 64 offset ≠ boundary.rip := by
    have hn := instruction_ne_boundary he hout (0x49e+offset) (by omega)
    simpa only [BitVec.ofNat_add, ← BitVec.add_assoc] using hn
  have code3 := code_slice he loaded2 0x49e borrowHighBytes (by decide) (by decide +kernel)
  have pre3 : s2.RIP = entry+0x49e#64 ∧ MemoryPre s2 ∧
      RangeApart (stackPtr s2+8#64) 8 (entry+0x49e#64) 56 :=
    ⟨rip2, memory2, memory2.scratch_apart he 8 8 0x49e 56 (by decide) (by decide)⟩
  obtain ⟨fuel3, s3, run3, ready3, _, effect3⟩ :=
    borrow_high_correct (entry+0x49e#64) boundary next3 s2 ready2 code3 pre3
  have frame3 := borrowHigh_frame effect3
  have scratch3 := borrow_frame frame3
  have memory3 := memory2.of_scratch scratch3
  have loaded3 := memory2.loaded (scratch3.mono (fun _ hc => List.mem_append_left _ hc)) loaded2
  have rip3 : s3.RIP = entry+0x4d6#64 := by
    simpa only [borrowHighEffect, BitVec.add_assoc, BitVec.reduceAdd] using effect3.rip
  have next4 (offset : Nat) (_ : 0 < offset) (h : offset ≤ 51) :
      (entry+0x4d6#64)+BitVec.ofNat 64 offset ≠ boundary.rip := by
    have hn := instruction_ne_boundary he hout (0x4d6+offset) (by omega)
    simpa only [BitVec.ofNat_add, ← BitVec.add_assoc] using hn
  have code4 := code_slice he loaded3 0x4d6 borrowTopBytes (by decide) (by decide +kernel)
  have pre4 : s3.RIP = entry+0x4d6#64 ∧ MemoryPre s3 ∧
      RangeApart (stackPtr s3+8#64) 8 (entry+0x4d6#64) 51 :=
    ⟨rip3, memory3, memory3.scratch_apart he 8 8 0x4d6 51 (by decide) (by decide)⟩
  obtain ⟨fuel4, s4, run4, ready4, _, effect4⟩ :=
    borrow_top_correct (entry+0x4d6#64) boundary next4 s3 ready3 code4 pre4
  have frame4 := borrowTop_frame effect4
  have scratch4 := borrow_frame frame4
  have memory4 := memory3.of_scratch scratch4
  have loaded4 := memory3.loaded (scratch4.mono (fun _ hc => List.mem_append_left _ hc)) loaded3
  have rip4 : s4.RIP = entry+0x509#64 := by
    simpa only [borrowTopEffect, BitVec.add_assoc, BitVec.reduceAdd] using effect4.rip
  have frame := borrow_trans (borrow_trans (borrow_trans frame1 frame2) frame3) frame4
  have scratch := borrow_frame frame
  exact ⟨fuel1+fuel2+fuel3+fuel4, s4, ((run1.trans run2).trans run3).trans run4,
    ready4, loaded4, rip4, borrow_input frame input,
    borrow_difference input modulus effect1 effect2 effect3 effect4, memory4, scratch,
    scratch_rsp scratch, scratch_rdi scratch⟩

end P256.Proofs.Sec1.SquareRoot.Montgomery.Reduction
