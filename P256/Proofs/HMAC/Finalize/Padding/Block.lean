import P256.Proofs.HMAC.Finalize.Padding.Block.Result

set_option autoImplicit false

namespace P256.Proofs.HMAC.Finalize.Padding

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Program.ScalarFrame (workRegion)
open P256.Proofs.Common

namespace Block

theorem pre [Bindings] (outer : Bool) {initial s : RamState} {boundary : ReturnBoundary}
    (pre : HashCalleePre initial boundary 0x100f10 168 672)
    (state : ScalarFrame.FrameState initial s 0 672 328) (rip : s.RIP = storeStart outer) :
    Pre (storeStart outer) s := by
  have writable (offset : Nat) (bound : offset + 8 ≤ 328) (aligned : offset % 8 = 0) :
      MemWritable s (rspOf s + BitVec.ofNat 64 offset) 8 := by
    change MemWritable s (stackPtr s + BitVec.ofNat 64 offset) 8
    rw [stack_address (depth := 328) state.rsp (by omega)]
    exact Program.writable_of_grow
      (Program.stack_sub_writable8 pre.stack
        (fun a ha ht => pre.avoids _ (by simp) a ha (.inr ht)) (by omega) (by omega)) state.allocated
  have code (offset : Nat) (bound : offset + 8 ≤ 328) :
      RangeApart (rspOf s + BitVec.ofNat 64 offset) 8 (storeStart outer) 96 := by
    cases outer
    · exact ScalarFrame.stack_code (stackPre pre) state (by decide) bound (codeOffset := 0x10ac) (by decide)
    · exact ScalarFrame.stack_code (stackPre pre) state (by decide) bound (codeOffset := 0x134a) (by decide)
  refine ⟨rip, ?_, ?_, ?_⟩
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact ScalarFrame.stack_readable (stackPre pre) state (by decide) (by decide)
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact writable _ (by decide) (by decide)
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals exact code _ (by decide)

theorem code (outer : Bool) {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange (storeStart outer) (bytes (storeRegister outer) (setupRegister outer))) s := by
  cases outer
  · exact programText_slice (programLoaded_codeIn loaded) 0x10ac _ (by decide) (by decide +kernel)
  · exact programText_slice (programLoaded_codeIn loaded) 0x134a _ (by decide) (by decide +kernel)

end Block

theorem block [Bindings] (outer : Bool)
    {initial s : RamState} {boundary : ReturnBoundary} {message : ByteArray}
    (pre : HashCalleePre initial boundary 0x100f10 168 672)
    (state : Padded initial s message outer)
    (rip : s.RIP = lengthStart outer) (small : message.size % 64 < 56) :
    ∃ fuel t, Advances boundary fuel s t ∧ BlockReady initial t message ∧
      t.RIP = compressionStart outer ∧ MemoryWriteFrame s t #v[scratchRegion initial] := by
  obtain ⟨n, a, ra, encoded, ripA, memoryA⟩ := Block.encode outer pre state rip
  obtain ⟨m, t, rt, ready, _, effect⟩ := Block.run (Block.storeStart outer)
    (Block.storeRegister outer) (Block.setupRegister outer)
    (by cases outer <;> simp [Block.setupRegister]) boundary (by
      intro i hi
      cases outer
      · exact boundary_ne_program pre.outerBoundary
          (by simpa only [Block.storeStart, Bool.false_eq_true, ite_false, BitVec.ofNat_add,
              BitVec.ofNat_eq_ofNat, Extracted.textAddress, ← BitVec.add_assoc, BitVec.reduceAdd] using
            inProgram_of_textOffset (0x10ac+i) (by omega))
      · exact boundary_ne_program pre.outerBoundary
          (by simpa only [Block.storeStart, ite_true, BitVec.ofNat_add,
              BitVec.ofNat_eq_ofNat, Extracted.textAddress, ← BitVec.add_assoc, BitVec.reduceAdd] using
            inProgram_of_textOffset (0x134a+i) (by omega)))
    a (readyToStep encoded.machine encoded.bindingsSupported) (Block.code outer encoded.loaded)
    (Block.pre outer pre encoded.toFrameState ripA)
  obtain ⟨result, frame⟩ := Block.result outer pre encoded ready effect small
  refine ⟨n+m, t, ra.trans rt, result, ?_, ?_⟩
  · cases outer <;> exact effect.rip
  · intro address apart
    rw [frame address apart, memoryA]

end P256.Proofs.HMAC.Finalize.Padding
