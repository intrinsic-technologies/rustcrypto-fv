import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Reduction.Common
import P256.Proofs.Common.Encoding.Parser.ByteStore
import P256.Proofs.Common.Instructions.ByteLogic.AndReg
import P256.Proofs.Common.Instructions.Setb.Triple
import P256.Proofs.Common.Instructions.ByteOps.Effects
import X86Proofs.Instructions.Test.Generated.RR.Triple

set_option autoImplicit false

open P256.Proofs.Common.Instructions (mov_m8_r8_effect_step)
open P256.Proofs.Common.Instructions.ByteLogic (andR8R8Effect and_r8_r8_rex_effect_step)
open P256.Proofs.Common.Instructions.Setb (SupportedOpcode setccR8Effect setcc_r8_rex_effect_step)

namespace P256.Proofs.Sec1.SquareRoot.Montgomery.Reduction

open P256.Proofs.Program
open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Proofs.SecretKeyFromBytes.Scalar
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

def prefixComponents (s : RamState) : List Component :=
  [.reg 5, .flags, .rip, .mem (stackPtr s + 8) 1]

theorem prefix_frame {s t : RamState} (h : AgreesExcept (prefixComponents s) s t) :
    AgreesExcept (scratchComponents s) s t := by
  apply h.widen
  · intro c hc hm
    simp only [prefixComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    all_goals simp_all [scratchComponents, Component.isMem]
  · intro address c hc hv
    refine ⟨.mem (stackPtr s) 112, by simp [scratchComponents], ?_⟩
    simp only [prefixComponents, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    all_goals try exact hv.elim
    exact scratch_covered (offset := 8) (by decide) hv

set_option maxHeartbeats 800000 in
set_option maxRecDepth 2048 in
theorem prefix_correct [Bindings] {entry : BitVec 64} {boundary : ReturnBoundary}
    {s : RamState} {high b : BitVec 64} (he : Entry entry)
    (ready : ReadyToStep s) (loaded : ProgramLoaded s) (hout : ¬ InProgram boundary.rip)
    (memory : MemoryPre s) (rip : s.RIP = entry + 0x509#64)
    (hi : (Operand.reg 15 : Operand 64).read s = high)
    (negBorrow : (Operand.reg 13 : Operand 64).read s = -b) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP = entry + 0x518#64 ∧
      (Operand.reg 5 : Operand 8).read t =
        (if high = 0 then 1 else 0) &&& (-b).setWidth 8 ∧
      AgreesExcept (prefixComponents s) s t := by
  obtain ⟨s1, run1, ready1, h1⟩ :=
    (test_r64_r64_effect_step (entry+0x509) 0x4d 0xff (by simp [RexWPrefix]) rfl).advances (boundary := boundary)
      ready (code_slice he loaded 0x509 [0x4d,0x85,0xff] (by decide) (by decide +kernel)) rip
      (by simpa only [testR64R64Effect, setccR8Effect, andR8R8Effect, storeEffect, AddrMode.tail, Disp.bytes, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceDiv, immBytes_length, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using instruction_ne_boundary he hout 0x50c (by decide))
  change (testR64R64Effect (entry+0x509) 15 15 s).Holds s s1 at h1
  have f1 : AgreesExcept [.flags, .rip] s s1 := h1.agrees
  have wide1 : AgreesExcept (components s) s s1 := f1.mono (by simp [components, scratchComponents])
  have loaded1 := memory.loaded wide1 loaded
  have hz : (StatusFlags.ofRFLAGS s1.RFLAGS).ZF = (high == 0) := by
    have hh := h1.flags.2.2.2.1
    simpa only [testR64R64Effect, testFlags, hi, BitVec.and_self, FlagAllows] using hh
  obtain ⟨s2, run2, ready2, h2⟩ :=
    (setcc_r8_rex_effect_step (entry+0x50c) 0x40 0x94 0xc5 (by simp [RexPrefix])
      (by simp [SupportedOpcode]) rfl).advances (boundary := boundary) ready1
      (code_slice he loaded1 0x50c [0x40,0x0f,0x94,0xc5] (by decide) (by decide +kernel))
      (by simpa only [testR64R64Effect, setccR8Effect, andR8R8Effect, storeEffect, AddrMode.tail, Disp.bytes, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceDiv, immBytes_length, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using h1.rip)
      (by simpa only [testR64R64Effect, setccR8Effect, andR8R8Effect, storeEffect, AddrMode.tail, Disp.bytes, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceDiv, immBytes_length, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using instruction_ne_boundary he hout 0x510 (by decide))
  change (setccR8Effect (entry+0x50c) 4 5 4 s1).Holds s1 s2 at h2
  have f2 : AgreesExcept [.reg 5, .rip] s1 s2 := h2.agrees
  have fa2 := f1.trans f2
  have wide2 : AgreesExcept (components s) s s2 := fa2.mono (by simp [components, scratchComponents])
  have loaded2 := memory.loaded wide2 loaded
  have byte2 : (Operand.reg 5 : Operand 8).read s2 = if high = 0 then 1 else 0 := by
    have hw := congrArg (BitVec.setWidth 8) h2.writes
    rw [P256.Proofs.Common.Instructions.ByteOps.ByteOps.mergeGPR_low8] at hw
    change (Operand.reg 5 : Operand 8).read s2 = (if (StatusFlags.ofRFLAGS s1.RFLAGS).ZF then 1 else 0) at hw
    simpa only [hz, beq_iff_eq] using hw
  have borrow2 : (Operand.reg 13 : Operand 8).read s2 = (-b).setWidth 8 := by
    change ((Operand.reg 13 : Operand 64).read s2).setWidth 8 = _
    rw [fa2.read (by simp), negBorrow]
  obtain ⟨s3, run3, ready3, h3⟩ :=
    (and_r8_r8_rex_effect_step (entry+0x510) 0x44 0xed (by simp [RexPrefix]) rfl).advances (boundary := boundary)
      ready2 (code_slice he loaded2 0x510 [0x44,0x20,0xed] (by decide) (by decide +kernel))
      (by simpa only [testR64R64Effect, setccR8Effect, andR8R8Effect, storeEffect, AddrMode.tail, Disp.bytes, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceDiv, immBytes_length, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using h2.rip)
      (by simpa only [testR64R64Effect, setccR8Effect, andR8R8Effect, storeEffect, AddrMode.tail, Disp.bytes, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceDiv, immBytes_length, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using instruction_ne_boundary he hout 0x513 (by decide))
  change (andR8R8Effect (entry+0x510) 5 13 s2).Holds s2 s3 at h3
  have f3 : AgreesExcept [.reg 5, .flags, .rip] s2 s3 := h3.agrees
  have fa3 := fa2.trans f3
  have wide3 : AgreesExcept (components s) s s3 := fa3.mono (by simp [components, scratchComponents])
  have loaded3 := memory.loaded wide3 loaded
  have byte3 : (Operand.reg 5 : Operand 8).read s3 =
      (if high = 0 then 1 else 0) &&& (-b).setWidth 8 := by
    have hw := congrArg (BitVec.setWidth 8) h3.writes
    rw [P256.Proofs.Common.Instructions.ByteOps.ByteOps.mergeGPR_low8] at hw
    exact hw.trans (by rw [byte2, borrow2])
  have rsp3 : stackPtr s3 = stackPtr s := fa3.read (r := 4) (n := 64) (by simp)
  obtain ⟨s4, run4, ready4, h4⟩ :=
    (mov_m8_r8_effect_step (entry+0x513) 0x40 (by simp [RexPrefix]) 5
      (.sib 4 none 0 (.d8 8)) (by decide +kernel) rfl rfl).advances (boundary := boundary) ready3
      (code_slice he loaded3 0x513 [0x40,0x88,0x6c,0x24,8] (by decide) (by decide +kernel))
      ⟨by simpa only [testR64R64Effect, setccR8Effect, andR8R8Effect, storeEffect, AddrMode.tail, Disp.bytes, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceDiv, immBytes_length, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using h3.rip,
        by change MemWritable s3 (stackPtr s3+8) 1
           exact (memory.of_components wide3).scratch 8 1 (by decide) (by decide) (by decide),
        by change RangeApart (stackPtr s3+8) 1 (entry+0x513) 5
           rw [rsp3]
           exact memory.scratch_apart he 8 1 0x513 5 (by decide) (by decide)⟩
      (by simpa only [testR64R64Effect, setccR8Effect, andR8R8Effect, storeEffect, AddrMode.tail, Disp.bytes, List.length_cons, List.length_nil, Nat.reduceAdd, Nat.reduceDiv, immBytes_length, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using instruction_ne_boundary he hout 0x518 (by decide))
  change ({ rip := (entry+0x513)+5, writes := [⟨(Operand.mem (stackPtr s3+8) : Operand 8),
    (Operand.reg 5 : Operand 8).read s3⟩] } : Effect).Holds s3 s4 at h4
  rw [rsp3] at h4
  have f4 : AgreesExcept [.mem (stackPtr s+8) 1, .rip] s3 s4 := by simpa [Effect.components] using h4.agrees
  have frame : AgreesExcept (prefixComponents s) s s4 :=
    (fa3.trans f4).mono (by simp [prefixComponents])
  have wide4 : AgreesExcept (components s) s s4 :=
    (prefix_frame frame).mono (fun _ hc => List.mem_append_left _ hc)
  refine ⟨4, s4, ((run1.trans run2).trans run3).trans run4, ready4,
    memory.loaded wide4 loaded, ?_, ?_, frame⟩
  · simpa only [storeEffect, BitVec.add_assoc, BitVec.reduceAdd] using h4.rip
  · exact (f4.read (by simp)).trans byte3

end P256.Proofs.Sec1.SquareRoot.Montgomery.Reduction
