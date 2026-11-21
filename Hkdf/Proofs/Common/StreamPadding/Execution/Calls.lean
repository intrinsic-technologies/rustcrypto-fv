import Hkdf.Proofs.Common.StreamPadding.Execution.Geometry
import Hkdf.Proofs.Common.Memory.Fill
import Hkdf.Proofs.Common.Memory.Pointers
import Hkdf.Proofs.Common.SHA256.Correctness
import Hkdf.Proofs.Common.SHA256.Mathematics.Padding.Tail
import Hkdf.Proofs.Common.Memory

set_option autoImplicit false

namespace Hkdf.Proofs.Common.StreamPadding.Execution

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Spec.Program Hkdf.Proofs.Program Hkdf.Proofs.Common Hkdf.Proofs.Common.Machine
open Hkdf.Proofs.Common.CallFrame
open Hkdf.Proofs.Common.SHA256

private def compressionLayout (v : Variant) :
    StackCallLayout v.reserve 64 32 336 :=
  ⟨v.frame + 8, v.frame - v.scratch, v.frame - v.hash,
    by cases v <;> decide, by cases v <;> decide,
    by cases v <;> decide, by cases v <;> decide,
    by cases v <;> decide, by cases v <;> decide,
    by cases v <;> decide⟩

private def fillLayout (v : Variant) (position : Nat) (bound : position ≤ 64) :
    StackCallLayout v.reserve 0 (64-position) 0 :=
  ⟨v.frame + 8, v.frame, v.frame - (v.tail + position),
    by cases v <;> decide, by cases v <;> decide,
    by omega, by cases v <;> simp only [Variant.frame, Variant.tail] at * <;> omega,
    by omega, by cases v <;> simp only [Variant.frame, Variant.tail] at * <;> omega,
    .inl (by cases v <;> simp only [Variant.frame, Variant.tail] at * <;> omega)⟩

private def compressionPc (v : Variant) (last : Bool) : BitVec 64 :=
  v.pc (if last then .lastCall else .firstCall)

private def compressionDisp (v : Variant) (last : Bool) : BitVec 32 :=
  match v, last with
  | .key, false => 0xffff30c1
  | .key, true => 0xffff2ff7
  | .hmac, false => 0xffffb765
  | .hmac, true => 0xffffb6b3
  | .simpleInner, false => 0xffff2281
  | .simpleInner, true => 0xffff21cf
  | .simpleOuter, false => 0xffff1fe3
  | .simpleOuter, true => 0xffff1f31

private def fillDisp (v : Variant) : BitVec 32 :=
  match v with
  | .key => 0xeaec0
  | .hmac => 0xf354c
  | .simpleInner => 0xea068
  | .simpleOuter => 0xe9dca

private theorem enter [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {v : Variant} {inputBytes : Nat} {precondition : RamState → Prop} {code : CodeMap}
    {target : RamState → BitVec 64} {ret : BitVec 64}
    (pre : CalleePre initial boundary v.helperEntry inputBytes v.outputBytes v.reserve)
    (running : Running initial boundary (regions v initial) s)
    (rsp : stackPtr s = base v initial)
    (step : StepEffect precondition code (callEffect target ret))
    (instruction : CodeIn code s) (conditions : precondition s)
    (continues : target s ≠ boundary.rip) :
    ∃ c, Advances boundary 1 s c ∧ ReadyToStep c ∧
      Running initial boundary (regions v initial) c ∧
      (callEffect target ret s).Holds s c ∧
      stackPtr c = base v initial - 8 ∧
      returnBoundary c = ⟨ret, stackPtr s⟩ := by
  obtain ⟨c, execution, ready, called⟩ := step.advances
    (supportedMachine_readyToStep running.machine) instruction conditions continues
  have rwrites := call_writes v pre rsp target ret
  have runningC := running.of_agrees execution ready called.agrees
    (by
      intro component member a covered
      obtain ⟨region, hr, contains⟩ := rwrites component member a covered
      exact writes_within_regions v pre region hr a.toNat contains)
    (regions_avoids v pre) (by simp [callEffect, pushEffect_components])
  refine ⟨c, execution, ready, runningC, called, ?_, call_boundary called⟩
  exact called.writes.1.trans (by change stackPtr s - 8 = _; rw [rsp])

theorem call_local_agrees {s c : RamState} {target : RamState → BitVec 64}
    {ret : BitVec 64} (called : (callEffect target ret s).Holds s c)
    (offset len : Nat) (apart : OffsetsApart (-8) 8 (BitVec.ofNat 64 offset) len)
    (small : 8+len < 2^64) :
    (Component.mem (stackPtr s + BitVec.ofNat 64 offset) len).Agrees s c := by
  intro i hi
  apply called.agrees.memory
  intro component member covered
  simp only [callEffect, pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl
  · exact covered.elim
  · obtain ⟨j, hj, equal⟩ := covered
    exact OffsetsApart.ne apart (stackPtr s) hj hi small
      (by simpa only [pushAddr, BitVec.sub_eq_add_neg] using equal.symm)
  · exact covered.elim

theorem fill [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {inputBytes position : Nat} (v : Variant)
    (pre : CalleePre initial boundary v.helperEntry inputBytes v.outputBytes v.reserve)
    (running : Running initial boundary (regions v initial) s)
    (rsp : stackPtr s = base v initial) (bound : position ≤ 64)
    (rip : s.RIP = v.pc .fillCall)
    (destination : s.regValue .rdi = stackPtr s + BitVec.ofNat 64 (v.tail+position))
    (zero : s.regValue .rsi = 0)
    (length : s.regValue .rdx = BitVec.ofNat 64 (64-position)) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      Running initial boundary (regions v initial) t ∧ t.RIP = v.pc .branch ∧
      stackPtr t = stackPtr s ∧ PreservesABI s t ∧
      MemoryWriteFrame s t (writes v (stackPtr s)) ∧
      MemoryWriteFrame s t #v[
        ⟨(stackPtr s + BitVec.ofNat 64 (v.tail+position)).toNat,64-position⟩,
        ⟨(stackPtr s-8).toNat,8⟩] ∧
      (∀ i < 64-position,
        t.external[stackPtr s + BitVec.ofNat 64 (v.tail+position) + BitVec.ofNat 64 i]? = some 0) := by
  have pointer := Memory.memset_pointer running.loaded
  have pointerValue : callMemPtr (v.pc .fillCall) (.rip (fillDisp v)) s = 0x10dd10 := by
    cases v <;> exact pointer.2
  have step := call_m64_effect_step (v.pc .fillCall) (.rip (fillDisp v)) trivial rfl rfl
  have instruction : CodeIn
      (codeRange (v.pc .fillCall) (encodeCallM64 (.rip (fillDisp v)))) s := by
    cases v
    · exact programText_slice (programLoaded_codeIn running.loaded) 0x16472 _
        (by decide) (by decide +kernel)
    · exact programText_slice (programLoaded_codeIn running.loaded) 0xdde6 _
        (by decide) (by decide +kernel)
    · exact programText_slice (programLoaded_codeIn running.loaded) 0x172ca _
        (by decide) (by decide +kernel)
    · exact programText_slice (programLoaded_codeIn running.loaded) 0x17568 _
        (by decide) (by decide +kernel)
  have conditions : CallMemPre (v.pc .fillCall) (.rip (fillDisp v)) s := by
    refine ⟨⟨⟨rip, call_writable v pre running rsp, ?_⟩, ?_⟩, ?_⟩
    · cases v
      · exact call_codeApart .key pre rsp 0x16472 6 (by decide)
      · exact call_codeApart .hmac pre rsp 0xdde6 6 (by decide)
      · exact call_codeApart .simpleInner pre rsp 0x172ca 6 (by decide)
      · exact call_codeApart .simpleOuter pre rsp 0x17568 6 (by decide)
    · rw [pointerValue]; decide
    · cases v <;> exact pointer.1
  obtain ⟨c, callRun, readyC, runningC, called, rspC, returnC⟩ :=
    enter pre running rsp step instruction conditions
      (by rw [pointerValue]
          exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0xdd10 (by decide)))
  have outputC : c.regValue .rdi = base v initial + BitVec.ofNat 64 (v.tail+position) := by
    rw [← rsp]
    exact (called.agrees.read (n := 64) (r := 7)
      (by simp [callEffect, pushEffect_components])).trans destination
  have zeroC : c.regValue .rsi = 0 :=
    (called.agrees.read (n := 64) (r := 6)
      (by simp [callEffect, pushEffect_components])).trans zero
  have lengthC : c.regValue .rdx = BitVec.ofNat 64 (64-position) :=
    (called.agrees.read (n := 64) (r := 2)
      (by simp [callEffect, pushEffect_components])).trans length
  have callee : CalleePre c boundary 0x10dd10 0 (64-position) 0 := by
    apply callee_pre_of_stack_output pre.stride pre.stack
      (pre.avoids _ (by simp)) pre.outerBoundary runningC.machine runningC.directionFlag
      runningC.loaded runningC.allocated (fillLayout v position bound)
      (called.rip.trans pointerValue)
    · exact rspC.trans (below_address v initial 8)
    · exact outputC.trans (local_address v pre (v.tail+position)
        (by have h : v.tail+64≤v.frame := by cases v <;> decide
            omega))
    · rw [returnC]
      cases v
      · exact inProgram_of_textOffset 0x16478 (by decide)
      · exact inProgram_of_textOffset 0xddec (by decide)
      · exact inProgram_of_textOffset 0x172d0 (by decide)
      · exact inProgram_of_textOffset 0x1756e (by decide)
    · change (c.regValue .rsi).toNat + 0 < 2^32
      rw [zeroC]; decide
    · intro a ha
      change (c.regValue .rsi).toNat ≤ a.toNat ∧ a.toNat < (c.regValue .rsi).toNat+0 at ha
      omega
    · intro a ha
      change (c.regValue .rsi).toNat ≤ a ∧ a < (c.regValue .rsi).toNat+0 at ha
      omega
  obtain ⟨t, result, filled, _⟩ := Memory.memset_zero_correct callee
    (by rw [zeroC]; rfl) lengthC (by omega)
  have within := fill_within_writes v pre rspC outputC (64-position) (by omega)
  have complete := call_result callee called result running.directionFlag
  have frame := frame_mono complete.1 within
  have runningT := runningC.of_callee result (by
    intro region member a contains
    obtain ⟨outer, ho, hin⟩ := within region member a contains
    exact writes_within_regions v pre outer ho a hin)
  obtain ⟨fuel, execution⟩ := result.execution
  refine ⟨1+fuel, t, callRun.trans execution, supportedMachine_readyToStep result.machine,
    runningT, ?_, ?_, complete.2, ?_, ?_, ?_⟩
  · rw [result.rip, returnC]
    cases v <;> rfl
  · exact result.rsp.trans (congrArg ReturnBoundary.rsp returnC)
  · simpa only [rsp] using frame
  · have stackRegion := call_stack_region v pre rspC 0
      (by cases v <;> decide)
    simpa only [registerRegion, outputC, stackRegion, Nat.add_zero, BitVec.ofNat_eq_ofNat, ← rsp] using complete.1
  · intro i hi
    simpa only [outputC, ← rsp] using filled i hi

theorem compress [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {inputBytes : Nat} {blockBytes : ByteArray} {hash : Array UInt32}
    (v : Variant) (last : Bool)
    (pre : CalleePre initial boundary v.helperEntry inputBytes v.outputBytes v.reserve)
    (running : Running initial boundary (regions v initial) s)
    (rsp : stackPtr s = base v initial)
    (rip : s.RIP = v.pc (if last then .lastCall else .firstCall))
    (destination : s.regValue .rdi = stackPtr s + BitVec.ofNat 64 v.hash)
    (source : s.regValue .rsi = stackPtr s + BitVec.ofNat 64 v.scratch)
    (count : s.regValue .rdx = 1)
    (bytes : (⟨(stackPtr s + BitVec.ofNat 64 v.scratch).toNat,64⟩ : MemoryRegion).HasBytes
      s.external blockBytes)
    (words : HashStateAt s (stackPtr s + BitVec.ofNat 64 v.hash) hash) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      Running initial boundary (regions v initial) t ∧
      t.RIP = v.pc (if last then .exit else .zero) ∧
      stackPtr t = stackPtr s ∧ PreservesABI s t ∧
      MemoryWriteFrame s t (writes v (stackPtr s)) ∧
      MemoryWriteFrame s t #v[
        ⟨(stackPtr s + BitVec.ofNat 64 v.hash).toNat,32⟩,
        ⟨(stackPtr s-344).toNat,344⟩] ∧
      HashStateAt t (stackPtr s + BitVec.ofNat 64 v.hash)
        (Hkdf.Proofs.NIST.SHA256.compress hash
          (Hkdf.Proofs.NIST.Encoding.octetsToBits blockBytes)) := by
  have step := call_rel32_effect_step (compressionPc v last) (compressionDisp v last)
    (by cases v <;> cases last <;> decide +kernel)
  have instruction : CodeIn
      (codeRange (compressionPc v last) (encodeCallRel32 (compressionDisp v last))) s := by
    cases v <;> cases last
    · exact programText_slice (programLoaded_codeIn running.loaded) 0x164fa _
        (by decide) (by decide +kernel)
    · exact programText_slice (programLoaded_codeIn running.loaded) 0x165c4 _
        (by decide) (by decide +kernel)
    · exact programText_slice (programLoaded_codeIn running.loaded) 0xde56 _
        (by decide) (by decide +kernel)
    · exact programText_slice (programLoaded_codeIn running.loaded) 0xdf08 _
        (by decide) (by decide +kernel)
    · exact programText_slice (programLoaded_codeIn running.loaded) 0x1733a _
        (by decide) (by decide +kernel)
    · exact programText_slice (programLoaded_codeIn running.loaded) 0x173ec _
        (by decide) (by decide +kernel)
    · exact programText_slice (programLoaded_codeIn running.loaded) 0x175d8 _
        (by decide) (by decide +kernel)
    · exact programText_slice (programLoaded_codeIn running.loaded) 0x1768a _
        (by decide) (by decide +kernel)
  have target : branchTarget (compressionPc v last) 5
      ((compressionDisp v last).signExtend 64) = 0x1095c0 := by
    cases v <;> cases last <;> decide +kernel
  have conditions : PushPre (compressionPc v last) 5 s := by
    refine ⟨rip, call_writable v pre running rsp, ?_⟩
    cases v <;> cases last
    · exact call_codeApart .key pre rsp 0x164fa 5 (by decide)
    · exact call_codeApart .key pre rsp 0x165c4 5 (by decide)
    · exact call_codeApart .hmac pre rsp 0xde56 5 (by decide)
    · exact call_codeApart .hmac pre rsp 0xdf08 5 (by decide)
    · exact call_codeApart .simpleInner pre rsp 0x1733a 5 (by decide)
    · exact call_codeApart .simpleInner pre rsp 0x173ec 5 (by decide)
    · exact call_codeApart .simpleOuter pre rsp 0x175d8 5 (by decide)
    · exact call_codeApart .simpleOuter pre rsp 0x1768a 5 (by decide)
  obtain ⟨c, callRun, readyC, runningC, called, rspC, returnC⟩ :=
    enter pre running rsp step instruction conditions
      (by rw [target]
          exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x95c0 (by decide)))
  have outputC : c.regValue .rdi = base v initial + BitVec.ofNat 64 v.hash := by
    rw [← rsp]
    exact (called.agrees.read (n := 64) (r := 7)
      (by simp [callEffect, pushEffect_components])).trans destination
  have sourceC : c.regValue .rsi = base v initial + BitVec.ofNat 64 v.scratch := by
    rw [← rsp]
    exact (called.agrees.read (n := 64) (r := 6)
      (by simp [callEffect, pushEffect_components])).trans source
  have countC : c.regValue .rdx = BitVec.ofNat 64 1 :=
    (called.agrees.read (n := 64) (r := 2)
      (by simp [callEffect, pushEffect_components])).trans count
  have callee : CalleePre c boundary 0x1095c0 64 32 336 := by
    apply callee_pre_of_stack pre.stride pre.stack (pre.avoids _ (by simp))
      pre.outerBoundary runningC.machine runningC.directionFlag runningC.loaded
      runningC.allocated (compressionLayout v) (called.rip.trans target)
    · exact rspC.trans (below_address v initial 8)
    · exact sourceC.trans (local_address v pre v.scratch (by cases v <;> decide))
    · exact outputC.trans (local_address v pre v.hash (by cases v <;> decide))
    · rw [returnC]
      cases v <;> cases last
      · exact inProgram_of_textOffset 0x164ff (by decide)
      · exact inProgram_of_textOffset 0x165c9 (by decide)
      · exact inProgram_of_textOffset 0xde5b (by decide)
      · exact inProgram_of_textOffset 0xdf0d (by decide)
      · exact inProgram_of_textOffset 0x1733f (by decide)
      · exact inProgram_of_textOffset 0x173f1 (by decide)
      · exact inProgram_of_textOffset 0x175dd (by decide)
      · exact inProgram_of_textOffset 0x1768f (by decide)
  have hashSame := call_local_agrees called v.hash 32
    (by cases v <;> unfold OffsetsApart <;> decide +kernel) (by decide)
  have scratchSame := call_local_agrees called v.scratch 64
    (by cases v <;> unfold OffsetsApart <;> decide +kernel) (by decide)
  have hashC : HashStateAt c (c.regValue .rdi) hash := by
    rw [outputC, ← rsp]
    exact Hkdf.Proofs.Common.hashState_of_bytes words hashSame
  have bytesC : (registerRegion c .rsi 64).HasBytes c.external blockBytes := by
    change (⟨(c.regValue .rsi).toNat,64⟩ : MemoryRegion).HasBytes _ _
    rw [sourceC, ← rsp]
    refine ⟨bytes.1, fun i => ?_⟩
    have hi : i.val < 64 := by have h := i.isLt; have size : blockBytes.size = 64 := bytes.1; omega
    simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using
      (scratchSame i.val hi).trans (by
        simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using bytes.2 i)
  have compression : Hkdf.Proofs.Common.SHA256.CompressionPre c boundary hash blockBytes 1 := by
    refine ⟨callee, ?_, countC, bytesC, hashC⟩
    rw [outputC, local_toNat v pre v.hash (by cases v <;> decide)]
    have aligned := pre.stack.2.2.2
    change (stackPtr initial).toNat % 16 = 8 at aligned
    have bounds := stack_bounds pre.stack
    have frameBound : v.frame ≤ v.reserve := by cases v <;> decide
    have frameAligned : v.frame % 4 = 0 := by cases v <;> decide
    have hashAligned : v.hash % 4 = 0 := by cases v <;> decide
    omega
  obtain ⟨t, result⟩ := Hkdf.Proofs.Common.SHA256.compression_correct compression
  have within := compression_within_writes v pre rspC outputC
  have complete := call_result callee called result.toCalleeResult running.directionFlag
  have frame := frame_mono complete.1 within
  have runningT := runningC.of_callee result.toCalleeResult (by
    intro region member a contains
    obtain ⟨outer, ho, hin⟩ := within region member a contains
    exact writes_within_regions v pre outer ho a hin)
  obtain ⟨fuel, execution⟩ := result.execution
  refine ⟨1+fuel, t, callRun.trans execution, supportedMachine_readyToStep result.machine,
    runningT, ?_, ?_, complete.2, ?_, ?_, ?_⟩
  · rw [result.rip, returnC]
    cases v <;> cases last <;> rfl
  · exact result.rsp.trans (congrArg ReturnBoundary.rsp returnC)
  · simpa only [rsp] using frame
  · have stackRegion := call_stack_region v pre rspC 336
      (by cases v <;> decide)
    simpa only [registerRegion, outputC, stackRegion, Nat.reduceAdd, BitVec.ofNat_eq_ofNat, ← rsp] using complete.1
  · simpa only [outputC, ← rsp, compressBlocks_single hash blockBytes bytes.1] using result.hashWords

end Hkdf.Proofs.Common.StreamPadding.Execution
