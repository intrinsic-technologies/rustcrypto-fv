import Hkdf.Proofs.NewExpand.Expand.Positive.Copy.Arguments
import Hkdf.Proofs.NewExpand.Expand.Positive.Copy.Geometry
import Hkdf.Proofs.NewExpand.Expand.Positive.Iteration.Counter.Frame
import Hkdf.Proofs.Common.Memory.Copy
import Hkdf.Proofs.Common.StreamPadding.Execution.Calls

namespace Hkdf.Proofs.NewExpand.Expand

open Hkdf.Spec.Program Hkdf.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Hkdf.Proofs.Common Hkdf.Proofs.Common.Machine Hkdf.Proofs.Common.CallFrame

def copyReturnSlot (entry : RamState) : MemoryRegion := ⟨(stackPtr entry).toNat - 544, 8⟩

theorem copyReturnSlot_within {entry : RamState} (stack : Stack.Valid entry 2264)
    {a : Nat} (h : (copyReturnSlot entry).Contains a) : (Stack.region entry 2264).Contains a := by
  have bounds := stack_bounds stack
  change (stackPtr entry).toNat - 544 ≤ a ∧ a < (stackPtr entry).toNat - 544 + 8 at h
  unfold MemoryRegion.Contains
  rw [stack_region_end]
  change (stackPtr entry).toNat - 2264 ≤ a ∧ _
  constructor <;> omega

theorem copyChunk [Bindings] {entry s : RamState} {boundary : ReturnBoundary}
    {key info digest : ByteArray} {ptr : BitVec 64} {length n : Nat}
    (pre : ExpandPre entry boundary key info ptr length) (saved : SavedFrame entry s boundary length)
    (pc : s.RIP = 0x10f53c) (more : 32*n < length) (limit : length ≤ 8160)
    (target : s.regValue .r12 = 0x10dd60)
    (dest : s.regValue .r14 = entry.regValue .rcx + BitVec.ofNat 64 (32*n))
    (src : s.regValue .r13 = stackPtr s + 16)
    (count : s.regValue .rbx = BitVec.ofNat 64 (min (length - 32*n) 32))
    (bytes : (⟨(stackPtr s + 16).toNat, 32⟩ : MemoryRegion).HasBytes s.external digest) :
    ∃ t, Counter.RunningFrame entry boundary length t ∧ t.RIP = 0x10f548 ∧
      stackPtr t = stackPtr s ∧ PreservesABI s t ∧
      MemoryWriteFrame s t #v[outputChunk entry length n, copyReturnSlot entry] ∧
      (outputChunk entry length n).HasBytes t.external (digest.extract 0 (min (length - 32*n) 32)) := by
  have ctx := Counter.StackContext.of_pre pre (by omega) limit
  obtain ⟨fuel,u,advance,ready,_,args⟩ := copyArguments boundary ctx.outside s
    (supportedMachine_readyToStep saved.machine)
    (programText_slice (programLoaded_codeIn saved.loaded) 0xf53c copyArgumentsBytes
      (by decide) (by decide +kernel)) pc
  have ag : AgreesExcept [.reg 7,.reg 6,.reg 2,.rip] s u := args.agrees
  have nomem : ∀ c ∈ [Component.reg 7,.reg 6,.reg 2,.rip], ∀ a, ¬ c.Covers a := by simp [Component.Covers]
  have runningU := Counter.no_memory ctx saved.toRunning advance ready ag nomem (by decide)
  have spU : stackPtr u = stackPtr s := ag.read (n := 64) (r := 4) (by decide)
  have targetU : u.regValue .r12 = 0x10dd60 := (ag.read (n := 64) (r := 12) (by decide)).trans target
  let callTarget := fun u : RamState ↦ u.regValue .r12
  have step : StepEffect (X86Proofs.CallPre 0x10f545 3 callTarget)
      (codeRange 0x10f545 [0x41,0xff,0xd4]) (callEffect callTarget 0x10f548) :=
    call_r64_rex_effect_step 0x10f545 0x41 0xd4 (by simp [RexPrefix]) rfl rfl
  obtain ⟨c,runningC,call,ret⟩ := Counter.enter_call ctx runningU (spU.trans saved.sp) 0xf545 3
    (by decide) args.rip step
    (programText_slice (programLoaded_codeIn runningU.loaded) 0xf545 [0x41,0xff,0xd4]
      (by decide) (by decide +kernel))
    (fun pushed => ⟨pushed, by change (u.regValue .r12).toNat < 2^32; rw [targetU]; decide⟩)
    (by change u.regValue .r12 ≠ _; rw [targetU]
        exact boundary_ne_program ctx.outside (inProgram_of_textOffset 0xdd60 (by decide)))
  have spC : stackPtr c = stackPtr entry - 544 := by
    rw [show stackPtr c = pushAddr u from call.writes.1, pushAddr, spU,
      show stackPtr s = stackPtr entry - 536 from saved.sp, BitVec.sub_sub]
    rfl
  have srcC : c.regValue .rsi = stackPtr s + 16 :=
    (call.agrees.read (n := 64) (r := 6) (by simp [callEffect, pushEffect_components])).trans
      (args.writes.2.1.trans src)
  have dstC : c.regValue .rdi = entry.regValue .rcx + BitVec.ofNat 64 (32*n) :=
    (call.agrees.read (n := 64) (r := 7) (by simp [callEffect, pushEffect_components])).trans
      (args.writes.1.trans dest)
  have countC : c.regValue .rdx = BitVec.ofNat 64 (min (length - 32*n) 32) :=
    (call.agrees.read (n := 64) (r := 2) (by simp [callEffect, pushEffect_components])).trans
      (args.writes.2.2.trans count)
  obtain ⟨callee,destEq,retEq⟩ := copyChunkPre pre more limit runningC (call.rip.trans targetU)
    (congrArg ReturnBoundary.rip ret) spC
    (srcC.trans (by rw [show stackPtr s = stackPtr entry - 536 from saved.sp]; bv_omega)) dstC
  change Stack.region c 0 = copyReturnSlot entry at retEq
  obtain ⟨t,result,copied,_⟩ := Memory.memcpy_correct callee countC (by omega)
  obtain ⟨frame,abi⟩ := call_result callee call result runningU.directionFlag
  have runningT := runningC.of_callee result (by
    intro r hr a ha
    rw [destEq,retEq] at hr
    have choices : r = outputChunk entry length n ∨ r = copyReturnSlot entry := by simpa using hr
    rcases choices with rfl | rfl
    · exact ⟨_, by simp [Counter.regions, writtenLength, limit], outputChunk_within entry length n a ha⟩
    · exact ⟨Stack.region entry 2264, by simp [Counter.regions], copyReturnSlot_within ctx.stack ha⟩)
  have abiU : PreservesABI s u := by
    apply preservesABI_of_agrees ag saved.directionFlag _ (by decide) (by decide) (by decide)
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ag.read (n := 64) (r := 3) (by decide)
    · exact ag.read (n := 64) (r := 5) (by decide)
    · exact ag.read (n := 64) (r := 12) (by decide)
    · exact ag.read (n := 64) (r := 13) (by decide)
    · exact ag.read (n := 64) (r := 14) (by decide)
    · exact ag.read (n := 64) (r := 15) (by decide)
  refine ⟨t,runningT,result.rip.trans (congrArg ReturnBoundary.rip ret),
    (result.rsp.trans (congrArg ReturnBoundary.rsp ret)).trans saved.sp.symm,
    preservesABI_trans abiU abi, ?_, ?_⟩
  · rw [destEq,retEq] at frame
    exact memoryWriteFrame_trans (ag.memoryWriteFrame (fun c hc a ha ↦ (nomem c hc a ha).elim)) frame
  · have size : digest.size = 32 := bytes.1
    have input := StreamPadding.Execution.call_local_agrees call 16 32
      (by unfold OffsetsApart; decide +kernel) (by decide)
    have memory := ag.external nomem
    refine ⟨by change (digest.extract _ _).size = _; rw [ByteArray.size_extract, size]; change _ = min _ 32; omega, ?_⟩
    rintro ⟨i, hi⟩
    rw [ByteArray.size_extract, size] at hi
    have byte := copied i (by omega)
    have inputByte := input i (by omega)
    change c.external[stackPtr u + 16 + BitVec.ofNat 64 i]? =
      u.external[stackPtr u + 16 + BitVec.ofNat 64 i]? at inputByte
    rw [spU, memory] at inputByte
    rw [srcC, dstC, inputByte] at byte
    have digestByte := bytes.2 ⟨i, by omega⟩
    simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at digestByte
    simpa only [outputChunk, BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq,
      ByteArray.getElem_extract, Nat.zero_add] using byte.trans digestByte

end Hkdf.Proofs.NewExpand.Expand
