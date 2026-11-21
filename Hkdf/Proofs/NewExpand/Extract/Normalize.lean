import Hkdf.Proofs.NewExpand.Extract.Normalize.Setup
import Hkdf.Proofs.Key
import Hkdf.Proofs.Common.StreamPadding.Execution.Calls

set_option autoImplicit false

namespace Hkdf.Proofs.NewExpand.Extract

open Hkdf.Spec Hkdf.Spec.Program Hkdf.Proofs.Program Hkdf.Proofs.Common
open Hkdf.Proofs.Common.CallFrame Hkdf.Proofs.Common.Machine
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

namespace Normalize

private abbrev layout : StackCallLayout 2264 32 64 720 :=
  ⟨464, 368, 336, by decide, by decide, by decide, by decide, by decide, by decide,
    .inl (by decide)⟩

private abbrev externalSaltLayout : StackCallLayout 2264 0 64 720 :=
  ⟨464, 368, 336, by decide, by decide, by decide, by decide, by decide, by decide,
    .inl (by decide)⟩

private theorem default_bytes [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    (stack : Stack.Valid initial 2264) (state : Prepared initial s boundary) :
    (⟨(saltAddress initial).toNat, 32⟩ : MemoryRegion).HasBytes s.external
      (RFC5869.defaultSalt .sha256) := by
  have read := stack_readable stack state.allocated (offset := 368) (len := 32)
    (by decide) (by decide)
  refine ⟨rfl, fun i ↦ ?_⟩
  have hi : i.val < 32 := i.isLt
  have chunk := Bytes.of_memLoad (n := 64) (m := s.external)
    (a := saltAddress initial + BitVec.ofNat 64 (8 * (i.val / 8))) (by
      intro j hj
      rw [BitVec.add_assoc, ← BitVec.ofNat_add]
      exact read.mem _ (by omega))
  rw [state.zeros (i.val / 8) (by omega)] at chunk
  have byte := chunk (i.val % 8) (by omega)
  rw [BitVec.add_assoc, ← BitVec.ofNat_add, show 8 * (i.val / 8) + i.val % 8 = i.val by omega] at byte
  change s.external[BitVec.ofNat 64 ((saltAddress initial).toNat + i.val)]? =
    some ((Array.replicate 32 (0 : UInt8))[i.val])
  rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  exact (by simpa [storedByte] using byte :
    s.external[saltAddress initial + BitVec.ofNat 64 i.val]? = some 0).trans
    (congrArg some (Array.getElem_replicate (n := 32) (v := (0 : UInt8))
      (i := i.val) (by simpa only [Array.size_replicate] using hi)).symm)

private theorem input_allocated {region : MemoryRegion} {m : Ram} {bytes : ByteArray}
    (contents : region.HasBytes m bytes) : region.Allocated m := by
  intro address contains
  have left := contains.1
  have right := contains.2
  let i := address.toNat - region.start
  have size : bytes.size = region.size := contents.1
  have hi : i < bytes.size := by dsimp [i]; omega
  have addressEq : BitVec.ofNat 64 (region.start + i) = address := by
    apply BitVec.eq_of_toNat_eq
    have add : region.start + i = address.toNat := by dsimp [i]; omega
    rw [add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  exact ⟨_, addressEq ▸ contents.2 ⟨i, hi⟩⟩

private theorem call_key [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
    {salt : Option ByteArray} {ikm : ByteArray} (pre : ExtractPre initial boundary salt ikm)
    (state : Prepared initial s boundary) :
    ∃ t, Normalized initial t boundary salt := by
  let ret : BitVec 64 := 0x10fadf
  let target : RamState → BitVec 64 := fun _ ↦ Key.entryAddress
  have pushed : pushAddr s = stackPtr initial - 464 := by
    change stackPtr s - 8 = _
    rw [state.rsp, base, BitVec.sub_sub]
    rfl
  have step : StepEffect (PushPre 0x10fada 5) (codeRange 0x10fada (encodeCallRel32 0x6841))
      (callEffect target ret) := call_rel32_effect_step _ _ (by decide)
  obtain ⟨c, current, effect, hret⟩ := state.toRunning.call_stack pre.call.stack pre.call.stackAvoid
    (depth := 456) state.rsp (by decide) (by decide) 0xfada 5 (by decide) state.rip step
    (programText_slice (programLoaded_codeIn state.loaded) 0xfada _
      (by decide) (by decide +kernel)) id
    (boundary_ne_program pre.call.outerBoundary (inProgram_of_textOffset 0x16320 (by decide)))
  have retIn : InProgram (returnBoundary c).rip := by
    rw [hret]; exact inProgram_of_textOffset 0xfadf (by decide)
  have rspC : stackPtr c = stackPtr initial - 464 := effect.writes.1.trans pushed
  have regs : AgreesExcept [.reg 4, .mem (pushAddr s) 8, .rip] s c := by
    simpa only [callEffect, pushEffect_components] using effect.agrees
  have output : c.regValue .rdi = stackPtr initial - 336 :=
    (regs.read (n := 64) (r := 7) (by simp)).trans state.output
  have input : c.regValue .rsi =
      (if initial.regValue .rsi = 0 then saltAddress initial else initial.regValue .rsi) :=
    (regs.read (n := 64) (r := 6) (by simp)).trans state.input
  have keyLen : c.regValue .rdx =
      (if initial.regValue .rsi = 0 then 32 else initial.regValue .rdx) :=
    (regs.read (n := 64) (r := 2) (by simp)).trans state.length
  have ctx : Key.Context c boundary (salt.getD (RFC5869.defaultSalt .sha256)) := by
    cases salt with
    | none =>
      have absent := pre.saltNull.mpr rfl
      rw [ite_eq_left absent] at input keyLen
      have localPre := callee_pre_of_stack pre.call.stride pre.call.stack pre.call.stackAvoid
        pre.call.outerBoundary current.machine current.directionFlag current.loaded current.allocated
        layout effect.rip rspC input output retIn
      have saved : (Component.mem (saltAddress initial) 32).Agrees s c := by
        have eq : stackPtr s + BitVec.ofNat 64 88 = saltAddress initial := by
          rw [state.rsp, base]; bv_omega
        have obs := Common.StreamPadding.Execution.call_local_agrees effect 88 32
          (by unfold OffsetsApart; decide +kernel) (by decide)
        rwa [eq] at obs
      refine ⟨localPre, by rw [keyLen]; rfl, ?_⟩
      have zero := default_bytes pre.call.stack state
      change (registerRegion c .rsi 32).HasBytes c.external (RFC5869.defaultSalt .sha256)
      rw [registerRegion, input]
      refine ⟨zero.1, fun i ↦ ?_⟩
      have hi : i.val < 32 := i.isLt
      have byte := saved i.val hi
      have address : BitVec.ofNat 64 ((saltAddress initial).toNat + i.val) =
          saltAddress initial + BitVec.ofNat 64 i.val := by
        rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq]
      rw [address]
      exact byte.trans (by rw [← address]; exact zero.2 i)
    | some key =>
      change Key.Context c boundary key
      have present : initial.regValue .rsi ≠ 0 := fun h ↦ by cases pre.saltNull.mp h
      rw [ite_eq_right present] at input keyLen
      have member : key ∈ some key := by simp
      have valid := pre.saltBytes key member
      have region : registerRegion c .rsi key.size = registerRegion initial .rsi key.size := by
        simp only [registerRegion, input]
      have saltApart : (registerRegion initial .rsi key.size).Disjoint
          (Stack.region initial 2264) :=
        (pre.separation.2 _ (by simp)).1 _ (by simp)
      have keyBytes := frame_hasBytes current.frame
        (fun written h ↦ Vector.mem_singleton.mp h ▸ saltApart)
        (by
          have h := valid.1
          change (registerRegion initial .rsi key.size).start + key.size < 2^32 at h
          change (registerRegion initial .rsi key.size).start + key.size ≤ 2^64
          omega) valid.2
      refine ⟨callee_pre_of_stack_output pre.call.stride pre.call.stack pre.call.stackAvoid
        pre.call.outerBoundary current.machine current.directionFlag current.loaded current.allocated
        externalSaltLayout effect.rip rspC output retIn ?_ ?_ ?_, ?_, ?_⟩
      · rw [region]; exact valid.1
      · rw [region]; exact input_allocated keyBytes
      · rw [region]; exact saltApart
      · rw [keyLen]; exact pre.saltLength key member
      · rw [region]; exact keyBytes
  obtain ⟨t, result, block⟩ := Key.normalize_correct ctx
  have running := current.of_callee result (by
    intro region hr a ha
    exact ⟨Stack.region initial 2264, by simp,
      stack_layout_within pre.call.stack layout rspC output region hr a ha⟩)
  obtain ⟨memory, abi⟩ := call_result ctx.toCalleePre effect result state.directionFlag
  have address : base initial + 80 = stackPtr initial - 376 := by unfold base; bv_omega
  have rspT : stackPtr t = stackPtr s := by
    change t.regValue .rsp = _
    rw [result.rsp, hret, state.rsp]
    rfl
  have final := state.toFrame.of_frame pre.call.stack running memory rspT abi.2.2.1 abi.2.2.2 (by
    intro region member
    rw [address]
    exact ⟨stack_layout_disjoint pre.call.stack layout rspC output
        (savedOffset := 48) (savedBytes := 56) (by decide) (by decide) region member,
      stack_layout_disjoint pre.call.stack layout rspC output
        (savedOffset := 376) (savedBytes := 8) (by decide) (by decide) region member⟩)
  refine ⟨t, ⟨final, ?_, ?_, ?_, ?_⟩⟩
  · rw [result.rip, hret]
  · exact (abi.1 .r15 (by simp)).trans state.ikmPtr
  · exact (abi.1 .r14 (by simp)).trans state.ikmLen
  · have blockAddress : base initial + 120 = stackPtr initial - 336 := by unfold base; bv_omega
    simpa only [registerRegion, output, blockAddress] using block

end Normalize

theorem normalize [Bindings] {initial : RamState} {boundary : ReturnBoundary}
    {salt : Option ByteArray} {ikm : ByteArray} (pre : ExtractPre initial boundary salt ikm) :
    ∃ s, Normalized initial s boundary salt := by
  obtain ⟨s, prepared⟩ := Normalize.prepare pre
  exact Normalize.call_key pre prepared

end Hkdf.Proofs.NewExpand.Extract
