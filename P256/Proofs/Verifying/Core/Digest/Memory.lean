import P256.Proofs.Verifying.Core.Digest.Setup.State
import P256.Proofs.Verifying.Core.Digest.Return
import P256.Proofs.SecretKeyFromBytes.Scalar.Representation

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Digest

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame
open SecretKeyFromBytes.Scalar (Nat256At)

theorem base_add_toNat [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : Core.Pre s boundary) {offset : Nat} (bound : offset ≤ 1176) :
    (frameBase s+BitVec.ofNat 64 offset).toNat = (stackPtr s).toNat-1176+offset := by
  have h := stack_bounds pre.stack
  have hs : (stackPtr s-1176).toNat = (stackPtr s).toNat-1176 :=
    stack_sub_toNat pre.stack (by decide)
  rw [frameBase, BitVec.toNat_add, hs,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by omega : offset < 2^64),
    Nat.mod_eq_of_lt (by omega)]

theorem digest_bytes [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {digest : ByteArray} (pre : Core.Pre s boundary)
    (memory : MemoryWriteFrame t u (prefixRegions s))
    (bytes : (⟨(frameBase s+424).toNat,32⟩ : MemoryRegion).HasBytes t.external digest) :
    (⟨(frameBase s+424).toNat,32⟩ : MemoryRegion).HasBytes u.external digest := by
  refine ⟨bytes.1,fun i => ?_⟩
  have hi : i.val < 32 := by have h := i.isLt; have size : digest.size = 32 := bytes.1; omega
  have addr : BitVec.ofNat 64 ((frameBase s+424).toNat+i.val) =
      frameBase s+424+BitVec.ofNat 64 i.val := by
    rw [BitVec.ofNat_add,BitVec.ofNat_toNat,BitVec.setWidth_eq]
  change u.external[BitVec.ofNat 64 ((frameBase s+424).toNat+i.val)]? = _
  rw [addr]
  have same : u.external[frameBase s+424+BitVec.ofNat 64 i.val]? =
      t.external[frameBase s+424+BitVec.ofNat 64 i.val]? :=
    prefix_byte pre memory (offset := 424) (len := 32) (by decide) (by decide) hi
  rw [same, ← addr]
  exact bytes.2 i

theorem setup_writes [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : Core.Pre s boundary) :
    WritesWithin (setupClobbers s) #v[workRegion s 9992] := by
  have within (offset len : Nat) (bound : offset+len ≤ 1128) {addr : BitVec 64}
      (covered : (Component.mem (frameBase s+BitVec.ofNat 64 offset) len).Covers addr) :
      (workRegion s 9992).Contains addr.toNat := by
    obtain ⟨i,hi,rfl⟩ := covered
    have hb := stack_bounds pre.stack
    have address : (frameBase s+BitVec.ofNat 64 offset+BitVec.ofNat 64 i).toNat =
        (stackPtr s).toNat-1176+(offset+i) := by
      rw [BitVec.add_assoc,← BitVec.ofNat_add,base_add_toNat pre (by omega)]
    change (stackPtr s).toNat-9992 ≤ _ ∧ _ < (stackPtr s).toNat-9992+9944
    rw [address]
    constructor <;> omega
  intro c hc addr covered
  simp only [setupClobbers,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals try exact covered.elim
  all_goals refine ⟨workRegion s 9992,by simp,?_⟩
  · exact within 128 1 (by decide) covered
  · exact within 576 4 (by decide) covered
  · exact within 24 8 (by decide) covered
  · exact within 16 8 (by decide) covered
  · exact within 8 8 (by decide) covered
  · exact within 0 8 (by decide) covered

theorem setup_prefix_writes [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Core.Pre s boundary) (state : Frame s t) :
    WritesWithin (setupClobbers s) (prefixRegions s) := by
  intro c hc addr covered
  simp only [setupClobbers,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals try exact covered.elim
  all_goals simp only [frameBase, ← state.rsp] at covered
  · exact prefix_local_contains pre state (offset := 128) (len := 1) (by decide) covered
  · exact prefix_local_contains pre state (offset := 576) (len := 4) (by decide) covered
  · exact prefix_local_contains pre state (offset := 24) (len := 8) (by decide) covered
  · exact prefix_local_contains pre state (offset := 16) (len := 8) (by decide) covered
  · exact prefix_local_contains pre state (offset := 8) (len := 8) (by decide) covered
  · exact prefix_local_contains pre state (offset := 0) (len := 8) (by decide) covered

theorem setup_slot {s t u : RamState} {offset x : Nat}
    (agrees : AgreesExcept (setupClobbers s) t u)
    (lo : 160 ≤ offset) (hi : offset+32 ≤ 1128)
    (apart : offset+32 ≤ 576 ∨ 580 ≤ offset)
    (value : Nat256At t (frameBase s+BitVec.ofNat 64 offset) x) :
    Nat256At u (frameBase s+BitVec.ofNat 64 offset) x := by
  refine ⟨value.1,fun i hi' => ?_⟩
  rw [agrees.byte]
  · exact value.2 i hi'
  · intro c hc covered
    simp only [setupClobbers,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals try exact covered.elim
    all_goals obtain ⟨j,hj,eq⟩ := covered
    all_goals bv_omega

theorem readBe_stack [Bindings] {s a b : RamState} {boundary : ReturnBoundary}
    {digest : ByteArray} (pre : Core.Pre s boundary)
    (state : FrameState s a 24 9992 1184)
    (dst : a.regValue .rdx = frameBase s)
    (result : ReadBe.Result a b boundary digest) :
    MemoryWriteFrame a b (prefixRegions s) := by
  have hb := stack_bounds pre.stack
  have sp : (stackPtr a).toNat = (stackPtr s).toNat-1184 := by
    rw [state.rsp]
    exact stack_sub_toNat pre.stack (by decide)
  have dp : (a.regValue .rdx).toNat = (stackPtr s).toNat-1176 := by
    rw [dst,frameBase]
    exact stack_sub_toNat pre.stack (by decide)
  intro addr outside
  apply result.frame addr
  intro region hr hin
  apply outside ⟨(stackPtr s).toNat-9992,9200⟩ (by simp [prefixRegions])
  have cases : region = registerRegion a .rdx 32 ∨ region = Stack.region a 128 :=
    by simpa using hr
  change (stackPtr s).toNat-9992 ≤ addr.toNat ∧
    addr.toNat < (stackPtr s).toNat-9992+9200
  rcases cases with rfl|rfl
  · change (a.regValue .rdx).toNat ≤ addr.toNat ∧
      addr.toNat < (a.regValue .rdx).toNat+32 at hin
    rw [dp] at hin
    exact ⟨Nat.le_trans (Nat.sub_le_sub_left (by decide : 1176 ≤ 9992) _) hin.1,
      by omega⟩
  · change (stackPtr a).toNat-128 ≤ addr.toNat ∧
      addr.toNat < (Stack.region a 128).start+(Stack.region a 128).size at hin
    rw [stack_region_end] at hin
    change (stackPtr a).toNat-128 ≤ addr.toNat ∧ addr.toNat < (stackPtr a).toNat+8 at hin
    rw [sp, Nat.sub_sub] at hin
    exact ⟨Nat.le_trans (Nat.sub_le_sub_left (by decide : 1184+128 ≤ 9992) _) hin.1,
      by omega⟩

theorem readBe_slot [Bindings] {s a b : RamState} {boundary : ReturnBoundary}
    {digest : ByteArray} {offset x : Nat} (pre : Core.Pre s boundary)
    (state : FrameState s a 24 9992 1184)
    (dst : a.regValue .rdx = frameBase s)
    (result : ReadBe.Result a b boundary digest)
    (lo : 32 ≤ offset) (hi : offset+32 ≤ 1128)
    (value : Nat256At a (frameBase s+BitVec.ofNat 64 offset) x) :
    Nat256At b (frameBase s+BitVec.ofNat 64 offset) x := by
  have hb := stack_bounds pre.stack
  have sp : (stackPtr a).toNat = (stackPtr s).toNat-1184 := by
    rw [state.rsp]
    exact stack_sub_toNat pre.stack (by decide)
  have dp : (a.regValue .rdx).toNat = (stackPtr s).toNat-1176 := by
    rw [dst,frameBase]
    exact stack_sub_toNat pre.stack (by decide)
  refine ⟨value.1,fun i hi' => ?_⟩
  rw [result.frame]
  · exact value.2 i hi'
  · intro region hr hin
    have addr : (frameBase s+BitVec.ofNat 64 offset+BitVec.ofNat 64 i).toNat =
        (stackPtr s).toNat-1176+(offset+i) := by
      rw [BitVec.add_assoc,← BitVec.ofNat_add,base_add_toNat pre (by omega)]
    have cases : region = registerRegion a .rdx 32 ∨ region = Stack.region a 128 :=
      by simpa using hr
    rcases cases with rfl|rfl
    · change (a.regValue .rdx).toNat ≤ _ ∧ _ < (a.regValue .rdx).toNat+32 at hin
      rw [dp,addr] at hin
      omega
    · change (stackPtr a).toNat-128 ≤ _ ∧
        _ < (Stack.region a 128).start+(Stack.region a 128).size at hin
      rw [stack_region_end] at hin
      change (stackPtr a).toNat-128 ≤ _ ∧ _ < (stackPtr a).toNat+8 at hin
      rw [sp,addr] at hin
      omega

end P256.Proofs.Verifying.Core.Digest
