import P256.Proofs.Verifying.Core.Interface
import P256.Proofs.Program.ScalarFrame.Memory
import P256.Proofs.Program.ScalarFrame.Call
import P256.Proofs.SecretKeyFromBytes.Scalar.Representation

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core

open P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program ScalarFrame

theorem signature_readable [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Core.Pre s boundary) (state : Frame s t) {offset len : Nat}
    (bound : offset+len ≤ 64) :
    MemReadable t (s.regValue .r8 + BitVec.ofNat 64 offset) len := by
  have bounded : (s.regValue .r8).toNat + 64 < 2^32 := pre.signatureBounded
  have low : (s.regValue .r8 + BitVec.ofNat 64 offset).toNat =
      (s.regValue .r8).toNat + offset := by
    rw [BitVec.toNat_add,BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : offset < 2^64),
      Nat.mod_eq_of_lt (by omega)]
  apply readable_of_grow (memoryRegion_memReadable pre.signatureBounded
    pre.signatureAllocated ?_ ?_) state.allocated
  · change (s.regValue .r8).toNat ≤ _
    rw [low]
    omega
  · change _ ≤ (s.regValue .r8).toNat+64
    rw [low]
    omega

theorem local_writable8 [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Core.Pre s boundary) (state : Frame s t) {offset : Nat}
    (bound : offset ≤ 1128) (aligned : offset % 8 = 0) :
    MemWritable t (stackPtr t + BitVec.ofNat 64 offset) 8 := by
  rw [scalar_stack_address (frameOffset := 1176) state.rsp (by decide) (by omega)]
  exact writable_of_grow (stack_sub_writable8 pre.stack
    (fun a ha hp => pre.avoids _ (by simp) a ha (.inr hp))
    (by omega) (by omega)) state.allocated

theorem local_signature_apart [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Core.Pre s boundary) (state : Frame s t) {offset len inputOffset inputLen : Nat}
    (bound : offset+len ≤ 1176) (inputBound : inputOffset+inputLen ≤ 64) :
    RangeApart (stackPtr t + BitVec.ofNat 64 offset) len
      (s.regValue .r8 + BitVec.ofNat 64 inputOffset) inputLen := by
  intro i hi j hj eq
  have hs : (Stack.region s 9992).Contains
      (stackPtr t + BitVec.ofNat 64 offset + BitVec.ofNat 64 i).toNat := by
    rw [scalar_stack_address (frameOffset := 1176) state.rsp (by decide) (by omega)]
    exact ScalarFrame.stack_contains pre.toCalleePre (by omega) (by omega) ⟨i,hi,rfl⟩
  have hin : (registerRegion s .r8 64).Contains
      (s.regValue .r8 + BitVec.ofNat 64 inputOffset + BitVec.ofNat 64 j).toNat := by
    rw [BitVec.add_assoc,← BitVec.ofNat_add]
    exact memoryRegion_contains_add pre.signatureBounded (len := 64)
      (Nat.le_refl _) (Nat.le_refl _) (by omega)
  rw [← eq] at hin
  exact pre.signatureStack _ hin hs

theorem local_work_contains [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Core.Pre s boundary) (state : Frame s t) {offset len : Nat} {a : BitVec 64}
    (bound : offset+len ≤ 1128)
    (covered : (Component.mem (stackPtr t+BitVec.ofNat 64 offset) len).Covers a) :
    (workRegion s 9992).Contains a.toNat := by
  rw [scalar_stack_address (frameOffset := 1176) state.rsp (by decide) (by omega)] at covered
  exact work_contains pre.toCalleePre (by omega) (by omega) covered

theorem signature_nat256 [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {offset x : Nat} (pre : Core.Pre s boundary) (bound : offset+32 ≤ 64)
    (memory : MemoryWriteFrame t u #v[Stack.region s 9992])
    (value : SecretKeyFromBytes.Scalar.Nat256At t
      (s.regValue .r8+BitVec.ofNat 64 offset) x) :
    SecretKeyFromBytes.Scalar.Nat256At u (s.regValue .r8+BitVec.ofNat 64 offset) x := by
  refine ⟨value.1,fun i hi => ?_⟩
  rw [memory]
  · exact value.2 i hi
  · intro region hr hin
    have eq : region = Stack.region s 9992 := by simpa using hr
    subst region
    apply pre.signatureStack _ ?_ hin
    rw [BitVec.add_assoc,← BitVec.ofNat_add]
    exact memoryRegion_contains_add pre.signatureBounded (len := 64)
      (Nat.le_refl _) (Nat.le_refl _) (by omega)

theorem work_memory_stack [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    (pre : Core.Pre s boundary)
    (memory : MemoryWriteFrame t u #v[workRegion s 9992]) :
    MemoryWriteFrame t u #v[Stack.region s 9992] := by
  intro a ha
  apply memory a
  intro region hr hin
  have eq : region = workRegion s 9992 := by simpa using hr
  subst region
  apply ha (Stack.region s 9992) (by simp)
  have bounds := stack_bounds pre.stack
  change (stackPtr s).toNat-9992 ≤ a.toNat ∧
    a.toNat < (stackPtr s).toNat-9992+(9992-48) at hin
  change (stackPtr s).toNat-9992 ≤ a.toNat ∧
    a.toNat < (Stack.region s 9992).start+(Stack.region s 9992).size
  rw [stack_region_end]
  constructor <;> omega

def prefixRegions (s : RamState) : Vector MemoryRegion 2 :=
  #v[⟨(stackPtr s).toNat-9992,9200⟩,⟨(stackPtr s).toNat-600,424⟩]

theorem prefix_stack_contains [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (pre : Core.Pre s boundary) {offset len : Nat} {a : BitVec 64}
    (lo : 792+len ≤ offset) (hi : offset ≤ 9992)
    (covered : (Component.mem (stackPtr s-BitVec.ofNat 64 offset) len).Covers a) :
    ∃ region ∈ prefixRegions s, region.Contains a.toNat := by
  obtain ⟨i,hi',rfl⟩ := covered
  have hb := stack_bounds pre.stack
  have hs := stack_sub_toNat pre.stack hi
  have ha : (stackPtr s-BitVec.ofNat 64 offset+BitVec.ofNat 64 i).toNat =
      (stackPtr s).toNat-offset+i := by
    rw [BitVec.toNat_add,hs,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : i < 2^64),Nat.mod_eq_of_lt (by omega)]
  refine ⟨⟨(stackPtr s).toNat-9992,9200⟩,by simp [prefixRegions],?_⟩
  change (stackPtr s).toNat-9992 ≤ _ ∧ _ < (stackPtr s).toNat-9992+9200
  rw [ha]
  constructor <;> omega

theorem prefix_local_contains [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : Core.Pre s boundary) (state : Frame s t) {offset len : Nat} {a : BitVec 64}
    (bound : offset+len ≤ 384 ∨ 576 ≤ offset ∧ offset+len ≤ 1000)
    (covered : (Component.mem (stackPtr t+BitVec.ofNat 64 offset) len).Covers a) :
    ∃ region ∈ prefixRegions s, region.Contains a.toNat := by
  have hb := stack_bounds pre.stack
  have off : offset ≤ 1176 := by omega
  rw [scalar_stack_address (frameOffset := 1176) state.rsp (by decide) off] at covered
  rcases bound with bound | ⟨lo,hi⟩
  · exact prefix_stack_contains pre (by omega) (by omega) covered
  · obtain ⟨i,hi',rfl⟩ := covered
    have hs := stack_sub_toNat pre.stack (offset := 1176-offset) (by omega)
    have ha : (stackPtr s-BitVec.ofNat 64 (1176-offset)+BitVec.ofNat 64 i).toNat =
        (stackPtr s).toNat-(1176-offset)+i := by
      rw [BitVec.toNat_add,hs,BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (by omega : i < 2^64),Nat.mod_eq_of_lt (by omega)]
    refine ⟨⟨(stackPtr s).toNat-600,424⟩,by simp [prefixRegions],?_⟩
    change (stackPtr s).toNat-600 ≤ _ ∧ _ < (stackPtr s).toNat-600+424
    rw [ha]
    constructor <;> omega

theorem prefix_memory_stack [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    (pre : Core.Pre s boundary) (memory : MemoryWriteFrame t u (prefixRegions s)) :
    MemoryWriteFrame t u #v[Stack.region s 9992] := by
  intro a outside
  apply memory a
  intro region hr hin
  apply outside (Stack.region s 9992) (by simp)
  have hb := stack_bounds pre.stack
  change (stackPtr s).toNat-9992 ≤ a.toNat ∧
    a.toNat < (Stack.region s 9992).start+(Stack.region s 9992).size
  rw [stack_region_end]
  have hr' : region = ⟨(stackPtr s).toNat-9992,9200⟩ ∨
      region = ⟨(stackPtr s).toNat-600,424⟩ := by simpa [prefixRegions] using hr
  rcases hr' with rfl | rfl
  all_goals dsimp only [MemoryRegion.Contains] at hin
  all_goals constructor <;> omega

theorem prefix_byte [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    (pre : Core.Pre s boundary) (memory : MemoryWriteFrame t u (prefixRegions s))
    {offset i len : Nat} (bound : offset+len ≤ 1176)
    (apart : (384 ≤ offset ∧ offset+len ≤ 576) ∨ 1000 ≤ offset) (hi : i < len) :
    u.external[frameBase s+BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? =
      t.external[frameBase s+BitVec.ofNat 64 offset+BitVec.ofNat 64 i]? := by
  apply memory
  intro region hr hin
  have hb := stack_bounds pre.stack
  have hs : (stackPtr s-1176).toNat = (stackPtr s).toNat-1176 :=
    stack_sub_toNat pre.stack (offset := 1176) (by decide)
  have ha : (frameBase s+BitVec.ofNat 64 offset+BitVec.ofNat 64 i).toNat =
      (stackPtr s).toNat-1176+(offset+i) := by
    rw [frameBase,BitVec.add_assoc,← BitVec.ofNat_add,BitVec.toNat_add,hs,
      BitVec.toNat_ofNat,Nat.mod_eq_of_lt (by omega : offset+i < 2^64),
      Nat.mod_eq_of_lt (by omega)]
  have hr' : region = ⟨(stackPtr s).toNat-9992,9200⟩ ∨
      region = ⟨(stackPtr s).toNat-600,424⟩ := by simpa [prefixRegions] using hr
  rcases hr' with rfl | rfl
  all_goals dsimp only [MemoryRegion.Contains] at hin
  all_goals rw [ha] at hin
  all_goals rcases apart with apart | apart <;> omega

theorem prefix_call [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    {target : RamState → BitVec 64} {ret : BitVec 64}
    (pre : Core.Pre s boundary) (state : Frame s t)
    (effect : (callEffect target ret t).Holds t u) :
    MemoryWriteFrame t u (prefixRegions s) := by
  apply effect.agrees.memoryWriteFrame
  intro c hc a ha
  simp only [pushEffect_components,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact ha.elim
  · rw [scalar_call_address state] at ha
    exact prefix_stack_contains pre (by decide) (by decide) ha
  · exact ha.elim

theorem prefix_result [Bindings] {s a b : RamState} {boundary : ReturnBoundary}
    {offset len reserve : Nat} (pre : Core.Pre s boundary)
    (state : FrameState s a 24 9992 1184) (result : CalleeResult a b boundary len reserve)
    (dst : a.regValue .rdi = frameBase s+BitVec.ofNat 64 offset)
    (bound : offset+len ≤ 384 ∨ 576 ≤ offset ∧ offset+len ≤ 1000)
    (reserved : reserve+1184 ≤ 9992) :
    MemoryWriteFrame a b (prefixRegions s) := by
  have hb := stack_bounds pre.stack
  have sp : (stackPtr a).toNat = (stackPtr s).toNat-1184 := by
    rw [state.rsp]
    exact stack_sub_toNat pre.stack (by decide)
  have hs : (stackPtr s-1176).toNat = (stackPtr s).toNat-1176 :=
    stack_sub_toNat pre.stack (by decide)
  have dp : (a.regValue .rdi).toNat = (stackPtr s).toNat-1176+offset := by
    rw [dst,frameBase,BitVec.toNat_add,hs,BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : offset < 2^64),Nat.mod_eq_of_lt (by omega)]
  intro addr outside
  apply result.frame addr
  intro region hr hin
  have cases : region = registerRegion a .rdi len ∨ region = Stack.region a reserve :=
    by simpa using hr
  rcases cases with rfl | rfl
  · change (a.regValue .rdi).toNat ≤ addr.toNat ∧
      addr.toNat < (a.regValue .rdi).toNat+len at hin
    rw [dp] at hin
    rcases bound with bound | bound
    · apply outside ⟨(stackPtr s).toNat-9992,9200⟩ (by simp [prefixRegions])
      dsimp only [MemoryRegion.Contains]
      constructor <;> omega
    · apply outside ⟨(stackPtr s).toNat-600,424⟩ (by simp [prefixRegions])
      dsimp only [MemoryRegion.Contains]
      constructor <;> omega
  · change (stackPtr a).toNat-reserve ≤ addr.toNat ∧
      addr.toNat < (Stack.region a reserve).start+(Stack.region a reserve).size at hin
    rw [stack_region_end] at hin
    change (stackPtr a).toNat-reserve ≤ addr.toNat ∧ addr.toNat < (stackPtr a).toNat+8 at hin
    rw [sp] at hin
    apply outside ⟨(stackPtr s).toNat-9992,9200⟩ (by simp [prefixRegions])
    dsimp only [MemoryRegion.Contains]
    constructor <;> omega

theorem prefix_load [Bindings] {s t u : RamState} {boundary : ReturnBoundary}
    (pre : Core.Pre s boundary) (memory : MemoryWriteFrame t u (prefixRegions s))
    {offset n : Nat} (bound : offset+n/8 ≤ 1176)
    (apart : (384 ≤ offset ∧ offset+n/8 ≤ 576) ∨ 1000 ≤ offset) :
    memLoad u.external (frameBase s+BitVec.ofNat 64 offset) n =
      memLoad t.external (frameBase s+BitVec.ofNat 64 offset) n := by
  apply memLoad_congr
  intro i hi
  exact congrArg (fun value : Option UInt8 => value.getD 0) (prefix_byte pre memory bound apart hi)

end P256.Proofs.Verifying.Core
