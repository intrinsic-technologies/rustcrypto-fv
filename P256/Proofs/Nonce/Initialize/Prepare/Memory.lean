import P256.Proofs.Nonce.Initialize.State
import P256.Proofs.HMAC.State
import P256.Proofs.HMAC.Finalize.FrameSupport
import P256.Proofs.Common.Memory.LoadBytes
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovLoad.Triple
import X86Proofs.Instructions.MovStore.Triple

set_option autoImplicit false

namespace P256.Proofs.Nonce.Initialize.Prepare

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

variable [Bindings] {initial s : RamState} {boundary : ReturnBoundary}
  {orderAddress : BitVec 64}

theorem argument_readable (pre : InitializePre initial boundary orderAddress)
    (stage : Stage initial s boundary) : MemReadable s (stackPtr s + 296) 8 := by
  have bounds := Program.stack_bounds pre.stack
  have start : (initial.regValue .rsp + 8).toNat = (stackPtr initial).toNat + 8 :=
    toNat_add_ofNat (stackPtr initial) 8 (by omega)
  have addr : stackPtr s + 296 = stackPtr initial + 16 := by
    rw [stage.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
    rfl
  have endBound : (stackPtr initial).toNat + 24 < 2^32 := by
    have h := pre.argumentsBounded
    change (initial.regValue .rsp + 8).toNat + 16 < 2^32 at h
    rw [start] at h
    omega
  have finish : (stackPtr initial + 16).toNat = (stackPtr initial).toNat + 16 :=
    toNat_add_ofNat (stackPtr initial) 16 (by omega)
  rw [addr]
  apply Program.readable_of_grow _ stage.allocated
  apply memoryRegion_memReadable pre.argumentsBounded pre.argumentsAllocated
  · change (initial.regValue .rsp + 8).toNat ≤ (stackPtr initial + 16).toNat
    rw [start, finish]
    omega
  · change (stackPtr initial + 16).toNat + 8 ≤ (initial.regValue .rsp + 8).toNat + 16
    rw [start, finish]
    omega

theorem argument_order (pre : InitializePre initial boundary orderAddress)
    (stage : Stage initial s boundary) :
    memLoad s.external (stackPtr s + 296) 64 = orderAddress := by
  have bounds := Program.stack_bounds pre.stack
  have start : (initial.regValue .rsp + 8).toNat = (stackPtr initial).toNat + 8 :=
    toNat_add_ofNat (stackPtr initial) 8 (by omega)
  have apart : ∀ region ∈ #v[registerRegion initial .rdi 72, Stack.region initial 2144],
      (MemoryRegion.mk (initial.regValue .rsp + 8).toNat 16).Disjoint region := by
    intro region hr
    have cases : region = registerRegion initial .rdi 72 ∨ region = Stack.region initial 2144 := by
      simpa using hr
    rcases cases with rfl | rfl
    · exact pre.argumentsOutput
    · intro a ha hs
      have low : (initial.regValue .rsp + 8).toNat ≤ a := ha.1
      have high : a < (stackPtr initial).toNat + 8 := by
        simpa only [stack_region_end] using hs.2
      rw [start] at low
      omega
  have copied : ∀ i < 16, s.external[initial.regValue .rsp + 8 + BitVec.ofNat 64 i]? =
      initial.external[initial.regValue .rsp + 8 + BitVec.ofNat 64 i]? := by
    intro i hi
    exact frame_read stage.frame apart
      (memoryRegion_contains_add pre.argumentsBounded (Nat.le_refl _) (Nat.le_refl _) hi)
  have addr : stackPtr s + 296 = initial.regValue .rsp + 16 := by
    rw [stage.rsp]
    simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc, stackPtr]
    rfl
  have bytes : ∀ i < 8, s.external[initial.regValue .rsp + 16 + BitVec.ofNat 64 i]? =
      initial.external[initial.regValue .rsp + 16 + BitVec.ofNat 64 i]? := by
    simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using
      copied_sub (offset := 8) (len := 8) copied (by decide)
  have load := loadBytes_ok_copy bytes pre.orderPointer
  have readable := argument_readable pre stage
  rw [addr] at readable ⊢
  exact Except.ok.inj ((Bytes.of_memLoad (n := 64) readable.mem).loadBytes64.symm.trans load)

theorem stack_writable8 (pre : InitializePre initial boundary orderAddress)
    (stage : Stage initial s boundary) {offset : Nat}
    (bound : offset + 8 ≤ 280) (aligned : offset % 8 = 0) :
    MemWritable s (stackPtr s + BitVec.ofNat 64 offset) 8 := by
  rw [HMAC.Finalize.stack_address (depth := 280) stage.rsp (by omega)]
  exact Program.writable_of_grow (Program.stack_sub_writable8 pre.stack
    (fun a ha ht => pre.avoids _ (by simp) a ha (.inr ht)) (by omega) (by omega)) stage.allocated

theorem after_store {t : RamState} {offset len fuel : Nat}
    (pre : InitializePre initial boundary orderAddress) (stage : Stage initial s boundary)
    (run : Advances boundary fuel s t) (ready : ReadyToStep t)
    (agrees : AgreesExcept [.mem (stackPtr s + BitVec.ofNat 64 offset) len, .rip] s t)
    (bound : offset + len ≤ 232) : Stage initial t boundary := by
  obtain ⟨n, hn⟩ := stage.execution
  refine ⟨ScalarFrame.FrameState.after_effect pre.toCalleePre (by decide)
    stage.toFrameState ready agrees ?_ (by simp), n + fuel, hn.trans run⟩
  intro c hc a ha
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · refine ⟨ScalarFrame.workRegion initial 2144, by simp, ?_⟩
    rw [HMAC.Finalize.stack_address (depth := 280) stage.rsp (by omega)] at ha
    exact ScalarFrame.work_contains pre.toCalleePre (by omega) (by omega) ha
  · exact ha.elim

theorem order_readable (pre : InitializePre initial boundary orderAddress)
    (stage : Stage initial s boundary) (offset : Nat) (bound : offset + 8 ≤ 32) :
    MemReadable s (orderAddress + BitVec.ofNat 64 offset) 8 := by
  apply readable_of_grow _ stage.allocated
  have low : orderAddress.toNat + offset < 2^64 := by
    have h := pre.orderBounded
    change orderAddress.toNat + 32 < 2^32 at h
    omega
  have addr : (orderAddress + BitVec.ofNat 64 offset).toNat = orderAddress.toNat + offset := by
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (show offset < 2^64 by omega), Nat.mod_eq_of_lt low]
  apply memoryRegion_memReadable pre.orderBounded pre.orderAllocated
  · change orderAddress.toNat ≤ _
    rw [addr]
    omega
  · change _ ≤ orderAddress.toNat + 32
    rw [addr]
    omega

theorem order_word (pre : InitializePre initial boundary orderAddress)
    (stage : Stage initial s boundary) (offset : Nat) (bound : offset + 8 ≤ 32) :
    memLoad s.external (orderAddress + BitVec.ofNat 64 offset) 64 =
      memLoad initial.external (orderAddress + BitVec.ofNat 64 offset) 64 := by
  apply memLoad_congr
  intro i hi
  change (s.external[_]?).getD 0 = (initial.external[_]?).getD 0
  congr 1
  apply frame_read stage.frame
  · intro region hr
    have cases : region = registerRegion initial .rdi 72 ∨ region = Stack.region initial 2144 := by
      simpa using hr
    rcases cases with rfl | rfl
    · exact pre.orderOutput
    · exact pre.orderStack
  · simpa only [BitVec.add_assoc, ← BitVec.ofNat_add] using
      memoryRegion_contains_add pre.orderBounded (Nat.le_refl _) (Nat.le_refl _)
        (show offset + i < 32 by omega)

theorem stack_writable1 (pre : InitializePre initial boundary orderAddress)
    (stage : Stage initial s boundary) {offset : Nat} (bound : offset + 1 ≤ 280) :
    MemWritable s (stackPtr s + BitVec.ofNat 64 offset) 1 := by
  rw [HMAC.Finalize.stack_address (depth := 280) stage.rsp (by omega)]
  apply Program.writable_of_grow _ stage.allocated
  exact Program.stack_sub_writable pre.stack
    (fun a ha ht => pre.avoids _ (by simp) a ha (.inr ht))
    (by omega) (by omega) (by decide) (by omega)


theorem stack_writable4 (pre : InitializePre initial boundary orderAddress)
    (stage : Stage initial s boundary) {offset : Nat}
    (bound : offset + 4 ≤ 280) (aligned : offset % 4 = 0) :
    MemWritable s (stackPtr s + BitVec.ofNat 64 offset) 4 := by
  rw [HMAC.Finalize.stack_address (depth := 280) stage.rsp (by omega)]
  apply Program.writable_of_grow _ stage.allocated
  apply Program.stack_sub_writable pre.stack
    (fun a ha ht => pre.avoids _ (by simp) a ha (.inr ht))
    (by omega) (by omega) (by decide)
  rw [Program.stack_sub_toNat pre.stack (by omega)]
  have hs : (stackPtr initial).toNat % 16 = 8 := pre.stack.2.2.2
  have hn := (Program.stack_bounds pre.stack).1
  have ha : ((stackPtr initial).toNat - (280 - offset)) % 4 = 0 := by omega
  have hm := Nat.mod_mod_of_dvd ((stackPtr initial).toNat - (280 - offset))
    (show 4 ∣ 4096 by decide)
  omega

end P256.Proofs.Nonce.Initialize.Prepare
