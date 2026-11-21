import P256.Proofs.Nonce.Fill.Tail.Decode.Memory

set_option autoImplicit false

namespace P256.Proofs.Nonce.Fill.Tail.Decode.Read

open P256.Spec P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

structure Prepared [Bindings] (initial s : RamState) (orderAddress : BitVec 64)
    (state : Nonce.State) : Prop extends Context initial s orderAddress state where
  rip : s.RIP = 0x107523
  r12 : s.regValue .r12 = frameBase initial + 8
  r14 : s.regValue .r14 = 0
  count : s.regValue .rsi = 32
  limbs : s.regValue .rcx = 4
  bits : s.regValue .r8 = 256
  source : s.regValue .rdi = initial.regValue .rsi
  destination : s.regValue .rdx = frameBase initial + 104
  output : (registerRegion initial .rsi 32).HasBytes s.external (updateValue state).value

variable [Bindings] {initial s t : RamState} {boundary : ReturnBoundary}
  {orderAddress : BitVec 64} {original state : Nonce.State}

theorem stack_writable4 (pre : Pre initial boundary orderAddress original)
    (stage : Frame initial s) {offset : Nat}
    (bound : offset + 4 ≤ 232) (aligned : offset % 4 = 0) :
    MemWritable s (stackPtr s + BitVec.ofNat 64 offset) 4 := by
  rw [stage.rsp, frameBase_add initial (by omega)]
  apply writable_of_grow _ stage.allocated
  apply stack_sub_writable pre.stack
    (fun a ha ht => pre.avoids _ (by simp) a ha (.inr ht))
    (by omega) (by omega) (by decide)
  rw [stack_sub_toNat pre.stack (by omega)]
  have hs : (stackPtr initial).toNat % 16 = 8 := pre.stack.2.2.2
  have hn := (stack_bounds pre.stack).1
  have ha : ((stackPtr initial).toNat - (232 - offset)) % 4 = 0 := by omega
  have hm := Nat.mod_mod_of_dvd ((stackPtr initial).toNat - (232 - offset))
    (show 4 ∣ 4096 by decide)
  omega

theorem output_after_store {offset len : Nat}
    (pre : Pre initial boundary orderAddress original) (frame : Frame initial s)
    (agrees : AgreesExcept [.mem (stackPtr s + BitVec.ofNat 64 offset) len, .rip] s t)
    (bound : offset + len ≤ 184)
    (bytes : (registerRegion initial .rsi 32).HasBytes s.external (updateValue state).value) :
    (registerRegion initial .rsi 32).HasBytes t.external (updateValue state).value := by
  apply frame_hasBytes (written := #v[Stack.region initial 2096])
    (agrees.memoryWriteFrame ?_) _ pre.inputBounded bytes
  · intro c hc a cover
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · refine ⟨Stack.region initial 2096, by simp, ?_⟩
      rw [frame.rsp, frameBase_add initial (by omega)] at cover
      exact ScalarFrame.stack_contains pre.toCalleePre (by omega) (by omega) cover
    · exact cover.elim
  · intro region hr
    have eq : region = Stack.region initial 2096 := by simpa using hr
    subst region
    exact pre.separation 0 2 (by decide)

end P256.Proofs.Nonce.Fill.Tail.Decode.Read
