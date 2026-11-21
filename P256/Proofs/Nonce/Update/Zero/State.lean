import P256.Proofs.Nonce.Update.Phases
import P256.Proofs.Nonce.Update.Frame
import P256.Proofs.HMAC.State

set_option autoImplicit false

namespace P256.Proofs.Nonce.Update.Zero

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

structure Context [Bindings] (initial s : RamState) (state : State) : Prop extends
    FrameState initial s where
  drbg : DrbgAt s (initial.regValue .rdi) state
  savedPointer : memLoad s.external (scratch initial + 72) 64 = initial.regValue .rdi
  savedValue : memLoad s.external (scratch initial + 64) 64 = initial.regValue .rdi + 32
  savedCount : memLoad s.external (scratch initial + 424) 64 = initial.regValue .rdx
  descriptors : s.regValue .rbp = initial.regValue .rsi
  savedEnd : memLoad s.external (scratch initial + 80) 64 =
    initial.regValue .rsi + initial.regValue .rdx * 16

structure CopyReady [Bindings] (initial s : RamState) (state : State) (input : ByteArray) : Prop extends
    Context initial s state where
  rip : s.RIP = 0x10a3b1
  source : s.regValue .rsi = scratch initial + 88
  destination : s.regValue .rdi = scratch initial + 432
  hashPointer : s.regValue .rbx = scratch initial + 432
  count : s.regValue .rdx = 168
  hmac : HMAC.HmacStateAt s (scratch initial + 88) state.key input

structure Copied [Bindings] (initial s : RamState) (state : State) (input : ByteArray) : Prop extends
    Context initial s state where
  rip : s.RIP = 0x10a3b7
  hashPointer : s.regValue .rbx = scratch initial + 432
  hmac : HMAC.HmacStateAt s (scratch initial + 432) state.key input

structure HashReady [Bindings] (initial s : RamState) (state : State) (input : ByteArray) : Prop extends
    Context initial s state where
  rip : s.RIP = 0x10a3f2
  hashPointer : s.regValue .rdi = scratch initial + 432
  outputPointer : s.regValue .rsi = scratch initial + 256
  hmac : HMAC.HmacStateAt s (scratch initial + 432) state.key input

structure Hashed [Bindings] (initial s : RamState) (state : State) (input : ByteArray) : Prop extends
    Context initial s state where
  rip : s.RIP = 0x10a3f7
  output : (MemoryRegion.mk (scratch initial + 256).toNat 32).HasBytes s.external
    (Standards.RFC.HMAC.hmac Operations.hash 64 state.key input)

structure ValueReady [Bindings] (initial s : RamState) (state : State) : Prop extends
    Context initial s state where
  rip : s.RIP = 0x10a441
  drbgPointer : s.regValue .rdi = initial.regValue .rdi
  savedDrbgPointer : s.regValue .rbx = initial.regValue .rdi

theorem Context.of_copied [Bindings] {initial s t : RamState} {state result : State}
    (current : Context initial s state) (frame : FrameState initial t)
    (drbg : DrbgAt t (initial.regValue .rdi) result)
    (descriptors : t.regValue .rbp = initial.regValue .rsi)
    (copied : ∀ offset ∈ ([64,72,80,424] : List Nat), ∀ i < 8,
      t.external[scratch initial + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]? =
        s.external[scratch initial + BitVec.ofNat 64 offset + BitVec.ofNat 64 i]?) :
    Context initial t result := by
  have word (offset : Nat) (member : offset ∈ ([64,72,80,424] : List Nat)) :
      memLoad t.external (scratch initial + BitVec.ofNat 64 offset) 64 =
        memLoad s.external (scratch initial + BitVec.ofNat 64 offset) 64 := by
    apply memLoad_congr
    intro i hi
    exact congrArg (fun x : Option UInt8 => x.getD 0) (copied offset member i hi)
  exact ⟨frame, drbg, (word 72 (by simp)).trans current.savedPointer,
    (word 64 (by simp)).trans current.savedValue, (word 424 (by simp)).trans current.savedCount,
    descriptors, (word 80 (by simp)).trans current.savedEnd⟩

end P256.Proofs.Nonce.Update.Zero
