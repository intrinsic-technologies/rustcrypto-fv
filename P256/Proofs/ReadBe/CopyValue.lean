import P256.Proofs.ReadBe.CallResult
import P256.Proofs.ReadBe.Input

set_option autoImplicit false

open P256.Proofs.Program

namespace P256.Proofs.ReadBe

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [Bindings] {s t u v : RamState} {boundary : ReturnBoundary}

theorem Pre.call_input_byte (pre : Pre s boundary) (frame : Frame s t)
    {target ret : BitVec 64} (effect : (callEffect (fun _ => target) ret t).Holds t u)
    {i : Nat} (hi : i < 32) :
    u.external[s.regValue .rdi + BitVec.ofNat 64 i]? =
      t.external[s.regValue .rdi + BitVec.ofNat 64 i]? := by
  apply effect.agrees.memoryWriteFrame (pre.call_writes frame)
  intro r hr ha
  have hin := memoryRegion_contains_add pre.inputBounded (Nat.le_refl _) (Nat.le_refl _) hi
  have hr' : r = registerRegion s .rdx 32 ∨ r = scratchRegion s := by simpa using hr
  rcases hr' with rfl | rfl
  · exact pre.separation (0 : Fin 3) (1 : Fin 3) (by decide) _ hin ha
  · exact pre.separation (0 : Fin 3) (2 : Fin 3) (by decide) _ hin (pre.scratch_subset ha)

theorem Pre.copied_limb (pre : Pre s boundary) (frame : Frame s t) {k : Nat}
    {input : ByteArray} (hk : k < 4)
    (bytes : (registerRegion s .rdi 32).HasBytes t.external input)
    (effect : (callEffect (fun _ => 0x11c930) 0x119131 t).Holds t u)
    (source : t.regValue .rsi = s.regValue .rdi + BitVec.ofNat 64 (24-8*k))
    (destination : t.regValue .rdi = frameBase s + 16)
    (copied : ∀ i < 8, v.external[u.regValue .rdi + BitVec.ofNat 64 i]? =
      u.external[u.regValue .rsi + BitVec.ofNat 64 i]?) :
    P256.Proofs.Common.Instructions.bswap64 (memLoad v.external (frameBase s + 16) 64) =
      BitVec.ofNat 64 (Arith.uint input / 2^(64*k)) := by
  have src : u.regValue .rsi = s.regValue .rdi + BitVec.ofNat 64 (8*(3-k)) := by
    rw [show 8*(3-k) = 24-8*k by omega]
    exact (effect.agrees.read (n := 64) (r := 6) (by simp)).trans source
  have dst : u.regValue .rdi = frameBase s + 16 :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans destination
  have equal : memLoad v.external (frameBase s + 16) 64 =
      memLoad t.external (s.regValue .rdi + BitVec.ofNat 64 (8*(3-k))) 64 := by
    apply memLoad_congr
    intro i hi
    change v.external[frameBase s + 16 + BitVec.ofNat 64 i]?.getD 0 =
      t.external[s.regValue .rdi + BitVec.ofNat 64 (8*(3-k)) + BitVec.ofNat 64 i]?.getD 0
    congr 1
    have copy := copied i hi
    rw [src, dst] at copy
    rw [copy, BitVec.add_assoc, ← BitVec.ofNat_add]
    exact pre.call_input_byte frame effect (by omega)
  rw [equal, bswap_input_memLoad_limb bytes (3-k) (by omega), show 3-(3-k) = k by omega]

end P256.Proofs.ReadBe
