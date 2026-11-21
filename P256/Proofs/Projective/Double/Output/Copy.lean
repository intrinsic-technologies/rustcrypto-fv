import P256.Proofs.Field.Representation
import P256.Proofs.Projective.Double.Memory
import P256.Proofs.Program.ScalarFrame.Copy32Bytes
import P256.Proofs.Projective.Add.Copy.Stack
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Field.Operations.Run.Compose

set_option autoImplicit false


namespace P256.Proofs.Projective.Double.Output

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

abbrev CopyPre (p : BitVec 64) (src : BitVec 5) (source target : Nat) :=
  Copy32.Pre p (fun s => (Operand.reg src : Operand 64).read s + BitVec.ofNat 64 source)
    (fun s => stackPtr s + BitVec.ofNat 64 target)

abbrev copyEffect (next : BitVec 64) (src : BitVec 5) (source target : Nat) :=
  Copy32.effect next (fun s => (Operand.reg src : Operand 64).read s + BitVec.ofNat 64 source)
    (fun s => stackPtr s + BitVec.ofNat 64 target)

theorem copy_source_apart {s : RamState} {p : BitVec 64} {src : BitVec 5} {source target : Nat}
    (pre : CopyPre p src source target s) (i : BitVec 64)
    (hi : i ∈ ([0,8,16,24] : List (BitVec 64))) (j : BitVec 64)
    (hj : j ∈ ([0,8,16,24] : List (BitVec 64))) :
    RangeApart (stackPtr s + (BitVec.ofNat 64 target + i)) 8
      ((Operand.reg src : Operand 64).read s + (BitVec.ofNat 64 source + j)) 8 := by
  have ib : i.toNat ≤ 24 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl <;> decide
  have jb : j.toNat ≤ 24 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hj
    rcases hj with rfl | rfl | rfl | rfl <;> decide
  intro a ha b hb he
  apply pre.apart (i.toNat+a) (by omega) (j.toNat+b) (by omega)
  simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.add_assoc]
    using he

theorem copy_montgomery {s t : RamState} {p next : BitVec 64} {src : BitVec 5} {source target x : Nat}
    (pre : CopyPre p src source target s) (effect : (copyEffect next src source target s).Holds s t)
    (input : MontgomeryAt s ((Operand.reg src : Operand 64).read s + BitVec.ofNat 64 source) x) :
    MontgomeryAt t (stackPtr s + BitVec.ofNat 64 target) x := by
  obtain ⟨_, _, h0, h8, h16, h24⟩ := effect.writes
  apply Field.montgomeryAt_of_memLoad_limbs input.1
  · intro i hi
    apply effect.agrees.grow
    have cases : i / 8 = 0 ∨ i / 8 = 1 ∨ i / 8 = 2 ∨ i / 8 = 3 := by omega
    have writable : P256.Proofs.Common.Instructions.CrossPageStore.Writable s ((stackPtr s + BitVec.ofNat 64 target) + BitVec.ofNat 64 (8*(i/8))) 8 := by
      rcases cases with h | h | h | h
      · simpa (config := {decide := true}) only [Copy32.effect, x86_compose, h, BitVec.add_assoc] using pre.writable 0 (by simp)
      · simpa (config := {decide := true}) only [Copy32.effect, x86_compose, h, BitVec.add_assoc] using pre.writable 8 (by simp)
      · simpa (config := {decide := true}) only [Copy32.effect, x86_compose, h, BitVec.add_assoc] using pre.writable 16 (by simp)
      · simpa (config := {decide := true}) only [Copy32.effect, x86_compose, h, BitVec.add_assoc] using pre.writable 24 (by simp)
    simpa only [BitVec.add_assoc, ← BitVec.ofNat_add, Nat.add_assoc, show 8*(i/8)+i%8=i by omega] using
      writable.mem (i%8) (by omega)
  · intro j hj
    rw [← input.memLoad_limb j hj]
    have cases : j=0 ∨ j=1 ∨ j=2 ∨ j=3 := by omega
    rcases cases with rfl | rfl | rfl | rfl
    · simpa (config := {decide := true}) only [Copy32.effect, x86_compose, BitVec.add_zero, BitVec.ofNat_add, BitVec.add_assoc, Write.AllHold] using h0
    · simpa (config := {decide := true}) only [Copy32.effect, x86_compose, BitVec.add_zero, BitVec.ofNat_add, BitVec.add_assoc, Write.AllHold] using h8
    · simpa (config := {decide := true}) only [Copy32.effect, x86_compose, BitVec.add_zero, BitVec.ofNat_add, BitVec.add_assoc, Write.AllHold] using h16
    · simpa (config := {decide := true}) only [Copy32.effect, x86_compose, BitVec.add_zero, BitVec.ofNat_add, BitVec.add_assoc, Write.AllHold] using h24

end P256.Proofs.Projective.Double.Output
