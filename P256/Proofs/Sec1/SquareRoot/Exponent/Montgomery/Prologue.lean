import P256.Proofs.Field.Interface
import P256.Proofs.Program.Push
import P256.Proofs.Program.State
import P256.Proofs.Common.Field.SquareRoot.Multiply.Prologue
import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Code
import X86Proofs.Program.Compose

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Montgomery

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Field.SquareRoot.Multiply

theorem prologue_correct [bindings : Bindings] {s : RamState} {boundary : ReturnBoundary}
    {entry : BitVec 64} (hentry : Entry entry)
    (pre : CalleePre s boundary entry 32 32 160) :
    ∃ t, Advances boundary 7 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP = entry + (14 : BitVec 64) ∧ stackPtr t = stackPtr s - 160 ∧
      t.external = savedMemory s ∧ AgreesExcept (prologueComponents s) s t := by
  have hsize (offset : Nat) (src : BitVec 4)
      (h : offset + (encodePushR64 src).length ≤ 1469) :
      routineOffset entry + offset + (encodePushR64 src).length < 118431 := by
    have := routineOffset_bound hentry
    omega
  have hbytes (offset : Nat) (src : BitVec 4)
      (h : offset + (encodePushR64 src).length ≤ 1469)
      (hb : Extracted.textBytes.toListFrom (0x145e0 + offset) (encodePushR64 src).length =
        encodePushR64 src) :
      Extracted.textBytes.toListFrom (routineOffset entry + offset) (encodePushR64 src).length =
        encodePushR64 src := (instruction_bytes hentry _ _ h).trans hb
  let s1 := pushAfter s 5
  let s2 := pushAfter s1 15
  let s3 := pushAfter s2 14
  let s4 := pushAfter s3 13
  let s5 := pushAfter s4 12
  let s6 := pushAfter s5 3
  have f1 : AgreesExcept [.reg 4, .mem (pushAddr s) 8, .rip] s s1 :=
    AgreesExcept.afterStep_push s _ _ _
  have f2 : AgreesExcept [.reg 4, .mem (pushAddr s1) 8, .rip] s1 s2 :=
    AgreesExcept.afterStep_push s1 _ _ _
  have f3 : AgreesExcept [.reg 4, .mem (pushAddr s2) 8, .rip] s2 s3 :=
    AgreesExcept.afterStep_push s2 _ _ _
  have f4 : AgreesExcept [.reg 4, .mem (pushAddr s3) 8, .rip] s3 s4 :=
    AgreesExcept.afterStep_push s3 _ _ _
  have f5 : AgreesExcept [.reg 4, .mem (pushAddr s4) 8, .rip] s4 s5 :=
    AgreesExcept.afterStep_push s4 _ _ _
  have f6 : AgreesExcept [.reg 4, .mem (pushAddr s5) 8, .rip] s5 s6 :=
    AgreesExcept.afterStep_push s5 _ _ _
  obtain ⟨e1, r1, l1, i1, p1⟩ := push_checked pre.stack (pre.avoids _ (by simp)) pre.outerBoundary
    (readyToStep pre.machine pre.bindingsSupported) pre.loaded (fun _ h => h) 5 0 (routineOffset entry + 0)
    (by simp) (by simpa only [Nat.add_zero, entry_address hentry] using pre.rip)
    (by decide) (by decide) (hsize 0 5 (by decide))
    (hbytes 0 5 (by decide) (by decide +kernel))
  obtain ⟨e2, r2, l2, i2, p2⟩ := push_checked pre.stack (pre.avoids _ (by simp)) pre.outerBoundary
    r1 l1 f1.grow 15 8 (routineOffset entry + 1) p1 i1
    (by decide) (by decide) (hsize 1 15 (by decide))
    (hbytes 1 15 (by decide) (by decide +kernel))
  obtain ⟨e3, r3, l3, i3, p3⟩ := push_checked pre.stack (pre.avoids _ (by simp)) pre.outerBoundary
    r2 l2 (f1.trans f2).grow 14 16 (routineOffset entry + 3) p2 i2
    (by decide) (by decide) (hsize 3 14 (by decide))
    (hbytes 3 14 (by decide) (by decide +kernel))
  obtain ⟨e4, r4, l4, i4, p4⟩ := push_checked pre.stack (pre.avoids _ (by simp)) pre.outerBoundary
    r3 l3 ((f1.trans f2).trans f3).grow 13 24 (routineOffset entry + 5) p3 i3
    (by decide) (by decide) (hsize 5 13 (by decide))
    (hbytes 5 13 (by decide) (by decide +kernel))
  obtain ⟨e5, r5, l5, i5, p5⟩ := push_checked pre.stack (pre.avoids _ (by simp)) pre.outerBoundary
    r4 l4 (((f1.trans f2).trans f3).trans f4).grow 12 32 (routineOffset entry + 7) p4 i4
    (by decide) (by decide) (hsize 7 12 (by decide))
    (hbytes 7 12 (by decide) (by decide +kernel))
  obtain ⟨e6, r6, l6, i6, p6⟩ := push_checked pre.stack (pre.avoids _ (by simp)) pre.outerBoundary
    r5 l5 ((((f1.trans f2).trans f3).trans f4).trans f5).grow 3 40 (routineOffset entry + 9) p5 i5
    (by decide) (by decide) (hsize 9 3 (by decide))
    (hbytes 9 3 (by decide) (by decide +kernel))
  have rip6 : s6.RIP = entry + (10 : BitVec 64) := by
    have hl : (encodePushR64 3).length = 1 := by decide
    have hi : s6.RIP = Extracted.textAddress + BitVec.ofNat 64 (routineOffset entry + 10) := by
      simpa only [hl, Nat.add_assoc] using i6
    rw [BitVec.ofNat_add, ← BitVec.add_assoc, entry_address hentry] at hi
    exact hi
  obtain ⟨t, e7, ready, effect⟩ :=
    (sub_r64_imm8_effect_step (entry + (10 : BitVec 64)) 0x48 0xec 0x70
      (by constructor <;> decide) (by decide) (by decide)).advances r6
      (code_slice hentry l6 10 _ (by decide) (by decide +kernel)) rip6
      (by
        change (entry + (10 : BitVec 64)) + (4 : BitVec 64) ≠ boundary.rip
        rw [BitVec.add_assoc]
        exact instruction_ne_boundary hentry pre.outerBoundary 14 (by decide))
  have ext : t.external = s6.external := effect.agrees.external
    (by simp [subR64Imm8Effect_components, Component.Covers])
  refine ⟨t, (((((e1.trans e2).trans e3).trans e4).trans e5).trans e6).trans e7,
    ready, ?_, ?_, ?_, ?_, ?_⟩
  · intro a b h
    rw [ext]
    exact l6 a b h
  · have he : t.RIP = (entry + (10 : BitVec 64)) + (4 : BitVec 64) := effect.rip
    rw [BitVec.add_assoc] at he
    exact he
  · have he : stackPtr t = stackPtr s6 - 112 := effect.writes
    rw [he, p6, BitVec.sub_sub]
    rfl
  · rw [ext]
    simp only [s6, s5, s4, s3, s2, s1, pushAfter_external]
    simp only [pushAddr, pushAfter_rsp, BitVec.sub_sub]
    simp (disch := decide +kernel) only [pushAfter_read_ne]
    rfl
  · apply ((((((f1.trans f2).trans f3).trans f4).trans f5).trans f6).trans effect.agrees).mono
    intro c hc
    simp only [subR64Imm8Effect_components, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with ((((((rfl | rfl | rfl) | (rfl | rfl | rfl)) |
      (rfl | rfl | rfl)) | (rfl | rfl | rfl)) | (rfl | rfl | rfl)) |
      (rfl | rfl | rfl)) | (rfl | rfl | rfl) <;>
      simp [prologueComponents, s1, s2, s3, s4, s5, pushAddr,
        pushAfter_rsp, BitVec.sub_sub, gprNumber, rexB, modrmRm]


end P256.Proofs.Sec1.SquareRoot.Montgomery
