import Sha3.Proofs.Update.Division.Length
import Sha3.Proofs.Update.Layout
import X86Proofs.Instructions.Branch.Triple
import X86Proofs.Instructions.NopMem.Triple

namespace Sha3.Proofs.Update.Division

open X86 X86.Machine X86.UserProcess X86Proofs Sha3.Spec.Program

def branchPC : Variant → BitVec 64
  | .sha224 => 0x1009b2 | .sha256 => 0x100695
  | .sha384 => 0x1003bb | .sha512 => 0x10010f

def branchDisp : Variant → BitVec 32
  | .sha224 => 0xc5 | .sha256 => 0xc4 | .sha384 => 0x8b | .sha512 => 0x6b

def branchLength : Variant → Nat
  | .sha512 => 2 | _ => 6

def lengthSteps : Variant → Nat
  | .sha224 => 8 | .sha256 => 9 | .sha384 => 7 | .sha512 => 8

def setupPC (v : Variant) : BitVec 64 := branchPC v + BitVec.ofNat 64 (branchLength v)

def nopPC (v : Variant) : BitVec 64 := setupPC v + 6

def nopPrefixes : Variant → List UInt8
  | .sha256 => [0x66, 0x66, 0x66, 0x66, 0x66, 0x66, 0x2e]
  | _ => [0x66]

def nopBytes (v : Variant) : List UInt8 :=
  match v with
  | .sha224 => [0x66, 0x90]
  | _ => encodeNopM (nopPrefixes v) (.sib 0 (some 0) 0 (.d32 0))

def nopLength : Variant → Nat
  | .sha224 => 2 | .sha256 => 15 | _ => 9

def setupClobbers : List Component := [.reg 14, .reg 5, .rip]

theorem length_setup [Bindings] (v : Variant) (boundary : ReturnBoundary)
    (n : BitVec 64) (hn : n.toNat < 2 ^ 32) (s : RamState)
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (hb : ¬ InProgram boundary.rip) (ip : s.RIP = divisionAddress v)
    (input : (Operand.reg 12 : Operand 64).read s = n) :
    ∃ t, Advances boundary (lengthSteps v) s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP = branchPC v ∧ Length.Registers v.rate 13 n t ∧
      AgreesExcept (Length.clobbers 13) s t := by
  cases v with
  | sha224 => exact Length.sha3_224_length_setup boundary n hn s ready loaded hb ip input
  | sha256 => exact Length.sha3_256_length_setup boundary n hn s ready loaded hb ip input
  | sha384 => exact Length.sha3_384_length_setup boundary n hn s ready loaded hb ip input
  | sha512 => exact Length.sha3_512_length_setup boundary n hn s ready loaded hb ip input

def branchBytes (v : Variant) : List UInt8 :=
  match v with
  | .sha512 => [0x72, 0x6b]
  | _ => 0x0f :: jccOpcode32 2 :: immBytes 32 (branchDisp v)

def branchStep (v : Variant) : RamState → Effect :=
  jccEffect (branchPC v) (branchLength v) 2 ((branchDisp v).signExtend 64)

private theorem branch_image (v : Variant) :
    ∀ x ∈ codeRange (branchPC v) (branchBytes v),
      x.1.toNat < Prelude.userAddressLimit ∧
        Extracted.programSections.fetchByte x.1 = some x.2 := by
  cases v <;> decide +kernel

private theorem branch_step [Bindings] (v : Variant) :
    StepEffect (fun s ↦ s.RIP = branchPC v)
      (codeRange (branchPC v) (branchBytes v)) (branchStep v) := by
  cases v with
  | sha224 | sha256 | sha384 =>
    apply (jcc_rel32_effect_step _ 2 _).mono_pre
    intro s hs
    exact ⟨hs, fun _ ↦ by decide +kernel⟩
  | sha512 =>
    apply (jcc_rel8_effect_step _ 2 0x6b).mono_pre
    intro s hs
    exact ⟨hs, fun _ ↦ by decide +kernel⟩

private theorem branch_target (v : Variant) :
    branchTarget (branchPC v) (branchLength v) ((branchDisp v).signExtend 64) =
      tailAddress v := by cases v <;> decide +kernel

private theorem jb [Bindings] (v : Variant) (boundary : ReturnBoundary) (s : RamState)
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (hb : ¬ InProgram boundary.rip) (ip : s.RIP = branchPC v) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP = (if (StatusFlags.ofRFLAGS s.RFLAGS).CF then tailAddress v else setupPC v) ∧
      AgreesExcept [.rip] s t := by
  obtain ⟨t, ht, rt, lt, et, _, _⟩ := advanceScalar
    (cs := [.rip]) (branch_step v) (branch_image v)
    (by intro t; simp [branchStep, jccEffect, branchEffect])
    (by intro a b h; rfl)
    (by intro t; simp [branchStep, jccEffect, branchEffect_components])
    (by simp [Component.Covers])
    (by
      intro t
      dsimp only [branchStep, jccEffect, branchEffect]
      split <;> apply Permutation.inProgram_permutation_address <;> cases v <;> decide +kernel)
    ready loaded hb ip (Obs.refl s)
  refine ⟨t, ht, rt, lt, ?_, et.agrees⟩
  simpa only [branchStep, jccEffect, branchEffect, condHolds, BitVec.reduceToNat,
    branch_target, setupPC] using et.rip

private theorem compare_cf (v : Variant) (n : BitVec 64) (hn : n.toNat < 2 ^ 32)
    {s : RamState} (registers : Length.Registers v.rate 13 n s) :
    (StatusFlags.ofRFLAGS s.RFLAGS).CF = decide (n.toNat < v.rate) := by
  have h := registers.comparison.1
  change (StatusFlags.ofRFLAGS s.RFLAGS).CF =
    decide ((BitVec.ofNat 64 (v.rate * (n.toNat / v.rate))).toNat <
      (BitVec.ofNat 64 v.rate).toNat) at h
  rw [h]
  congr 1
  have hle : v.rate * (n.toNat / v.rate) ≤ n.toNat := Nat.mul_div_le _ _
  have hrate := v.rate_le
  simp only [BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (by omega : v.rate * (n.toNat / v.rate) < 2 ^ 64),
    Nat.mod_eq_of_lt (by omega : v.rate < 2 ^ 64)]
  apply propext
  cases v <;> simp only [Variant.rate, Variant.lanes] <;> omega

private theorem setup_nomem : ∀ c ∈ setupClobbers, ∀ a, ¬ c.Covers a := by
  simp [setupClobbers, Component.Covers]

private theorem nop_step [Bindings] (v : Variant) :
    StepEffect (fun s ↦ s.RIP = nopPC v) (codeRange (nopPC v) (nopBytes v))
      (fun _ ↦ nopEffect (nopPC v) (nopLength v)) := by
  cases v with
  | sha224 => exact nop_66_effect_step _
  | sha256 | sha384 | sha512 =>
    exact nop_m_effect_step _ _ (by decide +kernel) (by decide +kernel)
      _ (by decide +kernel) (by decide +kernel) (by decide +kernel)

private theorem setup [Bindings] (v : Variant) (boundary : ReturnBoundary) (s : RamState)
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (hb : ¬ InProgram boundary.rip) (ip : s.RIP = setupPC v) :
    ∃ t, Advances boundary 3 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP = fullBlockAddress v ∧
      (Operand.reg 5 : Operand 64).read t = (Operand.reg 13 : Operand 64).read s ∧
      (Operand.reg 14 : Operand 64).read t = (Operand.reg 3 : Operand 64).read s ∧
      AgreesExcept setupClobbers s t := by
  obtain ⟨s1, h1, r1, l1, e1, o1, a1⟩ := advanceScalar
    (effect := movR64R64Effect (setupPC v) 5 13) (cs := setupClobbers)
    (mov_r64_r64_effect_step _ 0x4c 0xed
      (by unfold RexWPrefix; decide +kernel) (by decide +kernel))
    (by cases v <;> decide +kernel)
    (by intro t; simp [movR64R64Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [movR64R64Effect, h.read_reg])
    (by intro t; simp [movR64R64Effect_components, setupClobbers]) setup_nomem
    (by
      intro t
      dsimp only [movR64R64Effect]
      apply Permutation.inProgram_permutation_address <;> cases v <;> decide +kernel)
    ready loaded hb ip (Obs.refl s)
  obtain ⟨s2, h2, r2, l2, e2, o2, a2⟩ := advanceScalar
    (effect := movR64R64Effect (setupPC v + 3) 14 3) (cs := setupClobbers)
    (mov_r64_r64_effect_step _ 0x49 0xde
      (by unfold RexWPrefix; decide +kernel) (by decide +kernel))
    (by cases v <;> decide +kernel)
    (by intro t; simp [movR64R64Effect, Write.Full, Operand.Full])
    (by intro a b h; simp only [movR64R64Effect, h.read_reg])
    (by intro t; simp [movR64R64Effect_components, setupClobbers]) setup_nomem
    (by
      intro t
      dsimp only [movR64R64Effect]
      apply Permutation.inProgram_permutation_address <;> cases v <;> decide +kernel)
    r1 l1 hb e1.rip o1
  have ip2 : s2.RIP = nopPC v := by
    simpa only [nopPC, movR64R64Effect, BitVec.add_assoc, BitVec.reduceAdd,
      BitVec.ofNat_eq_ofNat] using e2.rip
  obtain ⟨t, h3, r3, l3, e3, o3, a3⟩ := advanceScalar
    (cs := setupClobbers) (nop_step v)
    (by cases v <;> decide +kernel)
    (by intro t; simp [nopEffect]) (by intro a b h; rfl)
    (by intro t; simp [setupClobbers]) setup_nomem
    (by
      intro t
      dsimp only [nopEffect]
      apply Permutation.inProgram_permutation_address <;> cases v <;> decide +kernel)
    r2 l2 hb ip2 o2
  refine ⟨t, h1.trans (h2.trans h3), r3, l3, ?_, ?_, ?_, ?_⟩
  · have h := e3.rip
    cases v <;> exact h
  · have h := (o3.read (Operand.reg 5 : Operand 64) trivial).symm
    x86_norm [movR64R64Effect, nopEffect] at h
    exact h
  · have h := (o3.read (Operand.reg 14 : Operand 64) trivial).symm
    x86_norm [movR64R64Effect, nopEffect] at h
    exact h
  · apply (a1.trans (a2.trans a3)).mono
    intro c hc
    simpa only [List.mem_append, or_self] using hc

private theorem preserve_lengths (v : Variant) (n : BitVec 64) {s t : RamState}
    (h : AgreesExcept setupClobbers s t)
    (registers : Length.Registers v.rate 13 n s) : Length.Registers v.rate 13 n t := by
  refine ⟨?_, ?_, ?_⟩
  · rw [h.read (by simp [setupClobbers])]
    exact registers.full
  · rw [h.read (by simp [setupClobbers])]
    exact registers.remaining
  · rw [h.rflags (by simp [setupClobbers]) (by simp [setupClobbers])]
    exact registers.comparison

theorem initial_taken [Bindings] (v : Variant) (boundary : ReturnBoundary)
    (n : BitVec 64) (hn : n.toNat < 2 ^ 32) (s : RamState)
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (hb : ¬ InProgram boundary.rip) (ip : s.RIP = branchPC v)
    (registers : Length.Registers v.rate 13 n s) (short : n.toNat < v.rate) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP = tailAddress v ∧ Length.Registers v.rate 13 n t ∧
      AgreesExcept [.rip] s t := by
  obtain ⟨t, ht, rt, lt, ipt, ag⟩ := jb v boundary s ready loaded hb ip
  refine ⟨t, ht, rt, lt, ?_,
    preserve_lengths v n (ag.mono (by simp [setupClobbers])) registers, ag⟩
  simpa [compare_cf v n hn registers, short] using ipt

theorem initial_fallthrough [Bindings] (v : Variant) (boundary : ReturnBoundary)
    (n : BitVec 64) (hn : n.toNat < 2 ^ 32) (s : RamState)
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (hb : ¬ InProgram boundary.rip) (ip : s.RIP = branchPC v)
    (registers : Length.Registers v.rate 13 n s) (long : v.rate ≤ n.toNat) :
    ∃ t, Advances boundary 4 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      t.RIP = fullBlockAddress v ∧ Length.Registers v.rate 13 n t ∧
      (Operand.reg 5 : Operand 64).read t = BitVec.ofNat 64 (v.rate * (n.toNat / v.rate)) ∧
      (Operand.reg 14 : Operand 64).read t = (Operand.reg 3 : Operand 64).read s ∧
      AgreesExcept setupClobbers s t := by
  obtain ⟨u, hu, ru, lu, ipu, au⟩ := jb v boundary s ready loaded hb ip
  have next : u.RIP = setupPC v := by
    simpa [compare_cf v n hn registers, Nat.not_lt.mpr long] using ipu
  obtain ⟨t, ht, rt, lt, ipt, count, source, ag⟩ := setup v boundary u ru lu hb next
  have frame : AgreesExcept setupClobbers s t := (au.trans ag).mono (by
    intro c hc
    simpa [setupClobbers, or_comm, or_left_comm, or_assoc] using hc)
  refine ⟨t, hu.trans ht, rt, lt, ipt, preserve_lengths v n frame registers, ?_, ?_, frame⟩
  · rw [count, au.read (by simp)]
    exact registers.full
  · rw [source, au.read (by simp)]

end Sha3.Proofs.Update.Division
