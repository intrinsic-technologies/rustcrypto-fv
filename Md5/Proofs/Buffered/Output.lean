import Md5.Proofs.Buffered.Stores.Program
import X86Proofs.Instructions.MovLoad.Triple

namespace Md5.Proofs.Buffered

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Md5.Proofs.Block Stores

def digestOutputChanges (s : RamState) : List Component :=
  [.reg 0, .reg 1, .rip, .mem (stackPtr s + 120) 8, .mem (stackPtr s + 112) 8,
    .mem (s.regValue .rbx + 8) 8, .mem (s.regValue .rbx) 8]

theorem digest_output [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (hReady : ReadyToStep s) (hCode : CodeIn Extracted.programImage s)
    (hRip : s.RIP = 0x100260) (hOutside : ¬ InProgram boundary.rip)
    (hSource : MemReadable s (stackPtr s + 8) 16)
    (hScratch : Md5.Proofs.Memory.MemWritable s (stackPtr s + 112) 16)
    (hOutput : Md5.Proofs.Memory.MemWritable s (s.regValue .rbx) 16)
    (hScratchCode : ∀ i < 16, ¬ InProgram (stackPtr s + 112 + BitVec.ofNat 64 i))
    (hOutputCode : ∀ i < 16, ¬ InProgram (s.regValue .rbx + BitVec.ofNat 64 i)) :
    ∃ t, Advances boundary 6 s t ∧ ReadyToStep t ∧ CodeIn Extracted.programImage t ∧
      t.RIP = 0x10027b ∧ AgreesExcept (digestOutputChanges s) s t ∧
      ∀ i < 16, t.external[s.regValue .rbx + BitVec.ofNat 64 i]? =
        s.external[stackPtr s + 8 + BitVec.ofNat 64 i]? := by
  have hb0 : CodeIn (codeRange 0x100260 [0x48, 0x8b, 0x44, 0x24, 0x08]) s :=
    program_text_slice hCode 0x260 5 (by decide +kernel)
  have hp0 : LoadPre 0x100260 (fun s ↦ stackPtr s + 8) 8 s :=
    ⟨hRip, by simpa using readable_sub hSource 0 8 (by decide +kernel)⟩
  obtain ⟨s1, ha1, hr1, he1⟩ :=
    (mov_r64_m64_effect_step 0x100260 0x48 (by unfold RexWPrefix; decide +kernel)
      0 (.sib 4 none 0 (.d8 8)) (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel)
      (by decide +kernel)).advances hReady hb0 hp0
      (text_address_ne_return hOutside 0x265 (by decide +kernel))
  have hx1 : AgreesExcept [.reg 0, .rip] s s1 := he1.agrees
  have hc1 := hx1.codeIn (by simp [Component.Covers]) hCode
  have hs1 : stackPtr s1 = stackPtr s := hx1.read (n := 64) (r := 4) (by simp)
  have hm1 : s1.external = s.external := hx1.external (by simp [Component.Covers])
  have hv0 : (Operand.reg 0 : Operand 64).read s1 =
      (Operand.mem (stackPtr s + 8) : Operand 64).read s := he1.writes
  have hb1 : CodeIn (codeRange 0x100265 [0x48, 0x8b, 0x4c, 0x24, 0x10]) s1 :=
    program_text_slice hc1 0x265 5 (by decide +kernel)
  have hp1 : LoadPre 0x100265 (fun s ↦ stackPtr s + 16) 8 s1 := by
    refine ⟨he1.rip, ?_⟩
    rw [hs1]
    simpa [BitVec.add_assoc] using
      (readable_sub hSource 8 8 (by decide +kernel)).of_external_eq hm1
  obtain ⟨s2, ha2, hr2, he2⟩ :=
    (mov_r64_m64_effect_step 0x100265 0x48 (by unfold RexWPrefix; decide +kernel)
      1 (.sib 4 none 0 (.d8 16)) (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel)
      (by decide +kernel)).advances hr1 hb1 hp1
      (text_address_ne_return hOutside 0x26a (by decide +kernel))
  have hx2 : AgreesExcept [.reg 1, .rip] s1 s2 := he2.agrees
  have hc2 := hx2.codeIn (by simp [Component.Covers]) hc1
  have hv1 : (Operand.reg 1 : Operand 64).read s2 =
      (Operand.mem (stackPtr s + 16) : Operand 64).read s := by
    have h := he2.writes
    change (Operand.reg 1 : Operand 64).read s2 =
      (Operand.mem (stackPtr s1 + 16) : Operand 64).read s1 at h
    simpa only [hs1, Operand.read, hm1] using h
  have hAll2 := hx1.trans hx2
  have hv02 : (Operand.reg 0 : Operand 64).read s2 =
      (Operand.mem (stackPtr s + 8) : Operand 64).read s :=
    (hx2.read (n := 64) (r := 0) (by simp)).trans hv0
  have hs2 : stackPtr s2 = stackPtr s :=
    hAll2.read (n := 64) (r := 4) (by simp)
  have hb2 : CodeIn (codeRange 0x10026a [0x48, 0x89, 0x4c, 0x24, 0x78]) s2 :=
    program_text_slice hc2 0x26a 5 (by decide +kernel)
  have hw2 : Md5.Proofs.Memory.MemWritable s2 (stackPtr s2 + 120) 8 := by
    rw [hs2]
    simpa [BitVec.add_assoc] using
      writable_of_agrees (writable_sub hScratch 8 8 (by decide +kernel)) hAll2
  have hav2 : ∀ i < 8, ¬ InProgram (stackPtr s2 + 120 + BitVec.ofNat 64 i) := by
    intro i hi
    rw [hs2]
    have h := hScratchCode (8 + i) (by omega)
    have heq : stackPtr s + 112 + BitVec.ofNat 64 (8 + i) =
        stackPtr s + 120 + BitVec.ofNat 64 i := by
      simp only [BitVec.ofNat_eq_ofNat, BitVec.ofNat_add, BitVec.add_assoc]
      congr 1
      rw [← BitVec.add_assoc]
      rfl
    rwa [heq] at h
  have hp2 : Md5.Proofs.Memory.StorePre 0x10026a 5
      (fun s ↦ stackPtr s + 120) 8 s2 :=
    ⟨he2.rip, hw2, rangeApart_text hav2 (offset := 0x26a)
      (by decide +kernel)⟩
  obtain ⟨s3, ha3, hr3, he3⟩ :=
    (Stores.mov_m64_r64_effect_step 0x10026a 0x48
      (by unfold RexWPrefix; decide +kernel) 1 (.sib 4 none 0 (.d8 120))
      (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)).advances
      hr2 hb2 hp2
      (text_address_ne_return hOutside 0x26f (by decide +kernel))
  have hx3 : AgreesExcept [.mem (stackPtr s2 + 120) 8, .rip] s2 s3 := by
    simpa [storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr, gprIndex] using he3.agrees
  rw [hs2] at hx3
  have hc3 := he3.codeIn (store_avoids_program
    (by simp [storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr, gprIndex]) hav2) hc2
  have hAll3 := hAll2.trans hx3
  have hs3 : stackPtr s3 = stackPtr s :=
    hAll3.read (n := 64) (r := 4) (by simp)
  have hb3 : CodeIn (codeRange 0x10026f [0x48, 0x89, 0x44, 0x24, 0x70]) s3 :=
    program_text_slice hc3 0x26f 5 (by decide +kernel)
  have hw3 : Md5.Proofs.Memory.MemWritable s3 (stackPtr s3 + 112) 8 := by
    rw [hs3]
    simpa [BitVec.add_assoc] using
      writable_of_agrees (writable_sub hScratch 0 8 (by decide +kernel)) hAll3
  have hav3 : ∀ i < 8, ¬ InProgram (stackPtr s3 + 112 + BitVec.ofNat 64 i) := by
    intro i hi
    rw [hs3]
    have h := hScratchCode (0 + i) (by omega)
    simpa [BitVec.ofNat_add, ← BitVec.add_assoc] using h
  have hp3 : Md5.Proofs.Memory.StorePre 0x10026f 5
      (fun s ↦ stackPtr s + 112) 8 s3 :=
    ⟨he3.rip, hw3, rangeApart_text hav3 (offset := 0x26f)
      (by decide +kernel)⟩
  obtain ⟨s4, ha4, hr4, he4⟩ :=
    (Stores.mov_m64_r64_effect_step 0x10026f 0x48
      (by unfold RexWPrefix; decide +kernel) 0 (.sib 4 none 0 (.d8 112))
      (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)).advances
      hr3 hb3 hp3
      (text_address_ne_return hOutside 0x274 (by decide +kernel))
  have hx4 : AgreesExcept [.mem (stackPtr s3 + 112) 8, .rip] s3 s4 := by
    simpa [storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr, gprIndex] using he4.agrees
  rw [hs3] at hx4
  have hc4 := he4.codeIn (store_avoids_program
    (by simp [storeAddrAt, AddrMode.addr, AddrMode.reg64, Disp.value, stackPtr, gprIndex]) hav3) hc3
  have hAll4 := hAll3.trans hx4
  have hs4 : s4.regValue .rbx = s.regValue .rbx :=
    hAll4.read (n := 64) (r := 3) (by simp)
  have hb4 : CodeIn (codeRange 0x100274 [0x48, 0x89, 0x4b, 0x8]) s4 :=
    program_text_slice hc4 0x274 4 (by decide +kernel)
  have hw4 : Md5.Proofs.Memory.MemWritable s4 (s4.regValue .rbx + 8) 8 := by
    rw [hs4]
    simpa [BitVec.add_assoc] using
      writable_of_agrees (writable_sub hOutput 8 8 (by decide +kernel)) hAll4
  have hav4 : ∀ i < 8, ¬ InProgram (s4.regValue .rbx + 8 + BitVec.ofNat 64 i) := by
    intro i hi
    rw [hs4]
    have h := hOutputCode (8 + i) (by omega)
    simpa [BitVec.ofNat_add, ← BitVec.add_assoc] using h
  have hp4 : Md5.Proofs.Memory.StorePre 0x100274 4
      (fun s ↦ s.regValue .rbx + 8) 8 s4 :=
    ⟨he4.rip, hw4, rangeApart_text hav4 (offset := 0x274)
      (by decide +kernel)⟩
  obtain ⟨s5, ha5, hr5, he5⟩ :=
    (Stores.mov_m64_r64_effect_step 0x100274 0x48
      (by unfold RexWPrefix; decide +kernel) 1 (.base 3 (.d8 8))
      (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)).advances
      hr4 hb4 hp4
      (text_address_ne_return hOutside 0x278 (by decide +kernel))
  have hComponents5 : (movM64R64Effect 0x100274 (gprNumber 0 (rexR 0x48) 1)
      (.base 3 (.d8 8)) s4).components = [.mem (s4.regValue .rbx + 8) 8, .rip] := by
    simp only [movM64R64Effect_components, storeAddrAt, AddrMode.addr, AddrMode.reg64,
      Operand.read, State.regValue, Syntax.Reg.fin, gprIndex, Disp.value]
    rfl
  have hx5 : AgreesExcept [.mem (s4.regValue .rbx + 8) 8, .rip] s4 s5 := by
    rw [← hComponents5]
    exact he5.agrees
  rw [hs4] at hx5
  have hc5 := he5.codeIn (store_avoids_program hComponents5 hav4) hc4
  have hAll5 := hAll4.trans hx5
  have hs5 : s5.regValue .rbx = s.regValue .rbx :=
    hAll5.read (n := 64) (r := 3) (by simp)
  have hb5 : CodeIn (codeRange 0x100278 [0x48, 0x89, 0x3]) s5 :=
    program_text_slice hc5 0x278 3 (by decide +kernel)
  have hw5 : Md5.Proofs.Memory.MemWritable s5 (s5.regValue .rbx) 8 := by
    rw [hs5]
    simpa [BitVec.add_assoc] using
      writable_of_agrees (writable_sub hOutput 0 8 (by decide +kernel)) hAll5
  have hav5 : ∀ i < 8, ¬ InProgram (s5.regValue .rbx + BitVec.ofNat 64 i) := by
    intro i hi
    rw [hs5]
    have h := hOutputCode (0 + i) (by omega)
    simpa [BitVec.ofNat_add, ← BitVec.add_assoc] using h
  have hp5 : Md5.Proofs.Memory.StorePre 0x100278 3
      (fun s ↦ s.regValue .rbx) 8 s5 :=
    ⟨he5.rip, hw5, rangeApart_text hav5 (offset := 0x278)
      (by decide +kernel)⟩
  have hAddr5 : storeAddrAt 0x100278 (.base 3 .none) 3 = fun t ↦ t.regValue .rbx := by
    funext t
    simp only [storeAddrAt, AddrMode.addr, AddrMode.reg64, Operand.read,
      State.regValue, Syntax.Reg.fin, gprIndex, Disp.value]
    change (t.regValue .rbx : BitVec 64) + 0 = t.regValue .rbx
    exact BitVec.add_zero _
  obtain ⟨s6, ha6, hr6, he6⟩ :=
    (Stores.mov_m64_r64_effect_step 0x100278 0x48
      (by unfold RexWPrefix; decide +kernel) 0 (.base 3 .none)
      (by unfold AddrMode.Valid; decide +kernel) (by decide +kernel) (by decide +kernel)).advances
      hr5 hb5 (by
        change Md5.Proofs.Memory.StorePre _ 3 (storeAddrAt 0x100278 (.base 3 .none) 3) 8 s5
        rwa [hAddr5])
      (text_address_ne_return hOutside 0x27b (by decide +kernel))
  have hComponents6 : (movM64R64Effect 0x100278 (gprNumber 0 (rexR 0x48) 0)
      (.base 3 .none) s5).components = [.mem (s5.regValue .rbx) 8, .rip] := by
    simp only [movM64R64Effect_components, storeAddrAt, AddrMode.addr, AddrMode.reg64,
      Operand.read, State.regValue, Syntax.Reg.fin, gprIndex, Disp.value,
      BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    rfl
  have hx6 : AgreesExcept [.mem (s5.regValue .rbx) 8, .rip] s5 s6 := by
    rw [← hComponents6]
    exact he6.agrees
  rw [hs5] at hx6
  have hc6 := he6.codeIn (store_avoids_program hComponents6 hav5) hc5
  have hAll6 := hAll5.trans hx6
  have hLow : Bytes s6.external (s.regValue .rbx) 8
      (storedByte ((Operand.mem (stackPtr s + 8) : Operand 64).read s)) := by
    apply bytes_of_read_eq
    · exact readable_of_agrees
        (by simpa using readable_sub hOutput.readable 0 8 (by decide +kernel)) hAll6
    · have h := he6.writes
      have h' : (Operand.mem (s5.regValue .rbx) : Operand 64).read s6 =
          (Operand.reg 0 : Operand 64).read s5 := by
        change (Operand.mem (storeAddrAt 0x100278 (.base 3 .none) 3 s5) : Operand 64).read s6 =
          (Operand.reg 0 : Operand 64).read s5 at h
        rw [hAddr5] at h
        exact h
      rw [hs5] at h'
      exact h'.trans ((((hx3.trans hx4).trans hx5).read (n := 64) (r := 0) (by simp)).trans hv02)
  have hHigh5 : Bytes s5.external (s.regValue .rbx + 8) 8
      (storedByte ((Operand.mem (stackPtr s + 16) : Operand 64).read s)) := by
    apply bytes_of_read_eq
    · exact readable_of_agrees (readable_sub hOutput.readable 8 8 (by decide +kernel)) hAll5
    · have h := he5.writes
      change (Operand.mem (s4.regValue .rbx + 8) : Operand 64).read s5 =
        (Operand.reg 1 : Operand 64).read s4 at h
      rw [hs4] at h
      exact h.trans (((hx3.trans hx4).read (n := 64) (r := 1) (by simp)).trans hv1)
  have hHigh : Bytes s6.external (s.regValue .rbx + 8) 8
      (storedByte ((Operand.mem (stackPtr s + 16) : Operand 64).read s)) := by
    apply hHigh5.of_agreesExcept hx6
    intro i hi c hc hcov
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · obtain ⟨j, hj, heq⟩ := hcov
      have ha := RangeApart.offsets (s.regValue .rbx) (a := 8) (b := 0)
        (len := 8) (count := 8) (by decide +kernel) (by decide +kernel)
        (.inr (by decide +kernel)) i hi j hj
      apply ha
      simpa using heq
    · exact hcov
  have hsLow := Bytes.of_memLoad (n := 64)
    (readable_sub hSource 0 8 (by decide +kernel)).mem
  have hsHigh := Bytes.of_memLoad (n := 64)
    (readable_sub hSource 8 8 (by decide +kernel)).mem
  simp only [BitVec.add_zero] at hsLow
  have hsHigh' : Bytes s.external (stackPtr s + 8 + 8) 8
      (storedByte ((Operand.mem (stackPtr s + 16) : Operand 64).read s)) := by
    simpa [BitVec.add_assoc, Operand.read] using hsHigh
  have hd := (hsLow.append hsHigh').copy_sub (hLow.append hHigh) 0 16
    (by decide +kernel) (by simpa using Bytes.of_isSome hSource.mem)
  refine ⟨s6, ha1.trans (ha2.trans (ha3.trans (ha4.trans (ha5.trans ha6)))),
    hr6, hc6, he6.rip, hAll6.mono (by simp [digestOutputChanges]), ?_⟩
  intro i hi
  have hdi := hd i hi
  simp only [BitVec.add_zero] at hdi
  rw [hdi]
  exact (Bytes.of_isSome hSource.mem i hi).symm

end Md5.Proofs.Buffered
