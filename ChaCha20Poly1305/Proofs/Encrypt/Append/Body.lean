import ChaCha20Poly1305.Proofs.Encrypt.Append.Loads
import X86Proofs.Instructions.Sub.Generated.RR.Triple
import X86Proofs.Instructions.Test.Generated.RR.Triple
import X86Proofs.Instructions.Add.Generated.RR.Triple

namespace ChaCha20Poly1305.Proofs.Encrypt

open ChaCha20Poly1305.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Wrapper MemoryRoutines.Machine

def appendBodyChanges : List Component :=
  [.reg 0, .reg 2, .reg 3, .reg 7, .reg 14, .reg 15, .flags, .rip]

theorem append_loads [Bindings] {s u : RamState} {buffer : BitVec 64}
    {length : Nat} {tag : Vector UInt8 16} {boundary : ReturnBoundary}
    (pre : AppendPre s buffer length tag) (outside : ¬ InProgram boundary.rip)
    (frame : MemoryWriteFrame s u #v[Stack.region s 48])
    (ready : ReadyToStep u) (code : CodeIn Extracted.programImage u)
    (rip : u.RIP = 0x101fb8) (rdi : rd u 7 = s.regValue .rdi)
    (rdx : rd u 2 = 16) :
    ∃ t, Advances boundary 4 u t ∧ GTrack appendBodyChanges u t ∧
      t.RIP = 0x101fc5 ∧ rd t 3 = 16 ∧ rd t 14 = s.regValue .rdi ∧
      rd t 0 = BitVec.ofNat 64 (length + 16) ∧ rd t 15 = BitVec.ofNat 64 length ∧
      rd t 2 = 16 := by
  have cap := append_descriptor_word pre frame (offset := 0) (by omega) pre.capacity
  have len := append_descriptor_word pre frame (offset := 16) (by omega) pre.lengthWord
  simp only [BitVec.add_zero] at cap
  have T0 : GTrack appendBodyChanges u u := ⟨ready, code, AgreesExcept.refl _ _⟩
  obtain ⟨u1, a1, T1, e1⟩ := gtrack_step
    (mov_r64_r64_effect_step 0x101fb8 0x48 0xd3 (by unfold RexWPrefix; decide) (by decide))
    T0 (program_text_slice T0.code 0x1fb8 3 (by decide +kernel)) rip
    (code_ne_boundary outside 0x1fbb (by omega)) (by fits [appendBodyChanges])
  change (movR64R64Effect 0x101fb8 3 2 u).Holds u u1 at e1
  have v1 : rd u1 3 = 16 := e1.writes.trans rdx
  obtain ⟨u2, a2, T2, e2⟩ := gtrack_step
    (mov_r64_r64_effect_step 0x101fbb 0x49 0xfe (by unfold RexWPrefix; decide) (by decide))
    T1 (program_text_slice T1.code 0x1fbb 3 (by decide +kernel)) e1.rip
    (code_ne_boundary outside 0x1fbe (by omega)) (by fits [appendBodyChanges])
  change (movR64R64Effect 0x101fbb 14 7 u1).Holds u1 u2 at e2
  have v2 : rd u2 14 = s.regValue .rdi := by
    exact (show rd u2 14 = rd u1 7 from e2.writes).trans
      ((e1.agrees.read (r := 7) (n := 64) (by simp)).trans rdi)
  have d2 : rd u2 7 = s.regValue .rdi := by
    exact ((e1.agrees.trans e2.agrees).read (r := 7) (n := 64) (by simp)).trans rdi
  have c2 : MemReadable u2 (s.regValue .rdi) 8 :=
    ⟨cap.1.low, fun i hi => T2.agrees.grow _ (cap.1.mem i hi)⟩
  have A2 : ∀ x, (AddrMode.base 7 .none).addr u2 x = s.regValue .rdi := by
    intro x
    change rd u2 7 + 0 = _
    bv_omega
  obtain ⟨u3, a3, T3, e3⟩ := gtrack_step
    (mov_r64_m64_effect_step 0x101fbe 0x48 (by unfold RexWPrefix; decide) 0
      (.base 7 .none) (by decide) (by decide) (by decide))
    T2 (program_text_slice T2.code 0x1fbe 3 (by decide +kernel))
    ⟨e2.rip, by rw [A2]; exact c2⟩
    (code_ne_boundary outside 0x1fc1 (by omega)) (by fits [appendBodyChanges])
  change (movR64M64Effect 0x101fbe 0 (.base 7 .none) u2).Holds u2 u3 at e3
  have v3 : rd u3 0 = BitVec.ofNat 64 (length + 16) := by
    rw [show rd u3 0 = (Operand.mem ((AddrMode.base 7 .none).addr u2 _) : Operand 64).read u2 from
        e3.writes, A2]
    change wd u2 (s.regValue .rdi) = _
    rw [gload T2.agrees (by simp [appendBodyChanges, Component.Covers])]
    exact cap.2
  have d3 : rd u3 7 = s.regValue .rdi := (e3.agrees.read (by simp)).trans d2
  have A3 : ∀ x, (AddrMode.base 7 (.d8 16)).addr u3 x = s.regValue .rdi + BitVec.ofNat 64 16 := by
    intro x
    change rd u3 7 + (16 : BitVec 8).signExtend 64 = _
    rw [d3]
    rfl
  have l3 : MemReadable u3 (s.regValue .rdi + BitVec.ofNat 64 16) 8 :=
    ⟨len.1.low, fun i hi => T3.agrees.grow _ (len.1.mem i hi)⟩
  obtain ⟨u4, a4, T4, e4⟩ := gtrack_step
    (mov_r64_m64_effect_step 0x101fc1 0x4c (by unfold RexWPrefix; decide) 7
      (.base 7 (.d8 16)) (by decide) (by decide) (by decide))
    T3 (program_text_slice T3.code 0x1fc1 4 (by decide +kernel))
    ⟨e3.rip, by rw [A3]; exact l3⟩
    (code_ne_boundary outside 0x1fc5 (by omega)) (by fits [appendBodyChanges])
  change (movR64M64Effect 0x101fc1 15 (.base 7 (.d8 16)) u3).Holds u3 u4 at e4
  have v4 : rd u4 15 = BitVec.ofNat 64 length := by
    rw [show rd u4 15 = (Operand.mem ((AddrMode.base 7 (.d8 16)).addr u3 _) : Operand 64).read u3
        from e4.writes, A3]
    change wd u3 (s.regValue .rdi + BitVec.ofNat 64 16) = _
    rw [gload T3.agrees (by simp [appendBodyChanges, Component.Covers])]
    exact len.2
  refine ⟨u4, a1.trans (a2.trans (a3.trans a4)), T4, e4.rip, ?_, ?_, ?_, v4, ?_⟩
  · exact ((e2.agrees.trans e3.agrees).trans e4.agrees).read (by simp) |>.trans v1
  · exact (e3.agrees.trans e4.agrees).read (by simp) |>.trans v2
  · exact e4.agrees.read (by simp) |>.trans v3
  · exact (((e1.agrees.trans e2.agrees).trans e3.agrees).trans e4.agrees).read
      (by simp) |>.trans rdx

theorem append_capacity [Bindings] {u v : RamState} {length : Nat}
    {boundary : ReturnBoundary} (outside : ¬ InProgram boundary.rip)
    (T0 : GTrack appendBodyChanges u v) (rip : v.RIP = 0x101fc5)
    (cap : rd v 0 = BitVec.ofNat 64 (length + 16))
    (len : rd v 15 = BitVec.ofNat 64 length) (rdx : rd v 2 = 16)
    (rbx : rd v 3 = 16) :
    ∃ t, Advances boundary 5 v t ∧ GTrack appendBodyChanges u t ∧
      t.RIP = 0x101fd2 ∧
      AgreesExcept [.reg 0, .flags, .rip] v t := by
  obtain ⟨u1, a1, T1, e1⟩ := gtrack_step
    (sub_r64_r64_effect_step 0x101fc5 0x4c 0xf8 (by unfold RexWPrefix; decide) (by decide))
    T0 (program_text_slice T0.code 0x1fc5 3 (by decide +kernel)) rip
    (code_ne_boundary outside 0x1fc8 (by omega))
    (by fits [appendBodyChanges, subR64R64Effect_components])
  change (subR64R64Effect 0x101fc5 0 15 v).Holds v u1 at e1
  have v1 : rd u1 0 = 16 := by
    rw [show rd u1 0 = rd v 0 - rd v 15 from e1.writes, cap, len, BitVec.ofNat_add]
    bv_omega
  have d1 : rd u1 2 = 16 := (e1.agrees.read (by simp)).trans rdx
  obtain ⟨u2, a2, T2, e2⟩ := gtrack_step
    (cmp_r64_r64_effect_step 0x101fc8 0x48 0xc2 (by unfold RexWPrefix; decide) (by decide))
    T1 (program_text_slice T1.code 0x1fc8 3 (by decide +kernel)) e1.rip
    (code_ne_boundary outside 0x1fcb (by omega)) (by fits [appendBodyChanges])
  change (cmpR64R64Effect 0x101fc8 2 0 u1).Holds u1 u2 at e2
  have hc2 : condHolds 7 (StatusFlags.ofRFLAGS u2.RFLAGS) = false := by
    have hz := e2.flags
    simp only [Effect.FlagsHold, cmpR64R64Effect] at hz
    obtain ⟨_, _, _, hz, _⟩ := hz
    change (StatusFlags.ofRFLAGS u2.RFLAGS).ZF = (cmpSpec (rd u1 2) (rd u1 0)).ZF at hz
    rw [d1, v1] at hz
    have he : (StatusFlags.ofRFLAGS u2.RFLAGS).ZF = true := hz
    rw [condHolds_7, he]
    simp
  obtain ⟨u3, a3, T3, e3⟩ := gtrack_step (jcc_rel8_effect_step 0x101fcb 7 0x2a)
    T2 (program_text_slice T2.code 0x1fcb 2 (by decide +kernel))
    ⟨e2.rip, fun _ => by decide⟩
    (by simp only [jccEffect, branchEffect, hc2, Bool.false_eq_true, ↓reduceIte]
        exact code_ne_boundary outside 0x1fcd (by omega))
    (by fits [appendBodyChanges])
  have rip3 : u3.RIP = 0x101fcd := by
    rw [e3.rip]
    simp only [jccEffect, branchEffect, hc2, Bool.false_eq_true, ↓reduceIte]
    rfl
  have b3 : rd u3 3 = 16 :=
    (((e1.agrees.trans e2.agrees).trans e3.agrees).read (by simp [jccEffect])).trans rbx
  obtain ⟨u4, a4, T4, e4⟩ := gtrack_step
    (test_r64_r64_effect_step 0x101fcd 0x48 0xdb (by unfold RexWPrefix; decide) (by decide))
    T3 (program_text_slice T3.code 0x1fcd 3 (by decide +kernel)) rip3
    (code_ne_boundary outside 0x1fd0 (by omega))
    (by fits [appendBodyChanges, testR64R64Effect_components])
  change (testR64R64Effect 0x101fcd 3 3 u3).Holds u3 u4 at e4
  have hc4 : condHolds 4 (StatusFlags.ofRFLAGS u4.RFLAGS) = false := by
    have hz := e4.flags
    simp only [Effect.FlagsHold, testR64R64Effect] at hz
    obtain ⟨_, _, _, hz, _⟩ := hz
    change (StatusFlags.ofRFLAGS u4.RFLAGS).ZF = ((rd u3 3 &&& rd u3 3) == 0) at hz
    rw [b3] at hz
    rw [condHolds_4]
    exact hz
  obtain ⟨u5, a5, T5, e5⟩ := gtrack_step (jcc_rel8_effect_step 0x101fd0 4 0x10)
    T4 (program_text_slice T4.code 0x1fd0 2 (by decide +kernel))
    ⟨e4.rip, fun _ => by decide⟩
    (by simp only [jccEffect, branchEffect, hc4, Bool.false_eq_true, ↓reduceIte]
        exact code_ne_boundary outside 0x1fd2 (by omega))
    (by fits [appendBodyChanges])
  refine ⟨u5, a1.trans (a2.trans (a3.trans (a4.trans a5))), T5, ?_, ?_⟩
  · rw [e5.rip]
    simp only [jccEffect, branchEffect, hc4, Bool.false_eq_true, ↓reduceIte]
    rfl
  · apply (((e1.agrees.trans e2.agrees).trans e3.agrees).trans e4.agrees).trans e5.agrees |>.mono
    intro c hc
    simpa [jccEffect, List.mem_cons, or_assoc, or_left_comm, or_comm] using hc

theorem append_copy_setup [Bindings] {s u v : RamState} {buffer : BitVec 64}
    {length : Nat} {tag : Vector UInt8 16} {boundary : ReturnBoundary}
    (pre : AppendPre s buffer length tag) (outside : ¬ InProgram boundary.rip)
    (frame : MemoryWriteFrame s v #v[Stack.region s 48])
    (T0 : GTrack appendBodyChanges u v) (rip : v.RIP = 0x101fd2)
    (desc : rd v 14 = s.regValue .rdi) (len : rd v 15 = BitVec.ofNat 64 length)
    (count : rd v 3 = 16) :
    ∃ t, Advances boundary 3 v t ∧ GTrack appendBodyChanges u t ∧
      t.RIP = 0x101fdc ∧ rd t 7 = buffer + BitVec.ofNat 64 length ∧ rd t 2 = 16 ∧
      AgreesExcept [.reg 7, .reg 2, .flags, .rip] v t := by
  have ptr := append_descriptor_word pre frame (offset := 8) (by omega) pre.pointer
  have A0 : ∀ x, (AddrMode.base 14 (.d8 8)).addr v x =
      s.regValue .rdi + BitVec.ofNat 64 8 := by
    intro x
    change rd v 14 + (8 : BitVec 8).signExtend 64 = _
    rw [desc]
    rfl
  obtain ⟨u1, a1, T1, e1⟩ := gtrack_step
    (mov_r64_m64_effect_step 0x101fd2 0x49 (by unfold RexWPrefix; decide) 7
      (.base 14 (.d8 8)) (by decide) (by decide) (by decide))
    T0 (program_text_slice T0.code 0x1fd2 4 (by decide +kernel))
    ⟨rip, by rw [A0]; exact ptr.1⟩
    (code_ne_boundary outside 0x1fd6 (by omega)) (by fits [appendBodyChanges])
  change (movR64M64Effect 0x101fd2 7 (.base 14 (.d8 8)) v).Holds v u1 at e1
  have v1 : rd u1 7 = buffer := by
    rw [show rd u1 7 = (Operand.mem ((AddrMode.base 14 (.d8 8)).addr v _) : Operand 64).read v from
        e1.writes, A0]
    exact ptr.2
  have l1 : rd u1 15 = BitVec.ofNat 64 length := (e1.agrees.read (by simp)).trans len
  obtain ⟨u2, a2, T2, e2⟩ := gtrack_step
    (add_r64_r64_effect_step 0x101fd6 0x4c 0xff (by unfold RexWPrefix; decide) (by decide))
    T1 (program_text_slice T1.code 0x1fd6 3 (by decide +kernel)) e1.rip
    (code_ne_boundary outside 0x1fd9 (by omega))
    (by fits [appendBodyChanges, addR64R64Effect_components])
  change (addR64R64Effect 0x101fd6 7 15 u1).Holds u1 u2 at e2
  have v2 : rd u2 7 = buffer + BitVec.ofNat 64 length := by
    rw [show rd u2 7 = rd u1 7 + rd u1 15 from e2.writes, v1, l1]
  have b2 : rd u2 3 = 16 := ((e1.agrees.trans e2.agrees).read (by simp)).trans count
  obtain ⟨u3, a3, T3, e3⟩ := gtrack_step
    (mov_r64_r64_effect_step 0x101fd9 0x48 0xda (by unfold RexWPrefix; decide) (by decide))
    T2 (program_text_slice T2.code 0x1fd9 3 (by decide +kernel)) e2.rip
    (code_ne_boundary outside 0x1fdc (by omega)) (by fits [appendBodyChanges])
  change (movR64R64Effect 0x101fd9 2 3 u2).Holds u2 u3 at e3
  refine ⟨u3, a1.trans (a2.trans a3), T3, e3.rip, ?_, e3.writes.trans b2, ?_⟩
  · exact (e3.agrees.read (by simp)).trans v2
  · apply ((e1.agrees.trans e2.agrees).trans e3.agrees).mono
    intro c hc
    simpa [List.mem_cons, or_assoc, or_left_comm, or_comm] using hc

end ChaCha20Poly1305.Proofs.Encrypt
