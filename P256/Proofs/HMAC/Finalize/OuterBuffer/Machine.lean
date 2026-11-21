import P256.Proofs.HMAC.Finalize.OuterBuffer.Append
import P256.Proofs.HMAC.Finalize.OuterBuffer.Machine.Head
import P256.Proofs.HMAC.Finalize.OuterBuffer.Machine.Copy
import P256.Proofs.HMAC.Finalize.OuterBuffer.Machine.Store
import P256.Proofs.HMAC.Finalize.OuterBuffer.Machine.Tail
import P256.Proofs.Common.Instructions.ByteLogic.OrImmediate
import P256.Proofs.Common.EffectCompose.Memory
import P256.Proofs.Common.Field.Operations.Run.Compose

set_option autoImplicit false

namespace P256.Proofs.HMAC.Finalize.OuterBuffer.Machine

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program
open P256.Proofs.Program.ScalarFrame (workRegion)
open P256.Proofs.Common
open P256.Proofs.Common.Field (AdvanceTriple)

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x101182
  readable : MemReadable s (stackPtr s + 8) 32
  writable : Common.Instructions.CrossPageStore.Writable s (stackPtr s + 176) 64
  codeApart : RangeApart (stackPtr s + 176) 64 0x101182 208
  position : memLoad s.external (stackPtr s + 239) 8 = 0

def bytes : List UInt8 :=
  [0x44,0xf,0xb6,0xbc,0x24,0xef,0x0,0x0,0x0,0x49,0x83,0xff,0x1f,0x77,0x42,0x48,0x8b,0x44,0x24,0x20,0x4a,0x89,0x84,0x3c,0xc8,0x0,0x0,0x0,0x48,0x8b,0x44,0x24,0x18,0x4a,0x89,0x84,0x3c,0xc0,0x0,0x0,0x0,0x48,0x8b,0x44,0x24,0x8,0x48,0x8b,0x4c,0x24,0x10,0x4a,0x89,0x8c,0x3c,0xb8,0x0,0x0,0x0,0x4a,0x89,0x84,0x3c,0xb0,0x0,0x0,0x0,0x41,0x80,0xcf,0x20,0x44,0x88,0xbc,0x24,0xef,0x0,0x0,0x0,0xeb,0x6d,0xba,0x40,0x0,0x0,0x0,0x4c,0x29,0xfa,0x4c,0x8d,0x2c,0x14,0x49,0x83,0xc5,0x8,0x4a,0x8d,0x3c,0x3c,0x48,0x81,0xc7,0xb0,0x0,0x0,0x0,0x49,0x83,0xc7,0xe0,0x48,0x8d,0x74,0x24,0x8,0x48,0x8d,0x2d,0x32,0xb7,0x1,0x0,0xff,0xd5,0x48,0xff,0x84,0x24,0x10,0x1,0x0,0x0,0x4c,0x8d,0xa4,0x24,0xb0,0x0,0x0,0x0,0xba,0x1,0x0,0x0,0x0,0x4c,0x89,0xf7,0x4c,0x89,0xe6,0xe8,0x70,0x47,0x1,0x0,0x48,0xbe,0xc0,0xff,0xff,0xff,0xff,0xff,0xff,0x7f,0x4c,0x21,0xfe,0x4c,0x1,0xee,0x44,0x88,0xbc,0x24,0xef,0x0,0x0,0x0,0x4c,0x89,0xe7,0x4c,0x89,0xfa,0xff,0xd5,0x48,0x8d,0x7c,0x24,0x48,0x48,0x8d,0xb4,0x24,0xb0,0x0,0x0,0x0,0xb9,0xd,0x0,0x0,0x0]

def effect (s : RamState) : Effect :=
  { rip := 0x101252
    writes := [⟨(.reg 0 : Operand 64), memLoad s.external (stackPtr s + 8) 64⟩,
      ⟨(.reg 1 : Operand 64), 13⟩,
      ⟨(.reg 15 : Operand 64), 32⟩,
      ⟨(.reg 7 : Operand 64), stackPtr s + 72⟩,
      ⟨(.reg 6 : Operand 64), stackPtr s + 176⟩,
      ⟨(.mem (stackPtr s + 176) : Operand 64), memLoad s.external (stackPtr s + 8) 64⟩,
      ⟨(.mem (stackPtr s + 184) : Operand 64), memLoad s.external (stackPtr s + 16) 64⟩,
      ⟨(.mem (stackPtr s + 192) : Operand 64), memLoad s.external (stackPtr s + 24) 64⟩,
      ⟨(.mem (stackPtr s + 200) : Operand 64), memLoad s.external (stackPtr s + 32) 64⟩,
      ⟨(.mem (stackPtr s + 239) : Operand 8), 32⟩]
    flags := some ⟨none,none,none,none,none,none⟩ }

theorem code {s : RamState} (loaded : ProgramLoaded s) :
    CodeIn (codeRange 0x101182 bytes) s :=
  programText_slice (programLoaded_codeIn loaded) 0x1182 bytes
    (by decide +kernel) (by decide +kernel)

theorem Pre.writable_at {s : RamState} (hp : Pre s) (offset len : Nat)
    (bound : offset + len ≤ 64) :
    Common.Instructions.CrossPageStore.Writable s (stackPtr s + BitVec.ofNat 64 (176 + offset)) len := by
  simpa only [BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using hp.writable.add offset bound

theorem Pre.apart_at {s : RamState} (hp : Pre s) (offset len codeOffset codeLen : Nat)
    (bound : offset + len ≤ 64) (codeBound : codeOffset + codeLen ≤ 208) :
    RangeApart (stackPtr s + BitVec.ofNat 64 (176 + offset)) len
      (0x101182 + BitVec.ofNat 64 codeOffset) codeLen := by
  intro i hi j hj
  simpa only [BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat] using
    hp.codeApart (offset+i) (by omega) (codeOffset+j) (by omega)

theorem Pre.readable_at {s : RamState} (hp : Pre s) (offset : Nat) (bound : offset + 8 ≤ 32) :
    MemReadable s (stackPtr s + BitVec.ofNat 64 (8 + offset)) 8 := by
  have addr : stackPtr s + BitVec.ofNat 64 (8 + offset) = stackPtr s + 8 + BitVec.ofNat 64 offset := by
    simp only [BitVec.ofNat_add, BitVec.add_assoc, BitVec.ofNat_eq_ofNat]
  rw [addr]
  refine ⟨?_, ?_⟩
  · have low := hp.readable.low
    generalize hb : stackPtr s + 8 = base at low ⊢
    simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
    omega
  · intro i hi
    simpa only [BitVec.ofNat_add, BitVec.add_assoc] using hp.readable.mem (offset+i) (by omega)

set_option maxHeartbeats 1000000 in
theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x101182 bytes) (Effect.post effect) := by
  intro s ready loaded hp
  have headPre : Head.Pre s := ⟨hp.rip, (hp.writable_at 63 1 (by decide)).toMemReadable, hp.position⟩
  obtain ⟨fuelA, a, runA, readyA, _, effectA⟩ := Head.run boundary outside s ready
    (loaded.mono (codeRange_slice_subset 0x101182 bytes 0 15)) headPre
  have agreesA : AgreesExcept [.reg 15,.flags,.rip] s a := effectA.agrees
  have spA : stackPtr a = stackPtr s := agreesA.read (n := 64) (r := 4) (by simp)
  have memA : a.external = s.external := agreesA.external (by simp [Component.Covers])
  have zeroA : (Operand.reg 15#5 : Operand 64).read a = 0#64 := effectA.writes
  have copyPre : Copy.Pre a := by
    refine ⟨effectA.rip, zeroA, ?_, ?_, ?_⟩
    · intro i hi
      rw [spA]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl
      · exact (hp.readable_at 0 (by decide)).of_external_eq memA
      · exact (hp.readable_at 8 (by decide)).of_external_eq memA
      · exact (hp.readable_at 16 (by decide)).of_external_eq memA
      · exact (hp.readable_at 24 (by decide)).of_external_eq memA
    · intro i hi
      rw [spA]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl
      · exact (hp.writable_at 0 8 (by decide)).of_external_eq memA
      · exact (hp.writable_at 8 8 (by decide)).of_external_eq memA
      · exact (hp.writable_at 16 8 (by decide)).of_external_eq memA
      · exact (hp.writable_at 24 8 (by decide)).of_external_eq memA
    · intro i hi
      rw [spA]
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl
      · exact hp.apart_at 0 8 0 208 (by decide) (by decide)
      · exact hp.apart_at 8 8 0 208 (by decide) (by decide)
      · exact hp.apart_at 16 8 0 208 (by decide) (by decide)
      · exact hp.apart_at 24 8 0 208 (by decide) (by decide)
  have codeA := agreesA.codeIn (by simp [Component.Covers]) loaded
  obtain ⟨fuelB, b, runB, readyB, _, effectB⟩ := Copy.run boundary outside a readyA
    (codeA.mono (codeRange_slice_subset 0x101182 bytes 15 52)) copyPre
  have spB : stackPtr b = stackPtr s :=
    (effectB.agrees.read (n := 64) (r := 4) (by simp [Copy.effect, Effect.components])).trans spA
  have zeroB : (Operand.reg 15#5 : Operand 64).read b = 0#64 :=
    (effectB.agrees.read (n := 64) (r := 15#5) (by simp [Copy.effect, Effect.components])).trans zeroA
  have codeB : CodeIn (codeRange 0x101182 bytes) b := by
    apply effectB.codeIn ?_ codeA
    apply Effect.avoids_codeRange
    simp only [Copy.effect, Effect.components, Write.component, Operand.component,
      List.map_cons, List.map_nil, List.append_nil, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false]
    intro c hc addr len eq
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl) | rfl <;> try cases eq
    all_goals rw [spA]
    · exact hp.apart_at 24 8 0 208 (by decide) (by decide)
    · exact hp.apart_at 16 8 0 208 (by decide) (by decide)
    · exact hp.apart_at 8 8 0 208 (by decide) (by decide)
    · exact hp.apart_at 0 8 0 208 (by decide) (by decide)
  obtain ⟨c, runC, readyC, effectC⟩ :=
    (Common.Instructions.ByteLogic.or_r15b_20_effect_step 0x1011c5).advances readyB
      (codeB.mono (codeRange_slice_subset 0x101182 bytes 67 4)) effectB.rip
      (boundary_ne_program outside (inProgram_of_textOffset 0x11c9 (by decide)))
  have agreesC : AgreesExcept [.reg 15,.flags,.rip] b c := effectC.agrees
  have spC : stackPtr c = stackPtr s :=
    (agreesC.read (n := 64) (r := 4) (by simp)).trans spB
  have resultC := Common.Instructions.ByteLogic.or_r15b_20_result_of_zero 0x1011c5 b c effectC zeroB
  have writableC := ((hp.writable_at 63 1 (by decide)).of_holds effectA |>.of_holds effectB).of_holds effectC
  have tailPre : Tail.Pre c := by
    refine ⟨effectC.rip, ?_, ?_⟩
    · change MemWritable c (stackPtr c + 239) 1
      rw [spC]
      exact ⟨writableC.low, writableC.mem, writableC.tables⟩
    · change RangeApart (stackPtr c + 239) 1 0x1011c9 137
      rw [spC]
      exact hp.apart_at 63 1 71 137 (by decide) (by decide)
  have codeC := agreesC.codeIn (by simp [Component.Covers]) codeB
  obtain ⟨fuelD, t, runD, readyT, _, effectD⟩ := Tail.run boundary outside c readyC
    (codeC.mono (codeRange_slice_subset 0x101182 bytes 71 137)) tailPre
  have agreesD : AgreesExcept [.mem (stackPtr s + 239) 1,.reg 7,.reg 6,.reg 1,.rip] c t := by
    have h := effectD.agrees
    simp only [Tail.effect, Effect.components, Write.component, Operand.component,
      List.map_cons, List.map_nil, List.append_nil, List.nil_append, List.cons_append] at h
    have rsp : rspOf c = stackPtr s := spC
    simpa only [rsp] using h
  have preserved : ∀ off : Nat, off ≤ 24 →
      memLoad t.external (stackPtr s + 176 + BitVec.ofNat 64 off) 64 =
        memLoad b.external (stackPtr s + 176 + BitVec.ofNat 64 off) 64 := by
    intro off hoff
    apply memLoad_congr
    intro i hi
    apply congrArg (fun v : Option UInt8 => v.getD 0)
    apply (agreesC.trans agreesD).byte
    intro component member cover
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with (rfl | rfl | rfl) | (rfl | rfl | rfl | rfl | rfl)
    all_goals try exact cover.elim
    obtain ⟨j, hj, he⟩ := cover
    bv_omega
  have wb := effectB.writes
  change (Operand.reg 0 : Operand 64).read b = memLoad a.external (stackPtr a + 8) 64 ∧
    (Operand.reg 1 : Operand 64).read b = memLoad a.external (stackPtr a + 16) 64 ∧
    memLoad b.external (stackPtr a + 200) 64 = memLoad a.external (stackPtr a + 32) 64 ∧
    memLoad b.external (stackPtr a + 192) 64 = memLoad a.external (stackPtr a + 24) 64 ∧
    memLoad b.external (stackPtr a + 184) 64 = memLoad a.external (stackPtr a + 16) 64 ∧
    memLoad b.external (stackPtr a + 176) 64 = memLoad a.external (stackPtr a + 8) 64 at wb
  rw [spA, memA] at wb
  have wd := effectD.writes
  change memLoad t.external (stackPtr c + 239) 8 = (Operand.reg 15 : Operand 8).read c ∧
    (Operand.reg 7 : Operand 64).read t = stackPtr c + 72 ∧
    (Operand.reg 6 : Operand 64).read t = stackPtr c + 176 ∧
    (Operand.reg 1 : Operand 64).read t = 13 at wd
  rw [spC] at wd
  have byteC : (Operand.reg 15 : Operand 8).read c = 32 := by
    have h := congrArg (BitVec.setWidth 8) resultC
    simp only [Operand.read, BitVec.setWidth_setWidth_of_le _ (by decide : 8 ≤ 64)] at h
    exact h
  have final : (effect s).Holds s t := by
    refine ⟨effectD.rip, ?_, ⟨trivial,trivial,trivial,trivial,trivial,trivial⟩, ?_⟩
    · change (Operand.reg 0 : Operand 64).read t = _ ∧
        (Operand.reg 1 : Operand 64).read t = _ ∧
        (Operand.reg 15 : Operand 64).read t = _ ∧
        (Operand.reg 7 : Operand 64).read t = _ ∧
        (Operand.reg 6 : Operand 64).read t = _ ∧
        memLoad t.external (stackPtr s + 176) 64 = _ ∧
        memLoad t.external (stackPtr s + 184) 64 = _ ∧
        memLoad t.external (stackPtr s + 192) 64 = _ ∧
        memLoad t.external (stackPtr s + 200) 64 = _ ∧
        memLoad t.external (stackPtr s + 239) 8 = _
      refine ⟨((agreesC.trans agreesD).read (n := 64) (r := 0) (by simp)).trans wb.1,
        wd.2.2.2, (agreesD.read (n := 64) (r := 15) (by simp)).trans resultC,
        wd.2.1, wd.2.2.1, ?_, ?_, ?_, ?_, wd.1.trans byteC⟩
      · simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using (preserved 0 (by decide)).trans (by simpa only [BitVec.add_zero, BitVec.ofNat_eq_ofNat] using wb.2.2.2.2.2)
      · simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using
          (preserved 8 (by decide)).trans (by simpa only [BitVec.ofNat_eq_ofNat,
            BitVec.add_assoc, BitVec.reduceAdd] using wb.2.2.2.2.1)
      · simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using
          (preserved 16 (by decide)).trans (by simpa only [BitVec.ofNat_eq_ofNat,
            BitVec.add_assoc, BitVec.reduceAdd] using wb.2.2.2.1)
      · simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using
          (preserved 24 (by decide)).trans (by simpa only [BitVec.ofNat_eq_ofNat,
            BitVec.add_assoc, BitVec.reduceAdd] using wb.2.2.1)
    · apply (agreesA.trans effectB.agrees |>.trans agreesC |>.trans agreesD).mono
      simp [effect, Copy.effect, Effect.components, spA]

  refine ⟨fuelA + fuelB + 1 + fuelD, t, ((runA.trans runB).trans runC).trans runD,
    readyT, ?_, final⟩
  apply final.codeIn ?_ loaded
  apply Effect.avoids_codeRange
  simp only [effect, Effect.components, Write.component, Operand.component,
    List.map_cons, List.map_nil, List.mem_append, List.mem_cons, List.not_mem_nil, or_false]
  intro component member addr len eq
  rcases member with ((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl) | rfl <;> try cases eq
  · exact hp.apart_at 0 8 0 208 (by decide) (by decide)
  · exact hp.apart_at 8 8 0 208 (by decide) (by decide)
  · exact hp.apart_at 16 8 0 208 (by decide) (by decide)
  · exact hp.apart_at 24 8 0 208 (by decide) (by decide)
  · exact hp.apart_at 63 1 0 208 (by decide) (by decide)

theorem effect_agrees {s t : RamState} (h : (effect s).Holds s t) :
    AgreesExcept (appendComponents s) s t := by
  apply h.agrees.widen
  · simp [effect, Effect.components, Component.isMem, appendComponents]
  · intro a c hc cover
    simp only [effect, Effect.components, Write.component, Operand.component,
      List.map_cons, List.map_nil, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with ((rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl) | rfl
    all_goals try exact cover.elim
    all_goals obtain ⟨i, hi, rfl⟩ := cover
    · exact ⟨.mem (stackPtr s + 176) 32, by simp [appendComponents], i, by omega, rfl⟩
    · refine ⟨.mem (stackPtr s + 176) 32, by simp [appendComponents], 8+i, by omega, ?_⟩
      change _ = stackPtr s + 176 + BitVec.ofNat 64 (_ + i)
      bv_omega
    · refine ⟨.mem (stackPtr s + 176) 32, by simp [appendComponents], 16+i, by omega, ?_⟩
      change _ = stackPtr s + 176 + BitVec.ofNat 64 (_ + i)
      bv_omega
    · refine ⟨.mem (stackPtr s + 176) 32, by simp [appendComponents], 24+i, by omega, ?_⟩
      change _ = stackPtr s + 176 + BitVec.ofNat 64 (_ + i)
      bv_omega
    · exact ⟨.mem (stackPtr s + 239) 1, by simp [appendComponents], i, hi, rfl⟩

theorem effect_words {s t : RamState} (h : (effect s).Holds s t) :
    ∀ j < 4, memLoad t.external (stackPtr s + 176 + BitVec.ofNat 64 (8*j)) 64 =
      memLoad s.external (stackPtr s + 8 + BitVec.ofNat 64 (8*j)) 64 := by
  have hw := h.writes
  simp only [effect, Write.AllHold, Operand.read] at hw
  intro j hj
  rcases (by omega : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3) with rfl | rfl | rfl | rfl
  · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero] using hw.2.2.2.2.2.1
  · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using hw.2.2.2.2.2.2.1
  · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using hw.2.2.2.2.2.2.2.1
  · simpa only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_assoc, BitVec.reduceAdd] using hw.2.2.2.2.2.2.2.2.1

theorem effect_position {s t : RamState} (h : (effect s).Holds s t) :
    memLoad t.external (stackPtr s + 239) 8 = 32 := h.writes.2.2.2.2.2.2.2.2.2

end P256.Proofs.HMAC.Finalize.OuterBuffer.Machine
