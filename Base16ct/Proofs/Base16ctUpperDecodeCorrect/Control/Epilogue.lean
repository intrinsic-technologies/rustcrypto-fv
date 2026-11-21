import Base16ct.Proofs.Common.Output
import Base16ct.Proofs.Base16ctUpperDecodeCorrect.Memory
import Base16ct.Proofs.Base16ctUpperDecodeCorrect.LoopStep.MachineInvariant
import Base16ct.Proofs.Copied.Md5.Proofs.Buffered.Stores.Effect
import Base16ct.Proofs.Base16ctUpperDecodeCorrect.Entry
import Base16ct.Proofs.Base16ctUpperDecodeCorrect.Decoder
import Base16ct.Proofs.Base16ctUpperDecodeCorrect.LoopStep.Instructions.Byte

namespace Base16ct.Proofs.Base16ctUpperDecodeCorrect

variable {alphabet : RFC4648.Alphabet}
open Base16ct.Spec Base16ct.Spec.Program Base16ct.Spec.Program.Extracted
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Instructions

set_option maxRecDepth 100000 in
theorem decode_return_suffix [Bindings] {s : RamState} {offset : Nat}
    (he : EntryReady programImage s) (hp : s.RIP = decodeAddress alphabet + BitVec.ofNat 64 offset)
    (hoffset : offset = 240 ∨ offset = 251)
    (hread : MemReadable s (stackPtr s) 8)
    (hlow : (stackTop s).toNat < 2^32) :
    ∃ t, Returns (returnBoundary s) 1 s t ∧ ReadyToStep t ∧
      AgreesExcept [.reg 4, .rip] s t := by
  have hcode : CodeIn (codeRange s.RIP [0xc3]) s := he.code.mono (by
    rw [hp]
    rcases hoffset with rfl | rfl <;> cases alphabet <;> decide +kernel)
  obtain ⟨t, hstep, hrt, ht⟩ := ret_effect_step s.RIP s he.ready hcode ⟨⟨rfl, hread⟩, hlow⟩
  refine ⟨t, Returns.of_step hstep ht.rip ?_, hrt, ht.agrees⟩
  exact ht.writes

set_option maxRecDepth 100000 in
theorem decode_finish_mov_eax_two [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (he : EntryReady programImage s) (hp : s.RIP = decodeAddress alphabet + 228#64)
    (hret : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ CodeIn programImage t ∧
      (movR32Imm32Effect s.RIP 5 0 (2#32) s).Holds s t := by
  apply advanceInProgram (mov_r32_imm32_effect_step (p := s.RIP) (op := 0xb8) (imm := 2#32) (by decide)) he.ready he.code
  · intro x hx
    obtain ⟨i, rfl⟩ := (mem_codeRange_iff _ _ _).mp hx
    change Fin 5 at i
    clear hx
    finite_cases i
    all_goals rw [hp]
    all_goals (cases alphabet <;> decide +kernel)
  · exact rfl
  · exact hret
  · change InProgram (BitVec.add s.RIP _)
    rw [hp]
    exact ⟨0x66, by cases alphabet <;> decide +kernel⟩
  · exact Effect.avoids_of_components_reg_rip (movR32Imm32Effect_components _ _ _ _ _) _

set_option maxRecDepth 100000 in
theorem decode_finish_test_si [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (he : EntryReady programImage s) (hp : s.RIP = decodeAddress alphabet + 233#64)
    (hret : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ CodeIn programImage t ∧
      (Instructions.testR16R16Effect s.RIP 6 6 s).Holds s t := by
  apply advanceInProgram (Instructions.test_r16_r16_effect_step s.RIP 0xf6 (by decide)) he.ready he.code
  · intro x hx
    obtain ⟨i, rfl⟩ := (mem_codeRange_iff _ _ _).mp hx
    change Fin 3 at i
    clear hx
    finite_cases i
    all_goals rw [hp]
    all_goals (cases alphabet <;> decide +kernel)
  · exact rfl
  · exact hret
  · change InProgram (BitVec.add s.RIP _)
    rw [hp]
    exact ⟨0x5b, by cases alphabet <;> decide +kernel⟩
  · exact Effect.Avoids.of_noMem (by simp [Effect.components, Instructions.testR16R16Effect, Component.Covers]) _

set_option maxRecDepth 100000 in
theorem decode_finish_pop_rbx [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (he : EntryReady programImage s) (hp : s.RIP = decodeAddress alphabet + 236#64)
    (hread : MemReadable s (stackPtr s) 8)
    (hret : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ CodeIn programImage t ∧
      (popR64Effect s.RIP 1 3 s).Holds s t := by
  apply advanceInProgram (pop_r64_effect_step s.RIP 0x5b (by decide) (by decide)) he.ready he.code
  · intro x hx
    obtain ⟨i, rfl⟩ := (mem_codeRange_iff _ _ _).mp hx
    change Fin 1 at i
    clear hx
    finite_cases i
    all_goals rw [hp]
    all_goals (cases alphabet <;> decide +kernel)
  · exact ⟨rfl, hread⟩
  · exact hret
  · change InProgram (BitVec.add s.RIP _)
    rw [hp]
    exact ⟨0x5d, by cases alphabet <;> decide +kernel⟩
  · exact popR64Effect_avoids _ _ _ _ _

set_option maxRecDepth 100000 in
theorem decode_finish_pop_rbp [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (he : EntryReady programImage s) (hp : s.RIP = decodeAddress alphabet + 237#64)
    (hread : MemReadable s (stackPtr s) 8)
    (hret : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ CodeIn programImage t ∧
      (popR64Effect s.RIP 1 5 s).Holds s t := by
  apply advanceInProgram (pop_r64_effect_step s.RIP 0x5d (by decide) (by decide)) he.ready he.code
  · intro x hx
    obtain ⟨i, rfl⟩ := (mem_codeRange_iff _ _ _).mp hx
    change Fin 1 at i
    clear hx
    finite_cases i
    all_goals rw [hp]
    all_goals (cases alphabet <;> decide +kernel)
  · exact ⟨rfl, hread⟩
  · exact hret
  · change InProgram (BitVec.add s.RIP _)
    rw [hp]
    exact ⟨0x74, by cases alphabet <;> decide +kernel⟩
  · exact popR64Effect_avoids _ _ _ _ _

set_option maxRecDepth 100000 in
theorem decode_finish_xor_eax [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (he : EntryReady programImage s) (hp : s.RIP = decodeAddress alphabet + 249#64)
    (hret : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ CodeIn programImage t ∧
      (xorR32R32Effect s.RIP 2 0 0 s).Holds s t := by
  apply advanceInProgram (xor_r32_r32_effect_step s.RIP 0xc0 (by decide)) he.ready he.code
  · intro x hx
    obtain ⟨i, rfl⟩ := (mem_codeRange_iff _ _ _).mp hx
    change Fin 2 at i
    clear hx
    finite_cases i
    all_goals rw [hp]
    all_goals (cases alphabet <;> decide +kernel)
  · exact rfl
  · exact hret
  · change InProgram (BitVec.add s.RIP _)
    rw [hp]
    exact ⟨0xc3, by cases alphabet <;> decide +kernel⟩
  · exact Effect.Avoids.of_noMem (by simp [Effect.components, xorR32R32Effect, Component.Covers]) _


set_option maxRecDepth 100000 in
theorem decode_finish_je [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (he : EntryReady programImage s) (hp : s.RIP = decodeAddress alphabet + 238#64)
    (hret : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ CodeIn programImage t ∧
      (jccEffect s.RIP 2 (4#4) ((6#8).signExtend 64) s).Holds s t := by
  apply advanceInProgram (jcc_rel8_effect_step s.RIP (4#4) (6#8)) he.ready he.code
  · intro x hx
    obtain ⟨i, rfl⟩ := (mem_codeRange_iff _ _ _).mp hx
    change Fin 2 at i
    clear hx
    finite_cases i
    all_goals rw [hp]
    all_goals (cases alphabet <;> decide +kernel)
  · refine ⟨rfl, ?_⟩
    intro _
    rw [hp]
    cases alphabet <;> decide +kernel
  · exact hret
  · unfold jccEffect branchEffect
    split <;> rw [hp]
    · exact ⟨0x4c, by cases alphabet <;> decide +kernel⟩
    · exact ⟨0xc3, by cases alphabet <;> decide +kernel⟩
  · exact branchEffect_avoids _ _ _ _

set_option maxRecDepth 100000 in
theorem decode_finish_store_length [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (he : EntryReady programImage s) (hp : s.RIP = decodeAddress alphabet + 246#64)
    (hw : Base16ct.Proofs.Copied.Md5.Proofs.Memory.StorePre s.RIP 3 (storeAddrAt s.RIP (.base 2 .none) 3) 8 s)
    (ha : (movM64R64Effect s.RIP 9 (.base 2 .none) s).Avoids programImage)
    (hret : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ CodeIn programImage t ∧
      (movM64R64Effect s.RIP 9 (.base 2 .none) s).Holds s t := by
  apply advanceInProgram (Base16ct.Proofs.Copied.Md5.Proofs.Buffered.Stores.mov_m64_r64_effect_step s.RIP 0x4c
    (by unfold RexWPrefix; decide) 1 (.base 2 .none)
    (by decide) rfl rfl) he.ready he.code
  · intro x hx
    obtain ⟨i, rfl⟩ := (mem_codeRange_iff _ _ _).mp hx
    change Fin 3 at i
    clear hx
    finite_cases i
    all_goals rw [hp]
    all_goals (cases alphabet <;> decide +kernel)
  · exact hw
  · exact hret
  · change InProgram (BitVec.add s.RIP 3#64)
    rw [hp]
    exact ⟨0x31, by cases alphabet <;> decide +kernel⟩
  · exact ha


set_option maxRecDepth 100000 in
theorem decode_finish_restore [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (he : EntryReady programImage s) (hp : s.RIP = decodeAddress alphabet + 236#64)
    (hrb : MemReadable s (stackPtr s) 8)
    (hrp : MemReadable s (stackPtr s + 8#64) 8)
    (hret : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 2 s t ∧ EntryReady programImage t ∧
      t.RIP = decodeAddress alphabet + 238#64 ∧
      AgreesExcept [.reg 3, .reg 4, .reg 5, .rip] s t ∧
      AddrMode.reg64 3 t = stackTop s ∧
      AddrMode.reg64 5 t = memLoad s.external (stackPtr s + 8#64) 64 ∧
      stackPtr t = stackPtr s + 16#64 := by
  obtain ⟨u, hau, hru, hcu, hu⟩ := decode_finish_pop_rbx he hp hrb hret
  have heu := entryReadyAfter he hru hcu hu.agrees
  have hpu : u.RIP = decodeAddress alphabet + 237#64 := by
    simpa [popR64Effect, hp, BitVec.add_assoc] using hu.rip
  have hfu : AgreesExcept [.reg 3, .reg 4, .rip] s u := hu.agrees
  have hmu : u.external = s.external := hfu.external (by simp [Component.Covers])
  have hspu : stackPtr u = stackPtr s + 8#64 := hu.writes.2
  have hread : MemReadable u (stackPtr u) 8 := by
    rw [hspu]
    exact hrp.of_external_eq hmu
  obtain ⟨t, hat, hrt, hct, ht⟩ := decode_finish_pop_rbp heu hpu hread hret
  have hft : AgreesExcept [.reg 5, .reg 4, .rip] u t := ht.agrees
  refine ⟨t, hau.trans hat, entryReadyAfter heu hrt hct ht.agrees, ?_,
    (hfu.trans hft).mono (by simp), (hft.read (by simp)).trans hu.writes.1, ?_, ?_⟩
  · simpa [popR64Effect, hpu, BitVec.add_assoc] using ht.rip
  · have hw := ht.writes.1
    change AddrMode.reg64 5 t = memLoad u.external (stackPtr u) 64 at hw
    simpa only [hmu, hspu] using hw
  · have hw := ht.writes.2
    change stackPtr t = stackPtr u + 8#64 at hw
    simpa [hspu, BitVec.add_assoc] using hw

set_option maxRecDepth 100000 in
theorem decode_finish_select [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {error : BitVec 8}
    (he : EntryReady programImage s) (hp : s.RIP = decodeAddress alphabet + 228#64)
    (hsi : AddrMode.reg64 6 s = error.setWidth 64)
    (hret : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 2 s t ∧ EntryReady programImage t ∧
      t.RIP = decodeAddress alphabet + 236#64 ∧
      AgreesExcept [.reg 0, .flags, .rip] s t ∧
      AddrMode.reg64 0 t = 2#64 ∧
      (StatusFlags.ofRFLAGS t.RFLAGS).ZF = decide (error = 0#8) := by
  obtain ⟨u, hau, hru, hcu, hu⟩ := decode_finish_mov_eax_two he hp hret
  have heu := entryReadyAfter he hru hcu hu.agrees
  have hpu : u.RIP = decodeAddress alphabet + 233#64 := by
    simpa [movR32Imm32Effect, hp, BitVec.add_assoc] using hu.rip
  have hfu : AgreesExcept [.reg 0, .rip] s u := hu.agrees
  obtain ⟨t, hat, hrt, hct, ht⟩ := decode_finish_test_si heu hpu hret
  have hft : AgreesExcept [.flags, .rip] u t := ht.agrees
  have hsiu : (Operand.reg 6#5 : Operand 16).read u = error.setWidth 16 := by
    have hh : AddrMode.reg64 6 u = AddrMode.reg64 6 s := hfu.read (n := 64) (r := 6) (by simp)
    have hx := congrArg (fun x : BitVec 64 => x.setWidth 16) (hh.trans hsi)
    simpa [AddrMode.reg64, Operand.read] using hx
  have hzero : (error.setWidth 16 == 0#16) = decide (error = 0#8) := by
    apply Bool.eq_iff_iff.mpr
    simp only [beq_iff_eq, decide_eq_true_eq]
    constructor
    · intro hz
      have hh := congrArg (fun x : BitVec 16 => x.setWidth 8) hz
      simpa using hh
    · intro hz
      simp [hz]
  refine ⟨t, hau.trans hat, entryReadyAfter heu hrt hct ht.agrees, ?_,
    (hfu.trans hft).mono (by simp), (hft.read (by simp)).trans hu.writes, ?_⟩
  · simpa [Instructions.testR16R16Effect, hpu, BitVec.add_assoc] using ht.rip
  · have hh := ht.flags.2.2.2.1
    change (StatusFlags.ofRFLAGS t.RFLAGS).ZF =
      ((Operand.reg 6#5 : Operand 16).read u &&& (Operand.reg 6#5 : Operand 16).read u == 0#16) at hh
    simpa only [hsiu, BitVec.and_self, hzero] using hh


set_option maxRecDepth 100000 in
theorem decode_success_suffix [Bindings] {s : RamState}
    (he : EntryReady programImage s) (hp : s.RIP = decodeAddress alphabet + 246#64)
    (hw : Base16ct.Proofs.Copied.Md5.Proofs.Memory.StorePre s.RIP 3 (storeAddrAt s.RIP (.base 2 .none) 3) 8 s)
    (ha : (movM64R64Effect s.RIP 9 (.base 2 .none) s).Avoids programImage)
    (hread : MemReadable s (stackPtr s) 8)
    (hapart : RangeApart (AddrMode.reg64 2 s) 8 (stackPtr s) 8)
    (hlow : (stackTop s).toNat < 2^32) (hret : ¬ InProgram (stackTop s)) :
    ∃ t, Returns (returnBoundary s) 3 s t ∧ ReadyToStep t ∧
      AgreesExcept [.mem (AddrMode.reg64 2 s) 8, .reg 0, .reg 4, .flags, .rip] s t ∧
      AddrMode.reg64 0 t = 0#64 ∧
      memLoad t.external (AddrMode.reg64 2 s) 64 = AddrMode.reg64 9 s := by
  obtain ⟨u, hau, hru, hcu, hu⟩ := decode_finish_store_length
    (boundary := returnBoundary s) he hp hw ha hret
  have haddr : storeAddrAt s.RIP (.base 2 .none) 3 s = AddrMode.reg64 2 s := by
    simp [storeAddrAt, AddrMode.addr, Disp.value]
  have hfu : AgreesExcept [.mem (AddrMode.reg64 2 s) 8, .rip] s u := by
    simpa [movM64R64Effect_components, storeAddrAt, AddrMode.addr, Disp.value] using hu.agrees
  have hspu : stackPtr u = stackPtr s := hfu.read (n := 64) (r := 4) (by simp)
  have htopu : stackTop u = stackTop s := by
    unfold stackTop
    rw [hspu]
    apply memLoad_congr
    intro i hi
    change (u.external[stackPtr s + BitVec.ofNat 64 i]?).getD 0 =
      (s.external[stackPtr s + BitVec.ofNat 64 i]?).getD 0
    rw [hfu.byte]
    intro c hc hcover
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · obtain ⟨j, hj, hjx⟩ := hcover
      exact hapart j hj i hi hjx.symm
    · exact hcover
  have heu := entryReadyAfter he hru hcu hu.agrees
  have hpu : u.RIP = decodeAddress alphabet + 249#64 := by
    have hh : u.RIP = BitVec.add s.RIP 3#64 := hu.rip
    simpa [hp, BitVec.add_assoc] using hh
  obtain ⟨v, hav, hrv, hcv, hv⟩ := decode_finish_xor_eax
    (boundary := returnBoundary s) heu hpu hret
  have hfv : AgreesExcept [.reg 0, .flags, .rip] u v := hv.agrees
  have hmv : v.external = u.external := hfv.external (by simp [Component.Covers])
  have hspv : stackPtr v = stackPtr s := (hfv.read (n := 64) (r := 4) (by simp)).trans hspu
  have htopv : stackTop v = stackTop s := by
    have hsp : stackPtr v = stackPtr u := hfv.read (n := 64) (r := 4) (by simp)
    simpa only [stackTop, Operand.read, hsp, hmv] using htopu
  have hev := entryReadyAfter heu hrv hcv hv.agrees
  have hpv : v.RIP = decodeAddress alphabet + 251#64 := by
    simpa [xorR32R32Effect, hpu, BitVec.add_assoc] using hv.rip
  have hr : MemReadable v (stackPtr v) 8 := by
    rw [hspv]
    exact ⟨hread.low, fun i hi => (hfu.trans hfv).grow _ (hread.mem i hi)⟩
  obtain ⟨t, hat, hrt, hft⟩ := decode_return_suffix hev hpv (Or.inr rfl)
    hr (by rw [htopv]; exact hlow)
  have hb : returnBoundary v = returnBoundary s := by
    change ({rip := stackTop v, rsp := stackPtr v + 8#64} : ReturnBoundary) =
      {rip := stackTop s, rsp := stackPtr s + 8#64}
    rw [htopv, hspv]
  rw [hb] at hat
  refine ⟨t, hau.returns (hav.returns hat), hrt,
    (hfu.trans (hfv.trans hft)).mono (by simp), ?_, ?_⟩
  · have hz : AddrMode.reg64 0 v = 0#64 := by
      simpa [xorR32R32Effect, Write.AllHold, Operand.read, AddrMode.reg64] using hv.writes
    exact (hft.read (by simp)).trans hz
  · have hm : t.external = u.external := (hfv.trans hft).external (by simp [Component.Covers])
    have hh := hu.writes
    change memLoad u.external (storeAddrAt s.RIP (.base 2 .none) 3 s) 64 =
      AddrMode.reg64 9 s at hh
    simpa only [hm, haddr] using hh


set_option maxRecDepth 100000 in
theorem decode_finish_branch [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {error : BitVec 8}
    (he : EntryReady programImage s) (hp : s.RIP = decodeAddress alphabet + 228#64)
    (hsi : AddrMode.reg64 6 s = error.setWidth 64)
    (hrb : MemReadable s (stackPtr s) 8)
    (hrp : MemReadable s (stackPtr s + 8#64) 8)
    (hret : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 5 s t ∧ EntryReady programImage t ∧
      t.RIP = (if error = 0#8 then decodeAddress alphabet + 246#64
        else decodeAddress alphabet + 240#64) ∧
      AgreesExcept [.reg 0, .reg 3, .reg 4, .reg 5, .flags, .rip] s t ∧
      AddrMode.reg64 0 t = 2#64 ∧
      AddrMode.reg64 3 t = stackTop s ∧
      AddrMode.reg64 5 t = memLoad s.external (stackPtr s + 8#64) 64 ∧
      stackPtr t = stackPtr s + 16#64 := by
  obtain ⟨u, hau, heu, hpu, hfu, haxu, hz⟩ := decode_finish_select he hp hsi hret
  have hmu : u.external = s.external := hfu.external (by simp [Component.Covers])
  have hspu : stackPtr u = stackPtr s := hfu.read (n := 64) (r := 4) (by simp)
  have hru : MemReadable u (stackPtr u) 8 := by
    rw [hspu]
    exact hrb.of_external_eq hmu
  have hrpu : MemReadable u (stackPtr u + 8#64) 8 := by
    rw [hspu]
    exact hrp.of_external_eq hmu
  obtain ⟨v, hav, hev, hpv, hfv, hbxv, hbpv, hspv⟩ := decode_finish_restore heu hpu hru hrpu hret
  obtain ⟨t, hat, hrt, hct, ht⟩ := decode_finish_je hev hpv hret
  have hft : AgreesExcept [.rip] v t := by
    simpa [Effect.components, jccEffect, branchEffect] using ht.agrees
  have hzv : (StatusFlags.ofRFLAGS v.RFLAGS).ZF = decide (error = 0#8) := by
    rw [hfv.rflags (by simp) (by simp)]
    exact hz
  refine ⟨t, hau.trans (hav.trans hat), entryReadyAfter hev hrt hct ht.agrees, ?_,
    (hfu.trans (hfv.trans hft)).mono (by simp),
    ((hfv.trans hft).read (by simp)).trans haxu, ?_, ?_, ?_⟩
  · have hh := ht.rip
    change t.RIP = (if (StatusFlags.ofRFLAGS v.RFLAGS).ZF then
      BitVec.add (BitVec.add v.RIP 2#64) 6#64 else BitVec.add v.RIP 2#64) at hh
    simpa [hzv, hpv, BitVec.add_assoc] using hh
  · have hh := (hft.read (n := 64) (r := 3) (by simp)).trans hbxv
    simpa [stackTop, Operand.read, AddrMode.reg64, hmu, hspu] using hh
  · have hh := (hft.read (n := 64) (r := 5) (by simp)).trans hbpv
    simpa [Operand.read, AddrMode.reg64, hmu, hspu] using hh
  · have hh := (hft.read (n := 64) (r := 4) (by simp)).trans hspv
    simpa [stackPtr, Operand.read, AddrMode.reg64] using hh.trans (congrArg (fun x => x + 16#64) hspu)


theorem decode_length_output_ready {initial s : RamState} {input : List UInt8}
    {routine : Routine} {capacity : Nat} {lengthWritten : Prop} {components : List Component}
    (hv : ValidCall routine initial input capacity lengthWritten) (hsuccess : lengthWritten)
    (hf : AgreesExcept components initial s) (hcapacity : input.length / 2 ≤ capacity) :
    Base16ct.Proofs.Copied.Md5.Proofs.Memory.MemWritable s (initial.regValue .rdx) 8 ∧
    (∀ i < 8, ¬ InProgram (initial.regValue .rdx + BitVec.ofNat 64 i)) ∧
    RangeApart (initial.regValue .rdx) 8 (stackPtr initial) 8 ∧
    RangeApart (initial.regValue .rdx) 8 (initial.regValue .rcx) (input.length / 2) := by
  have hl := hv.lengthOutputInMemoryIfLengthWritten hsuccess
  have hsep := hv.separation.2.2 hsuccess
  have hcontains {region : MemoryRegion} (hb : region.Bounded) {ptr : BitVec 64} {count : Nat}
      (hstart : region.start ≤ ptr.toNat) (hend : ptr.toNat + count ≤ region.start + region.size)
      (i : Nat) (hi : i < count) : region.Contains (ptr + BitVec.ofNat 64 i).toNat := by
    have hbound : region.start + region.size < 2^32 := hb
    rw [BitVec.toNat_add, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt (by omega : i < 2^64), Nat.mod_eq_of_lt (by omega)]
    constructor <;> omega
  have hlength (i : Nat) (hi : i < 8) : (lengthOutputRegion initial).Contains
      (initial.regValue .rdx + BitVec.ofNat 64 i).toNat :=
    hcontains hl.1 (Nat.le_refl _) (Nat.le_refl _) i hi
  have halloc : (lengthOutputRegion initial).Allocated s.external := by
    intro a ha
    exact Option.isSome_iff_exists.mp (hf.grow a (Option.isSome_iff_exists.mpr (hl.2 a ha)))
  have htable : (lengthOutputRegion initial).Avoids Base16ct.Proofs.Copied.Md5.Spec.Program.InPageTables := by
    intro a ha htable
    apply hsep.2 a ha
    right
    simp only [Base16ct.Proofs.Copied.Md5.Spec.Program.InPageTables] at htable
    obtain ⟨r, hr, ha⟩ := htable
    have hr' : r = (⟨0x1000, 8⟩ : MemoryRegion) ∨ r = ⟨0x2000, 32⟩ := by simpa using hr
    rcases hr' with rfl | rfl <;> simp only [MemoryRegion.Contains] at ha
    all_goals change 0x1000 ≤ a.toNat ∧ a.toNat < 0x1000 + 0x2000
    all_goals omega
  refine ⟨Base16ct.Proofs.Copied.Md5.Proofs.Memory.MemWritable.of_region hl.1 halloc htable
    (Nat.le_refl _) (Nat.le_refl _), ?_, ?_, ?_⟩
  · intro i hi hp
    exact hsep.2 _ (hlength i hi) (Or.inl hp)
  · intro i hi j hj heq
    have hsbound := hv.stack.1
    have hstk : (Stack.region initial routine.minStackBytes).Contains
        (stackPtr initial + BitVec.ofNat 64 j).toNat := by
      apply hcontains hsbound ?_ ?_ j hj
      · change (initial.regValue .rsp).toNat - routine.minStackBytes ≤ (initial.regValue .rsp).toNat
        omega
      · change (initial.regValue .rsp).toNat + 8 ≤
          (initial.regValue .rsp).toNat - routine.minStackBytes +
          ((initial.regValue .rsp).toNat + 8 - ((initial.regValue .rsp).toNat - routine.minStackBytes))
        omega
    exact hsep.1 (0 : Fin 3) (2 : Fin 3) (by decide) _ (hlength i hi) (by rw [heq]; exact hstk)
  · intro i hi j hj heq
    have houtBound : (outputRegion initial (input.length / 2)).Bounded := by
      have hb := hv.outputInMemory.2.1
      change (initial.regValue .rcx).toNat + capacity < 2^32 at hb
      change (initial.regValue .rcx).toNat + input.length / 2 < 2^32
      omega
    have hout : (outputRegion initial (input.length / 2)).Contains
        (initial.regValue .rcx + BitVec.ofNat 64 j).toNat :=
      hcontains houtBound (Nat.le_refl _) (Nat.le_refl _) j hj
    exact hsep.1 (0 : Fin 3) (1 : Fin 3) (by decide) _ (hlength i hi) (by rw [heq]; exact hout)

end Base16ct.Proofs.Base16ctUpperDecodeCorrect

namespace Base16ct.Proofs.Base16ctUpperDecodeCorrect
open Base16ct.Spec Base16ct.Spec.Program Base16ct.Spec.Program.Extracted
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
variable {alphabet : RFC4648.Alphabet}
set_option maxRecDepth 100000 in
theorem decode_completed_loop [Bindings]
    {initial s : RamState} {input : List UInt8} {capacity : Nat}
    (hv : ValidCall (decodeRoutine alphabet) initial input capacity
      (∃ output, pairDecodeResult [alphabet] input capacity = .ok output))
    (he : EntryReady programImage s)
    (h : DecodeMachineLoopInvariant [alphabet] (decodeAddress alphabet) 228 initial input input []
      #v[outputRegion initial (input.length / 2), Stack.region initial (decodeRoutine alphabet).minStackBytes]
      (decodeCallEffects initial (input.length / 2)) s)
    (heven : input.length % 2 = 0) (hcapacity : input.length / 2 ≤ capacity) :
    ∃ fuel t, Returns (returnBoundary initial) fuel s t ∧ ReadyToStep t ∧
      CalleeSavedRegistersUnchanged initial t ∧ DirectionFlagUnset t ∧
      AgreesExcept (.mem (initial.regValue .rdx) 8 :: decodeCallEffects initial (input.length / 2)) initial t ∧
      (match pairDecodeResult [alphabet] input capacity with
      | .ok output => SuccessfulStatus t ∧
        MemoryWriteFrame initial t #v[outputRegion initial output.length,
          lengthOutputRegion initial, Stack.region initial (decodeRoutine alphabet).minStackBytes] ∧
        Base16ct.Spec.Program.readOutput initial t output.length = .ok output.toByteArray ∧
        readLengthOutput initial t = .ok (BitVec.ofNat 64 output.length)
      | .error .invalidLength => FailureStatus t invalidLengthStatus ∧
        MemoryWriteFrame initial t #v[Stack.region initial (decodeRoutine alphabet).minStackBytes]
      | .error .invalidEncoding => FailureStatus t invalidEncodingStatus ∧
        MemoryWriteFrame initial t #v[outputRegion initial (input.length / 2),
          Stack.region initial (decodeRoutine alphabet).minStackBytes]) := by
  have hb := returnBoundaryValid hv
  have hp : s.RIP = decodeAddress alphabet + 228#64 := by simpa only [ite_true] using h.rip
  have hss : stackPtr s = stackPtr initial - 16#64 := by
    simpa [stackPtr, AddrMode.reg64, Operand.read, State.regValue, gprIndex, Syntax.Reg.fin] using h.rsp
  have hrb : MemReadable s (stackPtr s) 8 := by
    rw [hss]
    exact decode_saved_stack_readable hv h.agrees (offset := 16) (by decide) (by change 16 ≤ 144; decide)
  have hrp : MemReadable s (stackPtr s + 8#64) 8 := by
    have hh := decode_saved_stack_readable hv h.agrees (offset := 8) (by decide) (by change 8 ≤ 144; decide)
    have hslot : stackPtr s + 8#64 = initial.regValue .rsp - 8#64 := by
      rw [hss]
      change (stackPtr initial - 16#64) + 8#64 = stackPtr initial - 8#64
      simp only [BitVec.sub_eq_add_neg, BitVec.add_assoc]
      rfl
    rw [hslot]
    exact hh
  have hbx : stackTop s = AddrMode.reg64 3 initial := by
    have hl := (Bytes.of_memLoad (n := 64) hrb.mem).loadBytes64
    have hh := h.savedRBX
    change loadBytes s.external (stackPtr s) 8 = .ok (AddrMode.reg64 3 initial) at hh
    rw [hl] at hh
    exact Except.ok.inj hh
  have hbp : memLoad s.external (stackPtr s + 8#64) 64 = AddrMode.reg64 5 initial := by
    have hl := (Bytes.of_memLoad (n := 64) hrp.mem).loadBytes64
    have hh := h.savedRBP
    change loadBytes s.external (stackPtr s + 8#64) 8 = .ok (AddrMode.reg64 5 initial) at hh
    rw [hl] at hh
    exact Except.ok.inj hh
  obtain ⟨v, hav, hev, hpv, hfv, haxv, hbxv, hbpv, hspv⟩ :=
    decode_finish_branch (boundary := returnBoundary initial) he hp h.rsi hrb hrp hb.2
  have hfiv : AgreesExcept (decodeCallEffects initial (input.length / 2)) initial v :=
    (h.agrees.trans hfv).mono (by simp [decodeCallEffects, decodeLoopEffects])
  have hsp : stackPtr v = stackPtr initial := by
    rw [hspv, hss, BitVec.sub_add_cancel]
  have hreturn := decode_return_stack hv hfiv (by change 16 ≤ 144; decide) hcapacity
  have hreadv : MemReadable v (stackPtr v) 8 := by rw [hsp]; exact hreturn.1
  have htopv : stackTop v = stackTop initial := by
    change memLoad v.external (stackPtr v) 64 = _
    rw [hsp]
    exact hreturn.2
  have hbv : returnBoundary v = returnBoundary initial := by
    change ({rip := stackTop v, rsp := stackPtr v + 8#64} : ReturnBoundary) =
      {rip := stackTop initial, rsp := stackPtr initial + 8#64}
    rw [htopv, hsp]
  have hmodel : pairDecodeResult [alphabet] input capacity =
      if (decodeLoop [alphabet] input).2 = 0#8 then .ok (decodeLoop [alphabet] input).1
      else .error .invalidEncoding := by
    rw [decodeResult_loop _ _ _ (by cases alphabet <;> simp), ite_eq_right (by omega)]
    rfl
  have habi {t : RamState}
      (hft : AgreesExcept [.mem (initial.regValue .rdx) 8, .reg 0, .reg 4, .flags, .rip] v t) :
      CalleeSavedRegistersUnchanged initial t ∧ DirectionFlagUnset t ∧
      AgreesExcept (.mem (initial.regValue .rdx) 8 :: decodeCallEffects initial (input.length / 2)) initial t := by
    have hf : AgreesExcept (.mem (initial.regValue .rdx) 8 :: decodeCallEffects initial (input.length / 2)) initial t :=
      (hfiv.trans hft).mono (by simp [decodeCallEffects, decodeLoopEffects])
    refine ⟨?_, hf.directionFlagClear (by simp [decodeCallEffects, decodeLoopEffects]) hv.directionFlagUnset, hf⟩
    intro reg hreg
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hreg
    rcases hreg with rfl | rfl | rfl | rfl | rfl | rfl
    · exact (hft.read (n := 64) (r := 3) (by simp)).trans (hbxv.trans hbx)
    · exact (hft.read (n := 64) (r := 5) (by simp)).trans (hbpv.trans hbp)
    · exact hf.read (n := 64) (r := 12) (by simp [decodeCallEffects, decodeLoopEffects])
    · exact hf.read (n := 64) (r := 13) (by simp [decodeCallEffects, decodeLoopEffects])
    · exact hf.read (n := 64) (r := 14) (by simp [decodeCallEffects, decodeLoopEffects])
    · exact hf.read (n := 64) (r := 15) (by simp [decodeCallEffects, decodeLoopEffects])
  by_cases hz : (decodeLoop [alphabet] input).2 = 0#8
  · have hpv' : v.RIP = decodeAddress alphabet + 246#64 := by simpa only [hz, ite_true] using hpv
    have hsuccess : ∃ output, pairDecodeResult [alphabet] input capacity = .ok output :=
      ⟨_, by rw [hmodel, ite_eq_left hz]⟩
    obtain ⟨hwl, hlcode, hlstack, hloutput⟩ := decode_length_output_ready hv hsuccess hfiv hcapacity
    have hdx : AddrMode.reg64 2 v = initial.regValue .rdx :=
      (hfv.read (by simp)).trans h.rdx
    have hlen : AddrMode.reg64 9 v = BitVec.ofNat 64 (input.length / 2) :=
      (hfv.read (by simp)).trans h.r9
    have haddr : storeAddrAt v.RIP (.base 2 .none) 3 v = initial.regValue .rdx := by
      simpa [storeAddrAt, AddrMode.addr, Disp.value] using hdx
    have hpre : Base16ct.Proofs.Copied.Md5.Proofs.Memory.StorePre v.RIP 3 (storeAddrAt v.RIP (.base 2 .none) 3) 8 v := by
      refine ⟨rfl, ?_, ?_⟩
      · rw [haddr]; exact hwl
      · rw [haddr]
        intro i hi j hj heq
        apply hlcode i hi
        rw [heq, hpv']
        have hj' : j = 0 ∨ j = 1 ∨ j = 2 := by omega
        rcases hj' with rfl | rfl | rfl
        · exact ⟨0x4c, by cases alphabet <;> decide +kernel⟩
        · exact ⟨0x89, by cases alphabet <;> decide +kernel⟩
        · exact ⟨0x0a, by cases alphabet <;> decide +kernel⟩
    have havoid : (movM64R64Effect v.RIP 9 (.base 2 .none) v).Avoids programImage := by
      intro x hx c hc hcov
      have hcomps : (movM64R64Effect v.RIP 9 (.base 2 .none) v).components =
          [.mem (initial.regValue .rdx) 8, .rip] := by
        simp only [movM64R64Effect_components]
        have hh : storeAddrAt v.RIP (.base 2 .none) (3 + (AddrMode.base 2 .none).tail.length) v = initial.regValue .rdx := by
          simpa [storeAddrAt, AddrMode.addr, Disp.value] using hdx
        rw [hh]
      rw [hcomps] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · obtain ⟨i, hi, heq⟩ := hcov
        exact hlcode i hi ⟨x.2, heq ▸ hx⟩
      · exact hcov
    obtain ⟨t, hat, hrt, hft, hax, hlength⟩ := decode_success_suffix hev hpv' hpre havoid hreadv
      (by rw [hdx, hsp]; exact hlstack)
      (by rw [htopv]; exact hb.1) (by rw [htopv]; exact hb.2)
    rw [hbv] at hat
    rw [hdx] at hft hlength
    obtain ⟨hcallee, hdf, hf⟩ := habi hft
    refine ⟨8, t, hav.returns hat, hrt, hcallee, hdf, hf, ?_⟩
    rw [hmodel, ite_eq_left hz]
    simp only [decodeLoop_length]
    have hfst : AgreesExcept [.mem (initial.regValue .rdx) 8, .reg 0, .reg 3, .reg 4, .reg 5, .flags, .rip] s t :=
      (hfv.trans hft).mono (by simp)
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa [SuccessfulStatus, AddrMode.reg64, Operand.read, State.regValue,
        gprIndex, Syntax.Reg.fin] using congrArg (fun x : BitVec 64 => x.setWidth 32) hax
    · intro a ha
      have hbytes : t.external[a]? = s.external[a]? := by
        apply hfst.byte
        intro c hc hcover
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> try exact hcover
        obtain ⟨i, hi, heq⟩ := hcover
        apply ha (lengthOutputRegion initial) (by simp)
        rw [heq]
        simpa [lengthOutputRegion, registerRegion, BitVec.ofNat_add] using
          (region_contains_offset (hv.lengthOutputInMemoryIfLengthWritten hsuccess).1 hi)
      rw [hbytes]
      apply h.frame a
      intro region hr hin
      apply ha region ?_ hin
      have hr' : region = outputRegion initial (input.length / 2) ∨
          region = Stack.region initial (decodeRoutine alphabet).minStackBytes := by simpa using hr
      rcases hr' with rfl | rfl <;> simp
    · have hbytes : ∀ j, j < input.length / 2 →
          t.external[initial.regValue .rcx + BitVec.ofNat 64 j]? =
            s.external[initial.regValue .rcx + BitVec.ofNat 64 j]? := by
        intro j hj
        apply hfst.byte
        intro c hc hcover
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> try exact hcover
        obtain ⟨i, hi, heq⟩ := hcover
        exact hloutput i hi j (by omega) heq.symm
      rw [Base16ct.Proofs.readOutput_congr_prefix hbytes, readOutput_eq, h.output]
      rfl
    · apply Base16ct.Proofs.readLengthOutput_of_operand_read
      · exact ⟨hwl.low, fun i hi => hft.grow _ (hwl.bytes i hi)⟩
      · exact hlength.trans hlen
  · have hpv' : v.RIP = decodeAddress alphabet + 240#64 := by simpa only [hz, ite_false] using hpv
    obtain ⟨t, hat, hrt, hft⟩ := decode_return_suffix hev hpv' (Or.inl rfl) hreadv
      (by rw [htopv]; exact hb.1)
    rw [hbv] at hat
    obtain ⟨hcallee, hdf, hf⟩ := habi (hft.mono (by simp))
    refine ⟨6, t, hav.returns hat, hrt, hcallee, hdf, hf, ?_⟩
    rw [hmodel, ite_eq_right hz]
    have hax : AddrMode.reg64 0 t = 2#64 := (hft.read (by simp)).trans haxv
    refine ⟨?_, ?_⟩
    · simpa [FailureStatus, invalidEncodingStatus, AddrMode.reg64,
        Operand.read, State.regValue, gprIndex, Syntax.Reg.fin] using
        congrArg (fun x : BitVec 64 => x.setWidth 32) hax
    · have hmt := (hfv.trans hft).external (by simp [Component.Covers])
      intro address hout
      rw [hmt]
      exact h.frame address hout
end Base16ct.Proofs.Base16ctUpperDecodeCorrect
