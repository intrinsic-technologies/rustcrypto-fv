import Base16ct.Proofs.Base16ctUpperDecodeCorrect.Entry
import Base16ct.Proofs.Base16ctUpperDecodeCorrect.Decoder
import Base16ct.Proofs.Base16ctUpperDecodeCorrect.LoopStep.Instructions.OrImm
import Base16ct.Proofs.Base16ctUpperDecodeCorrect.LoopStep.Instructions.Cmov
import Base16ct.Proofs.Base16ctUpperDecodeCorrect.LoopStep.Instructions.Movsx
import Base16ct.Proofs.Base16ctUpperDecodeCorrect.LoopStep.Instructions.Lea32
import Base16ct.Proofs.Base16ctUpperDecodeCorrect.LoopStep.Instructions.Shift
import Base16ct.Proofs.Base16ctUpperDecodeCorrect.LoopStep.Instructions.Byte
import Base16ct.Proofs.Base16ctUpperDecodeCorrect.LoopStep.Instructions.OrReg
import Base16ct.Proofs.Base16ctUpperDecodeCorrect.LoopStep.Instructions.StoreImage
import X86Proofs

namespace Base16ct.Proofs.Base16ctUpperDecodeCorrect.Instructions

variable {alphabet : Base16ct.Proofs.Base16ctUpperDecodeCorrect.RFC4648.Alphabet}

open Base16ct.Spec Base16ct.Spec.Program Base16ct.Spec.Program.Extracted
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem advanceAt [bindings : Bindings] {s : RamState} {boundary : ReturnBoundary}
    {p : BitVec 64} {bytes : List UInt8} {e : RamState → Effect}
    (hstep : StepEffect (fun u => u.RIP = p) (codeRange p bytes) e)
    (hready : ReadyToStep s) (hcode : CodeIn programImage s)
    (hsub : ∀ x ∈ codeRange p bytes, x ∈ programImage)
    (hp : s.RIP = p) (hret : ¬ InProgram boundary.rip)
    (hnext : InProgram (e s).rip) (havoid : (e s).Avoids programImage) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ CodeIn programImage t ∧
      (e s).Holds s t := by
  apply advanceInProgram hstep hready hcode hsub
  · exact hp
  · exact hret
  · exact hnext
  · exact havoid

theorem advanceAtOffset [bindings : Bindings] {s : RamState} {boundary : ReturnBoundary}
    (entry : BitVec 64) (offset : Nat) {bytes : List UInt8} {e : RamState → Effect}
    (hstep : StepEffect (fun u => u.RIP = entry + BitVec.ofNat 64 offset)
      (codeRange (entry + BitVec.ofNat 64 offset) bytes) e)
    (hready : ReadyToStep s) (hcode : CodeIn programImage s)
    (hsub : ∀ x ∈ codeRange (entry + BitVec.ofNat 64 offset) bytes, x ∈ programImage)
    (hp : s.RIP = entry + BitVec.ofNat 64 offset) (hret : ¬ InProgram boundary.rip)
    (hnext : InProgram (e s).rip) (havoid : (e s).Avoids programImage) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ CodeIn programImage t ∧
      (e s).Holds s t := by
  exact advanceAt hstep hready hcode hsub hp hret hnext havoid

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem entryReadyAfter [bindings : Bindings] {s t : RamState} {e : RamState → Effect}
    (hentry : EntryReady programImage s) (hready : ReadyToStep t)
    (hcode : CodeIn programImage t) (heffect : (e s).Holds s t) :
    EntryReady programImage t :=
  ⟨hready, SupportedSSE.of_agreesExcept heffect.agrees hentry.sse, hcode⟩

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem decode_loop_load [bindings : Bindings] {s : RamState} {boundary : ReturnBoundary}
    (hentry : EntryReady programImage s) (hp : s.RIP = (decodeAddress alphabet) + 48#64)
    (hload : MemReadable s
      ((AddrMode.sib 7 (some 0) 1#2 .none).addr s (BitVec.add s.RIP (5#64))) 1)
    (hret : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ CodeIn programImage t ∧
      (movzxR32M8Effect s.RIP 5 (gprNumber 0 (rexR (0x44#8)) (0#3))
        (AddrMode.sib 7 (some 0) 1#2 .none) s).Holds s t := by
  let am : AddrMode := .sib 7 (some 0) 1#2 .none
  have hrex : RexNoWPrefix (0x44#8) := by unfold RexNoWPrefix; decide
  have hs := movzx_r_m8_rex_effect_step (p := s.RIP) (rex := 0x44)
      (by unfold RexPrefix; decide) (n := 32) (by decide) (by
        intro seg
        exact hrex.operand_size seg) (reg := 0#3) (am := am) (by unfold am; first | decide | (cases alphabet <;> decide))
      (by unfold am; first | decide | (cases alphabet <;> decide)) (by unfold am; first | decide | (cases alphabet <;> decide))
  apply advanceInProgram hs hentry.ready hentry.code
  · intro x hx
    obtain ⟨i, rfl⟩ := (mem_codeRange_iff _ _ _).mp hx
    change Fin 5 at i
    clear hx
    finite_cases i
    all_goals rw [hp]
    all_goals (cases alphabet <;> decide +kernel)
  · exact ⟨by rfl, hload⟩
  · exact hret
  · change InProgram (BitVec.add s.RIP (5#64))
    rw [hp]
    exact ⟨0x41, by (cases alphabet <;> decide +kernel)⟩
  · exact Effect.avoids_of_components_reg_rip
      (movzxR32M8Effect_components _ _ _ _ _) _

set_option maxRecDepth 100000 in
theorem decode_loop_load_second [bindings : Bindings] {s : RamState} {boundary : ReturnBoundary}
    (hentry : EntryReady programImage s) (hp : s.RIP = (decodeAddress alphabet) + 132#64)
    (hload : MemReadable s
      ((AddrMode.sib 7 (some 0) 1#2 (.d8 1)).addr s (BitVec.add s.RIP (6#64))) 1)
    (hret : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ CodeIn programImage t ∧
      (movzxR32M8Effect s.RIP 6 (gprNumber 0 (rexR (0x44#8)) (2#3))
        (AddrMode.sib 7 (some 0) 1#2 (.d8 1)) s).Holds s t := by
  let am : AddrMode := .sib 7 (some 0) 1#2 (.d8 1)
  have hrex : RexNoWPrefix (0x44#8) := by unfold RexNoWPrefix; decide
  have hs := movzx_r_m8_rex_effect_step (p := s.RIP) (rex := 0x44)
      (by unfold RexPrefix; decide) (n := 32) (by decide) (by
        intro seg
        exact hrex.operand_size seg) (reg := 2#3) (am := am) (by unfold am; first | decide | (cases alphabet <;> decide))
      (by unfold am; first | decide | (cases alphabet <;> decide)) (by unfold am; first | decide | (cases alphabet <;> decide))
  apply advanceInProgram hs hentry.ready hentry.code
  · intro x hx
    obtain ⟨i, rfl⟩ := (mem_codeRange_iff _ _ _).mp hx
    change Fin 6 at i
    clear hx
    finite_cases i
    all_goals rw [hp]
    all_goals (cases alphabet <;> decide +kernel)
  · exact ⟨by rfl, hload⟩
  · exact hret
  · change InProgram (BitVec.add s.RIP (6#64))
    rw [hp]
    exact ⟨0x41, by (cases alphabet <;> decide +kernel)⟩
  · exact Effect.avoids_of_components_reg_rip
      (movzxR32M8Effect_components _ _ _ _ _) _

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem decode_loop_mov_r9 [bindings : Bindings] {s : RamState} {boundary : ReturnBoundary}
    (hentry : EntryReady programImage s)
    (hp : s.RIP = (decodeAddress alphabet) + 53#64)
    (hret : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ CodeIn programImage t ∧
      (movR32Imm32Effect s.RIP 6 (gprNumber 0 (rexB (0x41#8)) (opcodeReg 0xba))
        (0x2f#32) s).Holds s t := by
  have hs := mov_r32_imm32_rex_effect_step
      (p := (decodeAddress alphabet) + 53#64) (rex := 0x41) (op := 0xba)
      (imm := 0x2f#32) (by unfold RexNoWPrefix; decide) (by decide)
  obtain ⟨t, ha, hr, hc, he⟩ :=
    advanceAtOffset (entry := (decodeAddress alphabet)) (offset := 53) hs hentry.ready hentry.code
      (by
        intro x hx
        obtain ⟨i, rfl⟩ := (mem_codeRange_iff _ _ _).mp hx
        change Fin 6 at i
        clear hx
        finite_cases i <;> (cases alphabet <;> decide +kernel))
      hp hret
      (by
        change InProgram (BitVec.add ((decodeAddress alphabet) + 53#64) (6#64))
        exact ⟨0x45, by (cases alphabet <;> decide +kernel)⟩)
      (Effect.avoids_of_components_reg_rip
        (movR32Imm32Effect_components _ _ _ _ _) _)
  exact ⟨t, ha, hr, hc, by simpa [hp] using he⟩

set_option maxRecDepth 100000 in
theorem decode_loop_dec_ebx [bindings : Bindings] {s : RamState} {boundary : ReturnBoundary}
    (hentry : EntryReady programImage s)
    (hp : s.RIP = (decodeAddress alphabet) + 203#64)
    (hret : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ CodeIn programImage t ∧
      (decR32Effect s.RIP 2 (gprNumber 0 0 (modrmRm 0xcb)) s).Holds s t := by
  have hs := dec_r32_effect_step
      (p := (decodeAddress alphabet) + 203#64) (modrm := 0xcb) (by decide) (by decide)
  obtain ⟨t, ha, hr, hc, he⟩ :=
    advanceAtOffset (entry := (decodeAddress alphabet)) (offset := 203) hs hentry.ready hentry.code
      (by
        intro x hx
        obtain ⟨i, rfl⟩ := (mem_codeRange_iff _ _ _).mp hx
        change Fin 2 at i
        clear hx
        finite_cases i <;> (cases alphabet <;> decide +kernel))
      hp hret
      (by
        change InProgram (BitVec.add ((decodeAddress alphabet) + 203#64) (2#64))
        exact ⟨0x44, by (cases alphabet <;> decide +kernel)⟩)
      (decR32Effect_avoids _ _ _ _ _)
  exact ⟨t, ha, hr, hc, by simpa [hp] using he⟩

set_option maxRecDepth 100000 in
theorem decode_loop_or_r8_ebx [bindings : Bindings] {s : RamState} {boundary : ReturnBoundary}
    (hentry : EntryReady programImage s)
    (hp : s.RIP = (decodeAddress alphabet) + 205#64)
    (hret : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ CodeIn programImage t ∧
      (orR32R32Effect s.RIP 3 (gprNumber 0 (rexB (0x44#8)) (modrmRm 0xc3))
        (gprNumber 0 (rexR (0x44#8)) (modrmReg 0xc3)) s).Holds s t := by
  have hs := or_r32_r32_rex_effect_step
      (p := (decodeAddress alphabet) + 205#64) (rex := 0x44) (modrm := 0xc3)
      (by unfold RexNoWPrefix; decide) (by decide)
  obtain ⟨t, ha, hr, hc, he⟩ :=
    advanceAtOffset (entry := (decodeAddress alphabet)) (offset := 205) hs hentry.ready hentry.code
      (by
        intro x hx
        obtain ⟨i, rfl⟩ := (mem_codeRange_iff _ _ _).mp hx
        change Fin 3 at i
        clear hx
        finite_cases i <;> (cases alphabet <;> decide +kernel))
      hp hret
      (by
        change InProgram (BitVec.add ((decodeAddress alphabet) + 205#64) (3#64))
        exact ⟨0x88, by (cases alphabet <;> decide +kernel)⟩)
      (Effect.Avoids.of_noMem (by simp [Effect.components, orR32R32Effect, Component.Covers]) _)
  exact ⟨t, ha, hr, hc, by simpa [hp] using he⟩

set_option maxRecDepth 100000 in
theorem decode_loop_inc_rsi [bindings : Bindings] {s : RamState} {boundary : ReturnBoundary}
    (hentry : EntryReady programImage s)
    (hp : s.RIP = (decodeAddress alphabet) + 211#64)
    (hret : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ CodeIn programImage t ∧
      (incR64Effect s.RIP (gprNumber 0 (rexB (0x48#8)) (modrmRm 0xc0)) s).Holds s t := by
  have hs := inc_r64_effect_step
      (p := (decodeAddress alphabet) + 211#64) (rex := 0x48) (modrm := 0xc0)
      (by unfold RexWPrefix; decide) (by decide) (by decide)
  obtain ⟨t, ha, hr, hc, he⟩ :=
    advanceAtOffset (entry := (decodeAddress alphabet)) (offset := 211) hs hentry.ready hentry.code
      (by
        intro x hx
        obtain ⟨i, rfl⟩ := (mem_codeRange_iff _ _ _).mp hx
        change Fin 3 at i
        clear hx
        finite_cases i <;> (cases alphabet <;> decide +kernel))
      hp hret
      (by
        change InProgram (BitVec.add ((decodeAddress alphabet) + 211#64) (3#64))
        exact ⟨0x0f, by (cases alphabet <;> decide +kernel)⟩)
      (incR64Effect_avoids _ _ s programImage)
  exact ⟨t, ha, hr, hc, by simpa [hp] using he⟩

set_option maxRecDepth 100000 in
theorem decode_loop_movzx_ebx_bh [bindings : Bindings] {s : RamState} {boundary : ReturnBoundary}
    (hentry : EntryReady programImage s)
    (hp : s.RIP = (decodeAddress alphabet) + 214#64)
    (hret : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ CodeIn programImage t ∧
      (movzxEbxBhEffect s.RIP s).Holds s t := by
  have hs := movzx_ebx_bh_effect_step (p := (decodeAddress alphabet) + 214#64)
  obtain ⟨t, ha, hr, hc, he⟩ :=
    advanceAtOffset (entry := (decodeAddress alphabet)) (offset := 214) hs hentry.ready hentry.code
      (by
        intro x hx
        obtain ⟨i, rfl⟩ := (mem_codeRange_iff _ _ _).mp hx
        change Fin 3 at i
        clear hx
        finite_cases i <;> (cases alphabet <;> decide +kernel))
      hp hret
      (by
        change InProgram (BitVec.add ((decodeAddress alphabet) + 214#64) (3#64))
        exact ⟨0x09, by (cases alphabet <;> decide +kernel)⟩)
      (Effect.avoids_of_components_reg_rip (by rfl) _)
  exact ⟨t, ha, hr, hc, by simpa [hp] using he⟩

set_option maxRecDepth 100000 in
theorem decode_loop_or_ebx_ecx [bindings : Bindings] {s : RamState} {boundary : ReturnBoundary}
    (hentry : EntryReady programImage s)
    (hp : s.RIP = (decodeAddress alphabet) + 217#64)
    (hret : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ CodeIn programImage t ∧
      (orR32R32Effect s.RIP 2 (gprNumber 0 0 (modrmRm 0xde))
        (gprNumber 0 0 (modrmReg 0xde)) s).Holds s t := by
  have hs := or_r32_r32_effect_step
      (p := (decodeAddress alphabet) + 217#64) (modrm := 0xde) (by decide)
  obtain ⟨t, ha, hr, hc, he⟩ :=
    advanceAtOffset (entry := (decodeAddress alphabet)) (offset := 217) hs hentry.ready hentry.code
      (by
        intro x hx
        obtain ⟨i, rfl⟩ := (mem_codeRange_iff _ _ _).mp hx
        change Fin 2 at i
        clear hx
        finite_cases i <;> (cases alphabet <;> decide +kernel))
      hp hret
      (by
        change InProgram (BitVec.add ((decodeAddress alphabet) + 217#64) (2#64))
        exact ⟨0x49, by (cases alphabet <;> decide +kernel)⟩)
      (Effect.Avoids.of_noMem (by simp [Effect.components, orR32R32Effect, Component.Covers]) _)
  exact ⟨t, ha, hr, hc, by simpa [hp] using he⟩

set_option maxRecDepth 100000 in
theorem decode_loop_cmp_rax_rsi [bindings : Bindings] {s : RamState} {boundary : ReturnBoundary}
    (hentry : EntryReady programImage s)
    (hp : s.RIP = (decodeAddress alphabet) + 219#64)
    (hret : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ CodeIn programImage t ∧
      (cmpR64R64Effect s.RIP (gprNumber 0 (rexB (0x49#8)) (modrmRm 0xc1))
        (gprNumber 0 (rexR (0x49#8)) (modrmReg 0xc1)) s).Holds s t := by
  have hs := cmp_r64_r64_effect_step
      (p := (decodeAddress alphabet) + 219#64) (rex := 0x49) (modrm := 0xc1)
      (by unfold RexWPrefix; decide) (by decide)
  obtain ⟨t, ha, hr, hc, he⟩ :=
    advanceAtOffset (entry := (decodeAddress alphabet)) (offset := 219) hs hentry.ready hentry.code
      (by
        intro x hx
        obtain ⟨i, rfl⟩ := (mem_codeRange_iff _ _ _).mp hx
        change Fin 3 at i
        clear hx
        finite_cases i <;> (cases alphabet <;> decide +kernel))
      hp hret
      (by
        change InProgram (BitVec.add ((decodeAddress alphabet) + 219#64) (3#64))
        exact ⟨0x0f, by (cases alphabet <;> decide +kernel)⟩)
      (Effect.Avoids.of_noMem (by simp [Effect.components, cmpR64R64Effect, Component.Covers]) _)
  exact ⟨t, ha, hr, hc, by simpa [hp] using he⟩

set_option maxRecDepth 100000 in
theorem decode_loop_add_ebx_r10 [bindings : Bindings] {s : RamState}
    {boundary : ReturnBoundary} (hentry : EntryReady programImage s)
    (hp : s.RIP = (decodeAddress alphabet) + 200#64)
    (hret : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ CodeIn programImage t ∧
      (addR32R32Effect s.RIP 3 (gprNumber 0 (rexB (0x44#8)) (modrmRm 0xd3))
        (gprNumber 0 (rexR (0x44#8)) (modrmReg 0xd3)) s).Holds s t := by
  have hs := add_r32_r32_rex_effect_step
      (p := (decodeAddress alphabet) + 200#64) (rex := 0x44) (modrm := 0xd3)
      (by unfold RexNoWPrefix; decide) (by decide)
  obtain ⟨t, ha, hr, hc, he⟩ :=
    advanceAtOffset (entry := (decodeAddress alphabet)) (offset := 200) hs hentry.ready hentry.code
      (by
        intro x hx
        obtain ⟨i, rfl⟩ := (mem_codeRange_iff _ _ _).mp hx
        change Fin 3 at i
        clear hx
        finite_cases i <;> (cases alphabet <;> decide +kernel))
      hp hret
      (by
        change InProgram (BitVec.add ((decodeAddress alphabet) + 200#64) (3#64))
        exact ⟨0xff, by (cases alphabet <;> decide +kernel)⟩)
      (addR32R32Effect_avoids _ _ _ _ _ _)
  exact ⟨t, ha, hr, hc, by simpa [hp] using he⟩

set_option maxRecDepth 100000 in
theorem decode_loop_sub_r9_r8 [bindings : Bindings] {s : RamState}
    {boundary : ReturnBoundary} (hentry : EntryReady programImage s)
    (hp : s.RIP = (decodeAddress alphabet) + 59#64)
    (hret : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ CodeIn programImage t ∧
      (subR32R32Effect s.RIP 3 (gprNumber 0 (rexB (0x45#8)) (modrmRm 0xc2))
        (gprNumber 0 (rexR (0x45#8)) (modrmReg 0xc2)) s).Holds s t := by
  have hs := sub_r32_r32_rex_effect_step
      (p := (decodeAddress alphabet) + 59#64) (rex := 0x45) (modrm := 0xc2)
      (by unfold RexNoWPrefix; decide) (by decide)
  obtain ⟨t, ha, hr, hc, he⟩ :=
    advanceAtOffset (entry := (decodeAddress alphabet)) (offset := 59) hs hentry.ready hentry.code
      (by
        intro x hx
        obtain ⟨i, rfl⟩ := (mem_codeRange_iff _ _ _).mp hx
        change Fin 3 at i
        clear hx
        finite_cases i <;> (cases alphabet <;> decide +kernel))
      hp hret
      (by
        change InProgram (BitVec.add ((decodeAddress alphabet) + 59#64) (3#64))
        exact ⟨0x45, by (cases alphabet <;> decide +kernel)⟩)
      (subR32R32Effect_avoids _ _ _ _ _ _)
  exact ⟨t, ha, hr, hc, by simpa [hp] using he⟩

set_option maxRecDepth 100000 in
theorem decode_loop_and_r10_r9 [bindings : Bindings] {s : RamState}
    {boundary : ReturnBoundary} (hentry : EntryReady programImage s)
    (hp : s.RIP = (decodeAddress alphabet) + 66#64)
    (hret : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ CodeIn programImage t ∧
      (andR32R32Effect s.RIP 3 (gprNumber 0 (rexB (0x45#8)) (modrmRm 0xd3))
        (gprNumber 0 (rexR (0x45#8)) (modrmReg 0xd3)) s).Holds s t := by
  have hs := and_r32_r32_rex_effect_step
      (p := (decodeAddress alphabet) + 66#64) (rex := 0x45) (modrm := 0xd3)
      (by unfold RexNoWPrefix; decide) (by decide)
  obtain ⟨t, ha, hr, hc, he⟩ :=
    advanceAtOffset (entry := (decodeAddress alphabet)) (offset := 66) hs hentry.ready hentry.code
      (by
        intro x hx
        obtain ⟨i, rfl⟩ := (mem_codeRange_iff _ _ _).mp hx
        change Fin 3 at i
        clear hx
        finite_cases i <;> (cases alphabet <;> decide +kernel))
      hp hret
      (by
        change InProgram (BitVec.add ((decodeAddress alphabet) + 66#64) (3#64))
        exact ⟨0x45, by (cases alphabet <;> decide +kernel)⟩)
      (andR32R32Effect_avoids _ _ _ _ _ _)
  exact ⟨t, ha, hr, hc, by simpa [hp] using he⟩

set_option maxRecDepth 100000 in
theorem decode_loop_movsx_r9_r10 [bindings : Bindings] {s : RamState}
    {boundary : ReturnBoundary} (hentry : EntryReady programImage s)
    (hp : s.RIP = (decodeAddress alphabet) + 69#64)
    (hret : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ CodeIn programImage t ∧
      (movsxR32R16Effect s.RIP (gprNumber 0 (rexR (0x45#8)) (modrmReg 0xd3))
        (gprNumber 0 (rexB (0x45#8)) (modrmRm 0xd3)) s).Holds s t := by
  have hs := movsx_r32_r16_rex_effect_step
      (p := (decodeAddress alphabet) + 69#64) (rex := 0x45) (modrm := 0xd3)
      (by unfold RexNoWPrefix; decide) (by decide)
  obtain ⟨t, ha, hr, hc, he⟩ :=
    advanceAtOffset (entry := (decodeAddress alphabet)) (offset := 69) hs hentry.ready hentry.code
      (by
        intro x hx
        obtain ⟨i, rfl⟩ := (mem_codeRange_iff _ _ _).mp hx
        change Fin 4 at i
        clear hx
        finite_cases i <;> (cases alphabet <;> decide +kernel))
      hp hret
      (by
        change InProgram (BitVec.add ((decodeAddress alphabet) + 69#64) (4#64))
        exact ⟨0x41, by (cases alphabet <;> decide +kernel)⟩)
      (Effect.avoids_of_components_reg_rip (by rfl) _)
  exact ⟨t, ha, hr, hc, by simpa [hp] using he⟩

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem decode_loop_lea_r10_r8 [bindings : Bindings] {s : RamState}
    {boundary : ReturnBoundary} (hentry : EntryReady programImage s)
    (hp : s.RIP = (decodeAddress alphabet) + 62#64)
    (hret : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ CodeIn programImage t ∧
      (leaR32Effect s.RIP 4 (gprNumber 0 (rexR (0x45#8)) (3#3))
        (.base 8 (.d8 0xc6)) s).Holds s t := by
  let am : AddrMode := .base 8 (.d8 0xc6)
  have hs := lea_r32_effect_step
      (p := (decodeAddress alphabet) + 62#64) (rex := 0x45) (reg := 3#3) (am := am)
      (by unfold RexNoWPrefix; decide) (by unfold am; first | decide | (cases alphabet <;> decide))
      (by unfold am; first | decide | (cases alphabet <;> decide)) (by unfold am; first | decide | (cases alphabet <;> decide))
  obtain ⟨t, ha, hr, hc, he⟩ :=
    advanceAtOffset (entry := (decodeAddress alphabet)) (offset := 62) hs hentry.ready hentry.code
      (by
        intro x hx
        obtain ⟨i, rfl⟩ := (mem_codeRange_iff _ _ _).mp hx
        change Fin 4 at i
        clear hx
        finite_cases i <;> (cases alphabet <;> decide +kernel))
      hp hret
      (by
        change InProgram (BitVec.add ((decodeAddress alphabet) + 62#64) (4#64))
        exact ⟨0x45, by (cases alphabet <;> decide +kernel)⟩)
      (Effect.avoids_of_components_reg_rip (by rfl) _)
  dsimp [am] at he
  change (leaR32Effect ((decodeAddress alphabet) + 62#64) 4
      (gprNumber 0 (rexR (0x45#8)) (3#3)) (.base 8 (.d8 0xc6)) s).Holds s t at he
  exact ⟨t, ha, hr, hc, by simpa [hp] using he⟩

set_option maxRecDepth 100000 in
theorem decode_loop_lea_r11_r9 [bindings : Bindings] {s : RamState}
    {boundary : ReturnBoundary} (hentry : EntryReady programImage s)
    (hp : s.RIP = (decodeAddress alphabet) + 162#64)
    (hret : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ CodeIn programImage t ∧
      (leaR32Effect s.RIP 4 (gprNumber 0 (rexR (0x41#8)) (3#3))
        (.base 10 (.d8 0xd1)) s).Holds s t := by
  let am : AddrMode := .base 10 (.d8 0xd1)
  have hs := lea_r32_effect_step
      (p := (decodeAddress alphabet) + 162#64) (rex := 0x41) (reg := 3#3) (am := am)
      (by unfold RexNoWPrefix; decide) (by unfold am; first | decide | (cases alphabet <;> decide))
      (by unfold am; first | decide | (cases alphabet <;> decide)) (by unfold am; first | decide | (cases alphabet <;> decide))
  obtain ⟨t, ha, hr, hc, he⟩ :=
    advanceAtOffset (entry := (decodeAddress alphabet)) (offset := 162) hs hentry.ready hentry.code
      (by
        intro x hx
        obtain ⟨i, rfl⟩ := (mem_codeRange_iff _ _ _).mp hx
        change Fin 4 at i
        clear hx
        finite_cases i <;> (cases alphabet <;> decide +kernel))
      hp hret
      (by
        change InProgram (BitVec.add ((decodeAddress alphabet) + 162#64) (4#64))
        exact ⟨0x44, by (cases alphabet <;> decide +kernel)⟩)
      (Effect.avoids_of_components_reg_rip (by rfl) _)
  dsimp [am] at he
  change (leaR32Effect ((decodeAddress alphabet) + 162#64) 4
      (gprNumber 0 (rexR (0x41#8)) (3#3)) (.base 10 (.d8 0xd1)) s).Holds s t at he
  exact ⟨t, ha, hr, hc, by simpa [hp] using he⟩

set_option maxRecDepth 100000 in
theorem decode_loop_lea_ebx_r9 [bindings : Bindings] {s : RamState}
    {boundary : ReturnBoundary} (hentry : EntryReady programImage s)
    (hp : s.RIP = (decodeAddress alphabet) + 178#64)
    (hret : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ CodeIn programImage t ∧
      (leaR32Effect s.RIP 4 (gprNumber 0 (rexR (0x41#8)) (5#3))
        (.base 10 (.d8 ((-(decodeLetterOffset alphabet + 7#32)).setWidth 8))) s).Holds s t := by
  let am : AddrMode := .base 10 (.d8 ((-(decodeLetterOffset alphabet + 7#32)).setWidth 8))
  have hs := lea_r32_effect_step
      (p := (decodeAddress alphabet) + 178#64) (rex := 0x41) (reg := 5#3) (am := am)
      (by unfold RexNoWPrefix; decide) (by unfold am; first | decide | (cases alphabet <;> decide))
      (by unfold am; first | decide | (cases alphabet <;> decide)) (by unfold am; first | decide | (cases alphabet <;> decide))
  obtain ⟨t, ha, hr, hc, he⟩ :=
    advanceAtOffset (entry := (decodeAddress alphabet)) (offset := 178) hs hentry.ready hentry.code
      (by
        intro x hx
        obtain ⟨i, rfl⟩ := (mem_codeRange_iff _ _ _).mp hx
        change Fin 4 at i
        clear hx
        finite_cases i <;> (cases alphabet <;> decide +kernel))
      hp hret
      (by
        change InProgram (BitVec.add ((decodeAddress alphabet) + 178#64) (4#64))
        exact ⟨0x44, by (cases alphabet <;> decide +kernel)⟩)
      (Effect.avoids_of_components_reg_rip (by rfl) _)
  dsimp [am] at he
  change (leaR32Effect ((decodeAddress alphabet) + 178#64) 4
      (gprNumber 0 (rexR (0x41#8)) (5#3)) (.base 10 (.d8 ((-(decodeLetterOffset alphabet + 7#32)).setWidth 8))) s).Holds s t at he
  exact ⟨t, ha, hr, hc, by simpa [hp] using he⟩

set_option maxRecDepth 100000 in
set_option maxRecDepth 100000 in
theorem decode_loop_shr_r9_first [bindings : Bindings] {s : RamState}
    {boundary : ReturnBoundary} (hentry : EntryReady programImage s)
    (hp : s.RIP = (decodeAddress alphabet) + 73#64)
    (hret : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ CodeIn programImage t ∧
      (shrR32Effect s.RIP 4 (gprNumber 0 (rexB (0x41#8)) (modrmRm 0xea))
        (shiftCount 32 (0x08#8)) s).Holds s t := by
  have hs := shr_r32_imm8_rex_effect_step
      (p := (decodeAddress alphabet) + 73#64) (rex := 0x41) (modrm := 0xea) (imm := 0x08)
      (by unfold RexNoWPrefix; decide) (by decide) (by decide)
  obtain ⟨t, ha, hr, hc, he⟩ :=
    advanceAtOffset (entry := (decodeAddress alphabet)) (offset := 73) hs hentry.ready hentry.code
      (by
        intro x hx
        obtain ⟨i, rfl⟩ := (mem_codeRange_iff _ _ _).mp hx
        change Fin 4 at i
        clear hx
        finite_cases i <;> (cases alphabet <;> decide +kernel))
      hp hret
      (by
        change InProgram (BitVec.add ((decodeAddress alphabet) + 73#64) (4#64))
        exact ⟨0x45, by (cases alphabet <;> decide +kernel)⟩)
      (Effect.Avoids.of_noMem (by simp [Effect.components, shrR32Effect, Component.Covers]) _)
  exact ⟨t, ha, hr, hc, by simpa [hp] using he⟩

set_option maxRecDepth 100000 in
theorem decode_loop_shr_r9_second [bindings : Bindings] {s : RamState}
    {boundary : ReturnBoundary} (hentry : EntryReady programImage s)
    (hp : s.RIP = (decodeAddress alphabet) + 107#64)
    (hret : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ CodeIn programImage t ∧
      (shrR32Effect s.RIP 4 (gprNumber 0 (rexB (0x41#8)) (modrmRm 0xea))
        (shiftCount 32 (0x08#8)) s).Holds s t := by
  have hs := shr_r32_imm8_rex_effect_step
      (p := (decodeAddress alphabet) + 107#64) (rex := 0x41) (modrm := 0xea) (imm := 0x08)
      (by unfold RexNoWPrefix; decide) (by decide) (by decide)
  obtain ⟨t, ha, hr, hc, he⟩ :=
    advanceAtOffset (entry := (decodeAddress alphabet)) (offset := 107) hs hentry.ready hentry.code
      (by
        intro x hx
        obtain ⟨i, rfl⟩ := (mem_codeRange_iff _ _ _).mp hx
        change Fin 4 at i
        clear hx
        finite_cases i <;> (cases alphabet <;> decide +kernel))
      hp hret
      (by
        change InProgram (BitVec.add ((decodeAddress alphabet) + 107#64) (4#64))
        exact ⟨0x41, by (cases alphabet <;> decide +kernel)⟩)
      (Effect.Avoids.of_noMem (by simp [Effect.components, shrR32Effect, Component.Covers]) _)
  exact ⟨t, ha, hr, hc, by simpa [hp] using he⟩

set_option maxRecDepth 100000 in
theorem decode_loop_sar_r10_first [bindings : Bindings] {s : RamState}
    {boundary : ReturnBoundary} (hentry : EntryReady programImage s)
    (hp : s.RIP = (decodeAddress alphabet) + 158#64)
    (hret : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ CodeIn programImage t ∧
      (sarR32Effect s.RIP 4 (gprNumber 0 (rexB (0x41#8)) (modrmRm 0xfb))
        (shiftCount 32 (0x08#8)) s).Holds s t := by
  have hs := sar_r32_imm8_rex_effect_step
      (p := (decodeAddress alphabet) + 158#64) (rex := 0x41) (modrm := 0xfb) (imm := 0x08)
      (by unfold RexNoWPrefix; decide) (by decide) (by decide)
  obtain ⟨t, ha, hr, hc, he⟩ :=
    advanceAtOffset (entry := (decodeAddress alphabet)) (offset := 158) hs hentry.ready hentry.code
      (by
        intro x hx
        obtain ⟨i, rfl⟩ := (mem_codeRange_iff _ _ _).mp hx
        change Fin 4 at i
        clear hx
        finite_cases i <;> (cases alphabet <;> decide +kernel))
      hp hret
      (by
        change InProgram (BitVec.add ((decodeAddress alphabet) + 158#64) (4#64))
        exact ⟨0x41, by (cases alphabet <;> decide +kernel)⟩)
      (Effect.Avoids.of_noMem (by simp [Effect.components, sarR32Effect, Component.Covers]) _)
  exact ⟨t, ha, hr, hc, by simpa [hp] using he⟩

set_option maxRecDepth 100000 in
theorem decode_loop_sar_r10_second [bindings : Bindings] {s : RamState}
    {boundary : ReturnBoundary} (hentry : EntryReady programImage s)
    (hp : s.RIP = (decodeAddress alphabet) + 189#64)
    (hret : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ CodeIn programImage t ∧
      (sarR32Effect s.RIP 4 (gprNumber 0 (rexB (0x41#8)) (modrmRm 0xfb))
        (shiftCount 32 (0x08#8)) s).Holds s t := by
  have hs := sar_r32_imm8_rex_effect_step
      (p := (decodeAddress alphabet) + 189#64) (rex := 0x41) (modrm := 0xfb) (imm := 0x08)
      (by unfold RexNoWPrefix; decide) (by decide) (by decide)
  obtain ⟨t, ha, hr, hc, he⟩ :=
    advanceAtOffset (entry := (decodeAddress alphabet)) (offset := 189) hs hentry.ready hentry.code
      (by
        intro x hx
        obtain ⟨i, rfl⟩ := (mem_codeRange_iff _ _ _).mp hx
        change Fin 4 at i
        clear hx
        finite_cases i <;> (cases alphabet <;> decide +kernel))
      hp hret
      (by
        change InProgram (BitVec.add ((decodeAddress alphabet) + 189#64) (4#64))
        exact ⟨0x41, by (cases alphabet <;> decide +kernel)⟩)
      (Effect.Avoids.of_noMem (by simp [Effect.components, sarR32Effect, Component.Covers]) _)
  exact ⟨t, ha, hr, hc, by simpa [hp] using he⟩

set_option maxRecDepth 100000 in
theorem decode_loop_lea_r10_r8_wide [bindings : Bindings] {s : RamState}
    {boundary : ReturnBoundary} (hentry : EntryReady programImage s)
    (hp : s.RIP = (decodeAddress alphabet) + 77#64)
    (hret : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ CodeIn programImage t ∧
      (leaR32Effect s.RIP 7 (gprNumber 0 (rexR (0x45#8)) (3#3))
        (.base 8 (.d32 0xfd1)) s).Holds s t := by
  let am : AddrMode := .base 8 (.d32 0xfd1)
  have hs := lea_r32_effect_step
      (p := (decodeAddress alphabet) + 77#64) (rex := 0x45) (reg := 3#3) (am := am)
      (by unfold RexNoWPrefix; decide) (by unfold am; first | decide | (cases alphabet <;> decide))
      (by unfold am; first | decide | (cases alphabet <;> decide)) (by unfold am; first | decide | (cases alphabet <;> decide))
  obtain ⟨t, ha, hr, hc, he⟩ :=
    advanceAtOffset (entry := (decodeAddress alphabet)) (offset := 77) hs hentry.ready hentry.code
      (by
        intro x hx
        obtain ⟨i, rfl⟩ := (mem_codeRange_iff _ _ _).mp hx
        change Fin 7 at i
        clear hx
        finite_cases i <;> (cases alphabet <;> decide +kernel))
      hp hret
      (by
        change InProgram (BitVec.add ((decodeAddress alphabet) + 77#64) (7#64))
        exact ⟨0x45, by (cases alphabet <;> decide +kernel)⟩)
      (Effect.avoids_of_components_reg_rip (by rfl) _)
  dsimp [am] at he
  change (leaR32Effect ((decodeAddress alphabet) + 77#64) 7
      (gprNumber 0 (rexR (0x45#8)) (3#3)) (.base 8 (.d32 0xfd1)) s).Holds s t at he
  exact ⟨t, ha, hr, hc, by simpa [hp] using he⟩

set_option maxRecDepth 100000 in
theorem decode_loop_lea_r11_r8 [bindings : Bindings] {s : RamState}
    {boundary : ReturnBoundary} (hentry : EntryReady programImage s)
    (hp : s.RIP = (decodeAddress alphabet) + 96#64)
    (hret : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ CodeIn programImage t ∧
      (leaR32Effect s.RIP 4 (gprNumber 0 (rexR (0x41#8)) (3#3))
        (.base 8 (.d8 ((-(decodeLetterOffset alphabet + 7#32)).setWidth 8))) s).Holds s t := by
  let am : AddrMode := .base 8 (.d8 ((-(decodeLetterOffset alphabet + 7#32)).setWidth 8))
  have hs := lea_r32_effect_step
      (p := (decodeAddress alphabet) + 96#64) (rex := 0x41) (reg := 3#3) (am := am)
      (by unfold RexNoWPrefix; decide) (by unfold am; first | decide | (cases alphabet <;> decide))
      (by unfold am; first | decide | (cases alphabet <;> decide)) (by unfold am; first | decide | (cases alphabet <;> decide))
  obtain ⟨t, ha, hr, hc, he⟩ :=
    advanceAtOffset (entry := (decodeAddress alphabet)) (offset := 96) hs hentry.ready hentry.code
      (by
        intro x hx
        obtain ⟨i, rfl⟩ := (mem_codeRange_iff _ _ _).mp hx
        change Fin 4 at i
        clear hx
        finite_cases i <;> (cases alphabet <;> decide +kernel))
      hp hret
      (by
        change InProgram (BitVec.add ((decodeAddress alphabet) + 96#64) (4#64))
        exact ⟨0x44, by (cases alphabet <;> decide +kernel)⟩)
      (Effect.avoids_of_components_reg_rip (by rfl) _)
  dsimp [am] at he
  change (leaR32Effect ((decodeAddress alphabet) + 96#64) 4
      (gprNumber 0 (rexR (0x41#8)) (3#3)) (.base 8 (.d8 ((-(decodeLetterOffset alphabet + 7#32)).setWidth 8))) s).Holds s t at he
  exact ⟨t, ha, hr, hc, by simpa [hp] using he⟩

set_option maxRecDepth 100000 in
theorem decode_loop_shl_r8 [bindings : Bindings] {s : RamState}
    {boundary : ReturnBoundary} (hentry : EntryReady programImage s)
    (hp : s.RIP = (decodeAddress alphabet) + 124#64)
    (hret : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ CodeIn programImage t ∧
      (shlR32Effect s.RIP 4 (gprNumber 0 (rexB (0x41#8)) (modrmRm 0xe0))
        (shiftCount 32 (0x04#8)) s).Holds s t := by
  have hs := shl_r32_imm8_rex_effect_step
      (p := (decodeAddress alphabet) + 124#64) (rex := 0x41) (modrm := 0xe0) (imm := 0x04)
      (by unfold RexNoWPrefix; decide) (by decide) (by decide)
  obtain ⟨t, ha, hr, hc, he⟩ :=
    advanceAtOffset (entry := (decodeAddress alphabet)) (offset := 124) hs hentry.ready hentry.code
      (by
        intro x hx
        obtain ⟨i, rfl⟩ := (mem_codeRange_iff _ _ _).mp hx
        change Fin 4 at i
        clear hx
        finite_cases i <;> (cases alphabet <;> decide +kernel))
      hp hret
      (by
        change InProgram (BitVec.add ((decodeAddress alphabet) + 124#64) (4#64))
        exact ⟨0x41, by (cases alphabet <;> decide +kernel)⟩)
      (Effect.Avoids.of_noMem (by simp [Effect.components, shlR32Effect, Component.Covers]) _)
  exact ⟨t, ha, hr, hc, by simpa [hp] using he⟩

set_option maxRecDepth 100000 in
theorem decode_loop_add_r8_minus16 [bindings : Bindings] {s : RamState}
    {boundary : ReturnBoundary} (hentry : EntryReady programImage s)
    (hp : s.RIP = (decodeAddress alphabet) + 128#64)
    (hret : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ CodeIn programImage t ∧
      (addR32Imm8Effect s.RIP 4 (gprNumber 0 (rexB (0x41#8)) (modrmRm 0xc0))
        (0xf0#8) s).Holds s t := by
  have hs := add_r32_imm8_rex_effect_step
      (p := (decodeAddress alphabet) + 128#64) (rex := 0x41) (modrm := 0xc0) (imm := 0xf0)
      (by unfold RexNoWPrefix; decide) (by decide) (by decide)
  obtain ⟨t, ha, hr, hc, he⟩ :=
    advanceAtOffset (entry := (decodeAddress alphabet)) (offset := 128) hs hentry.ready hentry.code
      (by
        intro x hx
        obtain ⟨i, rfl⟩ := (mem_codeRange_iff _ _ _).mp hx
        change Fin 4 at i
        clear hx
        finite_cases i <;> (cases alphabet <;> decide +kernel))
      hp hret
      (by
        change InProgram (BitVec.add ((decodeAddress alphabet) + 128#64) (4#64))
        exact ⟨0x44, by (cases alphabet <;> decide +kernel)⟩)
      (addR32Imm8Effect_avoids _ _ _ _ _ _)
  exact ⟨t, ha, hr, hc, by simpa [hp] using he⟩

set_option maxRecDepth 100000 in
theorem decode_loop_add_r8_letterOffset [bindings : Bindings] {s : RamState}
    {boundary : ReturnBoundary} (hentry : EntryReady programImage s)
    (hp : s.RIP = (decodeAddress alphabet) + 111#64)
    (hret : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ CodeIn programImage t ∧
      (addR32Imm32Effect s.RIP 7 (gprNumber 0 (rexB (0x41#8)) (modrmRm 0xc0))
        ((0x100a#32 - decodeLetterOffset alphabet)) s).Holds s t := by
  have hs := add_r32_imm32_rex_effect_step
      (p := (decodeAddress alphabet) + 111#64) (rex := 0x41) (modrm := 0xc0) (imm := (0x100a#32 - decodeLetterOffset alphabet))
      (by unfold RexNoWPrefix; decide) (by decide) (by decide)
  obtain ⟨t, ha, hr, hc, he⟩ :=
    advanceAtOffset (entry := (decodeAddress alphabet)) (offset := 111) hs hentry.ready hentry.code
      (by
        intro x hx
        obtain ⟨i, rfl⟩ := (mem_codeRange_iff _ _ _).mp hx
        change Fin 7 at i
        clear hx
        finite_cases i <;> (cases alphabet <;> decide +kernel))
      hp hret
      (by
        change InProgram (BitVec.add ((decodeAddress alphabet) + 111#64) (7#64))
        exact ⟨0x45, by (cases alphabet <;> decide +kernel)⟩)
      (addR32Imm32Effect_avoids _ _ _ _ _ _)
  exact ⟨t, ha, hr, hc, by simpa [hp] using he⟩

set_option maxRecDepth 100000 in
theorem decode_loop_add_r9_letterOffset [bindings : Bindings] {s : RamState}
    {boundary : ReturnBoundary} (hentry : EntryReady programImage s)
    (hp : s.RIP = (decodeAddress alphabet) + 193#64)
    (hret : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ CodeIn programImage t ∧
      (addR32Imm8Effect s.RIP 4 (gprNumber 0 (rexB (0x41#8)) (modrmRm 0xc2))
        (((10#32 - decodeLetterOffset alphabet).setWidth 8)) s).Holds s t := by
  have hs := add_r32_imm8_rex_effect_step
      (p := (decodeAddress alphabet) + 193#64) (rex := 0x41) (modrm := 0xc2) (imm := (10#32 - decodeLetterOffset alphabet).setWidth 8)
      (by unfold RexNoWPrefix; decide) (by decide) (by decide)
  obtain ⟨t, ha, hr, hc, he⟩ :=
    advanceAtOffset (entry := (decodeAddress alphabet)) (offset := 193) hs hentry.ready hentry.code
      (by
        intro x hx
        obtain ⟨i, rfl⟩ := (mem_codeRange_iff _ _ _).mp hx
        change Fin 4 at i
        clear hx
        finite_cases i <;> (cases alphabet <;> decide +kernel))
      hp hret
      (by
        change InProgram (BitVec.add ((decodeAddress alphabet) + 193#64) (4#64))
        exact ⟨0x45, by (cases alphabet <;> decide +kernel)⟩)
      (addR32Imm8Effect_avoids _ _ _ _ _ _)
  exact ⟨t, ha, hr, hc, by simpa [hp] using he⟩

set_option maxRecDepth 100000 in
theorem decode_loop_and_r32_advance [bindings : Bindings] {s : RamState}
    {boundary : ReturnBoundary} (entry : BitVec 64) (offset : Nat) (rex modrm : UInt8)
    (hentry : EntryReady programImage s) (hrex : RexNoWPrefix rex.toBitVec) (hmod : modrmMod modrm = 3)
    (hsub : ∀ x ∈ codeRange (entry + BitVec.ofNat 64 offset) [rex, 0x21, modrm], x ∈ programImage)
    (hp : s.RIP = entry + BitVec.ofNat 64 offset)
    (hnext : InProgram (BitVec.add (entry + BitVec.ofNat 64 offset) (3#64)))
    (hret : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ CodeIn programImage t ∧
      (andR32R32Effect s.RIP 3 (gprNumber 0 (rexB (rex.toBitVec)) (modrmRm modrm))
        (gprNumber 0 (rexR (rex.toBitVec)) (modrmReg modrm)) s).Holds s t := by
  have hs := and_r32_r32_rex_effect_step
      (p := entry + BitVec.ofNat 64 offset) (rex := rex) (modrm := modrm)
      hrex hmod
  obtain ⟨t, ha, hr, hc, he⟩ :=
    advanceAtOffset entry offset hs hentry.ready hentry.code
      hsub hp hret hnext (andR32R32Effect_avoids _ _ _ _ _ _)
  exact ⟨t, ha, hr, hc, by simpa [hp] using he⟩

set_option maxRecDepth 100000 in
theorem decode_loop_add_r32_advance [bindings : Bindings] {s : RamState}
    {boundary : ReturnBoundary} (entry : BitVec 64) (offset : Nat) (rex modrm : UInt8) (imm : BitVec 8)
    (hentry : EntryReady programImage s) (hrex : RexNoWPrefix rex.toBitVec)
    (hmod : modrmMod modrm = 3) (hreg : modrmReg modrm = 0)
    (hsub : ∀ x ∈ codeRange (entry + BitVec.ofNat 64 offset)
      (rex :: 0x83 :: modrm :: immBytes 8 imm), x ∈ programImage)
    (hp : s.RIP = entry + BitVec.ofNat 64 offset)
    (hnext : InProgram (BitVec.add (entry + BitVec.ofNat 64 offset) (4#64)))
    (hret : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ CodeIn programImage t ∧
      (addR32Imm8Effect s.RIP 4 (gprNumber 0 (rexB rex.toBitVec) (modrmRm modrm)) imm s).Holds s t := by
  have hs := add_r32_imm8_rex_effect_step
      (p := entry + BitVec.ofNat 64 offset) (rex := rex) (modrm := modrm) (imm := imm)
      hrex hmod hreg
  obtain ⟨t, ha, hr, hc, he⟩ :=
    advanceAtOffset entry offset hs hentry.ready hentry.code
      hsub hp hret hnext (addR32Imm8Effect_avoids _ _ _ _ _ _)
  exact ⟨t, ha, hr, hc, by simpa [hp] using he⟩

set_option maxRecDepth 100000 in
theorem decode_loop_jne [bindings : Bindings] {s : RamState} {boundary : ReturnBoundary}
    (hentry : EntryReady programImage s)
    (hp : s.RIP = (decodeAddress alphabet) + 222#64)
    (hret : ¬ InProgram boundary.rip) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ CodeIn programImage t ∧
      (jccEffect s.RIP 6 (5#4) ((0xffffff4c#32).signExtend 64) s).Holds s t := by
  have hs := jcc_rel32_effect_step (p := s.RIP) (cc := 5#4) (disp := 0xffffff4c#32)
  apply advanceInProgram hs hentry.ready hentry.code
  · intro x hx
    obtain ⟨i, rfl⟩ := (mem_codeRange_iff _ _ _).mp hx
    change Fin 6 at i
    clear hx
    finite_cases i
    all_goals rw [hp]
    all_goals simp [jccOpcode32, immBytes]
    all_goals (cases alphabet <;> decide +kernel)
  · constructor
    · rfl
    · intro _
      rw [hp]
      (cases alphabet <;> decide +kernel)
  · exact hret
  · unfold jccEffect branchEffect InProgram
    by_cases hc : condHolds (5#4) (StatusFlags.ofRFLAGS s.RFLAGS) = true
    · rw [hc]
      refine ⟨0x44, ?_⟩
      rw [hp]
      (cases alphabet <;> decide +kernel)
    · have hc' : condHolds (5#4) (StatusFlags.ofRFLAGS s.RFLAGS) = false := by
        exact (Bool.eq_false_iff).2 hc
      rw [hc']
      refine ⟨0xb8, ?_⟩
      rw [hp]
      (cases alphabet <;> decide +kernel)
  · exact branchEffect_avoids _ _ _ _

open Base16ct.Spec Base16ct.Spec.Program Base16ct.Spec.Program.Extracted
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Base16ct.Proofs.Base16ctUpperDecodeCorrect.Instructions.StoreImage

theorem decode_loop_store [bindings : Bindings] {s : RamState} {boundary : ReturnBoundary}
    (hentry : EntryReady programImage s)
    (_hp : s.RIP = (decodeAddress alphabet) + 208#64)
    (hstore : StorePre ((decodeAddress alphabet) + 208#64) 3
      (fun u => (lowerStoreAM).addrAt u 3) 1 s)
    (hret : ¬ InProgram boundary.rip)
    (havoid : (storeEffect ((decodeAddress alphabet) + 208#64) 3
      (fun u => (lowerStoreAM).addrAt u 3)
      (fun u => (Operand.reg 3 : Operand 8).read u) s).Avoids programImage) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ CodeIn programImage t ∧
      (storeEffect ((decodeAddress alphabet) + 208#64) 3
        (fun u => (lowerStoreAM).addrAt u 3)
        (fun u => (Operand.reg 3 : Operand 8).read u) s).Holds s t := by
  have hs := mov_lower_store_step (p := (decodeAddress alphabet) + 208#64)
  apply advanceInProgram hs hentry.ready hentry.code
  · intro x hx
    obtain ⟨i, rfl⟩ := (mem_codeRange_iff _ _ _).mp hx
    change Fin 3 at i
    clear hx
    finite_cases i
    all_goals (cases alphabet <;> decide +kernel)
  · exact hstore
  · exact hret
  · change InProgram ((storeEffect ((decodeAddress alphabet) + 208#64) 3
      (fun u => (lowerStoreAM).addrAt u 3)
      (fun u => (Operand.reg 3 : Operand 8).read u) s).rip)
    unfold storeEffect
    change InProgram ((decodeAddress alphabet) + 208#64 + 3#64)
    exact ⟨0x48, by (cases alphabet <;> decide +kernel)⟩
  · exact havoid

end Base16ct.Proofs.Base16ctUpperDecodeCorrect.Instructions
