import Md5.Proofs.Buffered.FinalizeReset.Contracts
import Md5.Proofs.Buffered.FinalizeReset.Normalize.Execution

namespace Md5.Proofs.Buffered.FinalizeReset

open Md5.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs Md5.Proofs.Block

theorem Storage.readable {variant : Variant} {s : RamState} (h : Storage s variant) (offset len : Nat)
    (hEnd : offset + len ≤ variant.stackBytes) :
    MemReadable s (stackPtr s + BitVec.ofNat 64 offset) len := by
  have hsize := variant.stackBytes_bounds
  have hHigh := h.stackHigh
  have hLow := h.stackLow
  unfold userAddressLimit at hHigh
  have hOffset : offset < 2^64 := by omega
  have hSum : (stackPtr s).toNat + offset < 2^64 := by omega
  have hAddress : (stackPtr s + BitVec.ofNat 64 offset).toNat =
      (stackPtr s).toNat + offset := by
    rw [BitVec.toNat_add, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hOffset,
      Nat.mod_eq_of_lt hSum]
  apply memReadable_of_allocated h.stackAllocated
  · change _ ≤ 2^32
    rw [hAddress]
    omega
  · change (stackPtr s).toNat - 320 ≤ _
    rw [hAddress]
    omega
  · change _ ≤ (stackPtr s).toNat - 320 + (320 + variant.stackBytes)
    rw [hAddress]
    omega

theorem normalize {variant : Variant} [Bindings] {s : RamState} {boundary : ReturnBoundary}
    {message : ByteArray} (hReady : ReadyToStep s)
    (hCode : CodeIn Extracted.programImage s) (hStorage : Storage s variant)
    (hOutside : ¬ InProgram boundary.rip) (hRip : s.RIP = (variant.address 0x100790))
    (hAbsorbed : Absorbed (context s) message s) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ t.RIP = (variant.address 0x1007a6) ∧
      (Operand.reg 0 : Operand 64).read t = BitVec.ofNat 64 (message.size % 64) ∧
      (Operand.reg 14 : Operand 64).read t = BitVec.ofNat 64 (message.size / 64) <<< 9 ∧
      (Operand.reg 12 : Operand 64).read t =
        (Operand.mem (stackPtr s + 0xc0) : Operand 64).read s ∧
      stackPtr t = stackPtr s ∧
      AgreesExcept [.reg 0, .reg 12, .reg 14, .flags, .rip] s t := by
  have hsize := variant.stackBytes_bounds
  have hBytes : CodeIn (codeRange (variant.address 0x100790) Normalize.bytes) s := by
    cases variant with
    | saved => exact program_text_slice hCode 0x790 22 (by decide +kernel)
    | direct => exact program_text_slice hCode 0xe40 22 (by decide +kernel)
  have hPre : Normalize.ReadPre s variant :=
    ⟨hRip, hStorage.readable 0x58 8 (by omega),
      hStorage.readable 0x47 1 (by omega), hStorage.readable 0xc0 8 (by omega)⟩
  obtain ⟨fuel, t, hAdvance, hReady', _, hEffect⟩ :=
    Normalize.execution boundary hOutside s hReady hBytes hPre
  have hAvoid : (Normalize.effect s variant).Avoids Extracted.programImage :=
    Effect.Avoids.of_noMem (by simp [Normalize.effect, Effect.components,
      Write.component, Operand.component, Component.Covers]) _
  have hPosition : (Operand.mem (stackPtr s + 0x47) : Operand 8).read s =
      BitVec.ofNat 8 (message.size % 64) := by
    simpa only [context, BitVec.add_assoc, show (8 : BitVec 64) + 63 = 71 from rfl]
      using hAbsorbed.position
  have hBlocks : (Operand.mem (stackPtr s + 0x58) : Operand 64).read s =
      BitVec.ofNat 64 (message.size / 64) := by
    simpa only [context, BitVec.add_assoc, show (8 : BitVec 64) + 80 = 88 from rfl]
      using hAbsorbed.blocks
  have hWrites := hEffect.writes
  change (Operand.reg 0 : Operand 64).read t =
      ((Operand.mem (stackPtr s + 0x47) : Operand 8).read s).setWidth 64 ∧
    (Operand.reg 12 : Operand 64).read t =
      (Operand.mem (stackPtr s + 0xc0) : Operand 64).read s ∧
    (Operand.reg 14 : Operand 64).read t =
      (Operand.mem (stackPtr s + 0x58) : Operand 64).read s <<< 9 at hWrites
  refine ⟨fuel, t, hAdvance, hReady', hEffect.codeIn hAvoid hCode, hEffect.rip,
    ?_, ?_, hWrites.2.1, ?_, hEffect.agrees⟩
  · rw [hWrites.1, hPosition]
    exact BitVec.setWidth_ofNat_of_le_of_lt (by decide) (by omega)
  · rw [hWrites.2.2, hBlocks]
  · exact hEffect.agrees.read (n := 64) (r := 4) (by
      simp [Normalize.effect, Effect.components, Write.component, Operand.component])

end Md5.Proofs.Buffered.FinalizeReset
