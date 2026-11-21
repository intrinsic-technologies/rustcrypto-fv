import Sha2.Proofs.Wrapper.Hash.Finalize.Pad.Load
import Sha2.Proofs.Wrapper.Hash.Padding.FillSetup

set_option autoImplicit false

namespace Sha2.Proofs.Wrapper.Hash.Finalize.Pad

open Sha2.Spec Sha2.Proofs.Program Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.SHA256

structure FillReady [Bindings] (initial s : RamState) (message : ByteArray) (v : Variant := .sha256)
    : Prop
    extends Working initial s message (compressBlocks v.initialHash message) v where
  rip : s.RIP = (v.pc 0x1f6)
  tailBytes : (⟨(stackPtr initial - 344).toNat, message.size % 64⟩ : MemoryRegion).HasBytes
    s.external (remainderBytes message)
  marker : s.external[stackPtr initial - 344 + BitVec.ofNat 64 (message.size % 64)]? = some 128
  paddingLength : s.regValue .rbx = BitVec.ofNat 64 (63 - message.size % 64)
  destination : s.regValue .rdi = stackPtr initial - BitVec.ofNat 64 (280 + (63 - message.size % 64))
  zero : s.regValue .rsi = 0
  count : s.regValue .rdx = BitVec.ofNat 64 (63 - message.size % 64)

theorem setup [Bindings] {v : Variant} {initial s : RamState} {inputs : Array Input} {message : ByteArray}
    (ctx : Context initial inputs v)
    (input : Loaded initial s message v) :
    ∃ t, FillReady initial t message v := by
  have tailBound : message.size % 64 < 64 := Nat.mod_lt _ (by decide)
  have address : rspOf s + (Operand.reg 15 : Operand 64).read s =
      stackPtr initial - BitVec.ofNat 64 (344 - message.size % 64) := by
    change rspOf s + s.regValue .r15 = _
    rw [input.tailLength]
    exact Wrapper.stack_add input.rsp (by omega)
  have address' : rspOf s + (Operand.reg 15 : Operand 64).read s =
      stackPtr initial - 344 + BitVec.ofNat 64 (message.size % 64) := by
    change stackPtr s + s.regValue .r15 = _
    rw [input.rsp, input.tailLength]
  have pre : Padding.FillSetup.Pre s v :=
    ⟨input.rip, address ▸ stack_writable1 ctx input.toState (by omega),
      address ▸ stack_codeApart ctx (by omega) (by omega) (by cases v <;> decide : (v.textOffset + 0x1e5) + 17 ≤ 71757)⟩
  obtain ⟨_, t, run, ready, _, effect⟩ := Padding.FillSetup.run (v := v) (returnBoundary initial)
    (validCall_returnBoundary ctx.machine ctx.call).2.2 s
    (supportedMachine_readyToStep input.machine) (Padding.FillSetup.code (v := v) input.loaded) pre
  have frame := effect.agrees
  have localWrite : Wrapper.LocalWrites initial (Padding.FillSetup.effect s v).components := by
    intro c hc a ha
    simp only [Padding.FillSetup.effect, Effect.components, List.map_cons, List.map_nil,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false, Write.component, Operand.component] at hc
    rcases hc with ((rfl | rfl | rfl | rfl) | rfl) | rfl <;> try exact ha.elim
    rw [address] at ha
    exact Wrapper.local_memory (by omega) (by omega) (by omega) a ha
  have preserved := Wrapper.preserved_of_agrees ctx input.toPreserved run ready frame localWrite
    (by simp [Padding.FillSetup.effect, Effect.components])
    (by simp [Padding.FillSetup.effect, Effect.components])
  have bytes (i : Nat) (hi : i < 104) (ne : i ≠ message.size % 64) :
      t.external[stackPtr initial - 344 + BitVec.ofNat 64 i]? =
        s.external[stackPtr initial - 344 + BitVec.ofNat 64 i]? := by
    apply frame.byte
    intro c hc ha
    simp only [Padding.FillSetup.effect, Effect.components, List.map_cons, List.map_nil,
      List.mem_append, List.mem_cons, List.not_mem_nil, or_false, Write.component, Operand.component] at hc
    rcases hc with ((rfl | rfl | rfl | rfl) | rfl) | rfl <;> try exact ha.elim
    obtain ⟨j, hj, eq⟩ := ha
    have hj0 : j = 0 := by omega
    subst j
    rw [address', BitVec.ofNat_eq_ofNat, BitVec.add_zero] at eq
    have same := (BitVec.add_right_inj _).mp eq
    have natSame := congrArg BitVec.toNat same
    simp only [BitVec.toNat_ofNat] at natSame
    apply ne
    omega
  have writes := effect.writes
  change memLoad t.external (rspOf s + (Operand.reg 15 : Operand 64).read s) 8 = 128 ∧
    t.regValue .rdi = rspOf s + (Operand.reg 15 : Operand 64).read s + 1 ∧
    t.regValue .rsi = 0 ∧ t.regValue .rdx = s.regValue .rbx at writes
  refine ⟨t, ⟨⟨preserved, ?_, ?_⟩, ?_, ?_⟩, effect.rip, ?_, ?_, ?_, ?_, writes.2.2.1,
    writes.2.2.2.trans input.paddingLength⟩
  · apply Wrapper.hashState_of_bytes input.hashWords
    intro i hi
    have byte := bytes (64+i) (by omega) (by omega)
    simp only [BitVec.ofNat_add, ← BitVec.add_assoc] at byte
    simpa only [BitVec.sub_eq_add_neg, BitVec.add_assoc, BitVec.reduceNeg,
      BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using byte
  · exact (frame.read (n := 64) (r := 14)
      (by simp [Padding.FillSetup.effect, Effect.components])).trans input.hashPointer
  · exact (frame.read (n := 64) (r := 12)
      (by simp [Padding.FillSetup.effect, Effect.components])).trans input.blocks
  · exact (frame.read (n := 64) (r := 15)
      (by simp [Padding.FillSetup.effect, Effect.components])).trans input.tailLength
  · refine ⟨input.tailBytes.1, ?_⟩
    intro i
    have hi : i.val < message.size % 64 := by simpa only [remainderBytes_size] using i.isLt
    change t.external[BitVec.ofNat 64 ((stackPtr initial - 344).toNat + i.val)]? = _
    rw [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq, bytes i.val (by omega) (by omega)]
    simpa only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] using input.tailBytes.2 i
  · have value := writes.1
    rw [address', memLoad_8] at value
    change ((t.external[stackPtr initial - 344 + BitVec.ofNat 64 (message.size % 64)]?).getD 0).toBitVec = 128 at value
    cases byte : t.external[stackPtr initial - 344 + BitVec.ofNat 64 (message.size % 64)]? with
    | none =>
      rw [byte] at value
      contradiction
    | some v =>
      simp only [byte, Option.getD_some] at value
      have eq : v = 128 := UInt8.eq_of_toBitVec_eq value
      exact congrArg some eq
  · exact (frame.read (n := 64) (r := 3)
      (by simp [Padding.FillSetup.effect, Effect.components])).trans input.paddingLength
  · rw [writes.2.1, address]
    have add : 344 - message.size % 64 = (280 + (63 - message.size % 64)) + 1 := by omega
    rw [add, BitVec.ofNat_add]
    simp only [← BitVec.sub_sub, BitVec.sub_add_cancel, BitVec.ofNat_eq_ofNat]

end Sha2.Proofs.Wrapper.Hash.Finalize.Pad
