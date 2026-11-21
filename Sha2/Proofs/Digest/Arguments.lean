import Sha2.Proofs.Digest.Header
import Sha2.Proofs.Digest.Entry
import Sha2.Proofs.Common.Machine.ExecutionState

set_option autoImplicit false

namespace Sha2.Proofs.Digest

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine
  X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.SHA256.Blocks.Digest

theorem header512 [bindings : Bindings] (routine : Routine)
    (member : routine ∈ [sha384Digest, sha512Digest, sha512_224Digest, sha512_256Digest])
    {initial s : RamState} {data : ByteArray}
    (machine : SupportedMachine bindings initial)
    (call : OneShot.ValidCall routine initial data)
    (state : ExecutionState initial s
      #v[OneShot.outputRegion routine initial, Stack.region initial 1152])
    (rip : s.RIP = routine.entryAddress + (17 : BitVec 64)) :
    ∃ t, ExecutionState initial t
      #v[OneShot.outputRegion routine initial, Stack.region initial 1152] ∧
      (Header.effect (routine.entryAddress + (17 : BitVec 64)) s).Holds s t := by
  have budget : routine.minStackBytes = 1152 := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> rfl
  obtain ⟨fuel, t, run, ready, _, result⟩ := Header.run (routine.entryAddress + (17 : BitVec 64))
    (returnBoundary initial) (valid_return_boundary machine call.stack call.returnAddress).2.2
    (header512_inside routine member) s (supportedMachine_readyToStep state.machine)
    (header512_code routine member state.loaded) rip
  refine ⟨t, state.of_agrees ?_ run ready result.agrees ?_ ?_, result⟩
  · intro region member a ha h
    have mem : region ∈ [OneShot.outputRegion routine initial,
        Stack.region initial routine.minStackBytes] := by
      simpa only [budget, List.mem_cons, List.mem_singleton, Vector.mem_mk,
        List.mem_toArray] using member
    exact (call.separation.2 region mem).2 a ha (.inl h)
  · intro c hc a ha
    have member : c ∈ [.reg 3, .reg 14, .reg 6, .rip] := hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl <;> exact ha.elim
  · simp [Header.effect, Effect.components, Write.component, Operand.component]

theorem entered512 [bindings : Bindings] (routine : Routine)
    (member : routine ∈ [sha384Digest, sha512Digest, sha512_224Digest, sha512_256Digest])
    {initial : RamState} {data : ByteArray}
    (machine : SupportedMachine bindings initial)
    (call : OneShot.ValidCall routine initial data) :
    ∃ p s, ExecutionState initial s
      #v[OneShot.outputRegion routine initial, Stack.region initial 1152] ∧
      (Prologue.effect routine.entryAddress .six552 initial).Holds initial p ∧
      (Header.effect (routine.entryAddress + 17) p).Holds p s ∧
      s.regValue .rbx = initial.regValue .rdx ∧
      s.regValue .r14 = BitVec.ofNat 64 data.size ∧
      s.regValue .rsi = initial.regValue .rdi ∧
      stackPtr s = stackPtr initial - 600 ∧
      s.RIP = routine.entryAddress + (26 : BitVec 64) := by
  obtain ⟨p, stateP, push, rspP, ripP⟩ := prologue512 routine member machine call
  obtain ⟨s, stateS, args⟩ := header512 routine member machine call stateP ripP
  have regs : s.regValue .rbx = p.regValue .rdx ∧
      s.regValue .r14 = p.regValue .rsi ∧
      s.regValue .rsi = p.regValue .rdi := args.writes
  have kept (r : BitVec 5) (ne : r ≠ 4#5) :
      (Operand.reg r : Operand 64).read p = (Operand.reg r : Operand 64).read initial := by
    apply push.agrees.read
    simp [Prologue.effect, Prologue.registers, Epilogue.Layout.six, Effect.components,
      Write.component, Operand.component]
    exact ne
  refine ⟨p, s, stateS, push, args, regs.1.trans (kept 2 (by decide)), ?_,
    regs.2.2.trans (kept 7 (by decide)), ?_, ?_⟩
  · refine regs.2.1.trans ((kept 6 (by decide)).trans ?_)
    change initial.regValue .rsi = BitVec.ofNat 64 data.size
    rw [← call.lengthArgumentMatchesData]
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · exact (args.agrees.read (n := 64) (r := 4) (by
      simp [Header.effect, Effect.components])).trans rspP
  · simpa [Header.effect, BitVec.add_assoc] using args.rip

end Sha2.Proofs.Digest
