import P256.Proofs.Projective.Add.Output.CopyYYPlus
import P256.Proofs.Projective.Add.Output.CopyXY
import P256.Proofs.Projective.Add.Output.CopyYZ
import P256.Proofs.Projective.Add.Output.CopyBXZ3
import P256.Proofs.Projective.Add.Output.CopyYYMinus
import P256.Proofs.Projective.Add.Output.CopyXXMinus
import P256.Proofs.Projective.Add.Output.CopyX
import P256.Proofs.Projective.Add.Output.CopyY
import P256.Proofs.Projective.Add.Output.CopyZ
import P256.Proofs.Projective.Add.Output.Memory
import P256.Proofs.Projective.Add.Copy.Stack

set_option autoImplicit false

open P256.Proofs.Common.Field (AdvanceTriple)

namespace P256.Proofs.Projective.Add.Output

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines
open P256.Proofs.Program P256.Proofs.Program.ScalarFrame P256.Proofs.Field
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [Bindings] {s t u : RamState} {boundary : ReturnBoundary}

theorem copy_output_pre {ip : BitVec 64} {source destination : RamState → BitVec 64}
    {off srcOff : Nat}
    (pre : CalleePre s boundary 0x1051f0 96 96 920) (state : FrameState s t 96 920 632)
    (bound : off + 32 ≤ 96) (srcBound : srcOff + 32 ≤ 632)
    (src : source t = stackPtr t + BitVec.ofNat 64 srcOff)
    (dst : destination t = s.regValue .rdi + BitVec.ofNat 64 off)
    (rip : t.RIP = ip) : Copy32.Pre ip source destination t := by
  have rd : MemReadable t (source t) 32 := src ▸ stack_readable (frameOffset := 632) pre state (by decide) srcBound
  have wr : P256.Proofs.Common.Instructions.CrossPageStore.Writable t (destination t) 32 := dst ▸ (output_writable pre (by decide) state.allocated).add off bound
  refine ⟨rip, ?_, ?_, ?_, ?_⟩
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    all_goals exact P256.Proofs.Common.Memory.memReadable_sub rd _ 8 (by decide)
  · intro i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    all_goals exact wr.add _ (by decide)
  · rw [src, dst, scalar_stack_address (frameOffset := 632) state.rsp (by decide) (by omega)]
    exact stack_apart pre bound (by omega) (by omega)
  · intro i hi pc len hc
    rw [dst]
    have apart := P256.Proofs.Common.Instructions.RangeApart.add_left (h := (output_code pre hc)) off bound
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl
    all_goals exact P256.Proofs.Common.Instructions.RangeApart.add_left (h := apart) _ (by decide)

theorem execute_output {entryOffset off srcOff value : Nat} {endIP : BitVec 64}
    {source destination : RamState → BitVec 64} {bytes : List UInt8}
    (pre : CalleePre s boundary 0x1051f0 96 96 920) (state : FrameState s t 96 920 632)
    (block : AdvanceTriple boundary
      (Copy32.Pre (Extracted.textAddress + BitVec.ofNat 64 entryOffset) source destination)
      (codeRange (Extracted.textAddress + BitVec.ofNat 64 entryOffset) bytes)
      (Effect.post (Copy32.effect endIP source destination)))
    (codeBound : entryOffset + bytes.length ≤ 118431)
    (code : Extracted.textBytes.toListFrom entryOffset bytes.length = bytes)
    (bound : off + 32 ≤ 96) (srcBound : srcOff + 32 ≤ 632)
    (src : source t = stackPtr t + BitVec.ofNat 64 srcOff)
    (dst : destination t = s.regValue .rdi + BitVec.ofNat 64 off)
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 entryOffset)
    (input : MontgomeryAt t (source t) value) :
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u 96 920 632 ∧ u.RIP = endIP ∧
      MontgomeryAt u (destination t) value ∧ AgreesExcept (Copy32.components (destination t)) t u := by
  obtain ⟨fuel, u, run, ready, _, effect⟩ := block t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) entryOffset bytes codeBound code)
    (copy_output_pre pre state bound srcBound src dst rip)
  have agrees := Copy32.frame effect
  have writes : WritesWithin (Copy32.components (destination t))
      #v[registerRegion s .rdi 96, workRegion s 920] := by
    intro c hc a ha
    simp only [Copy32.components, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    rw [dst] at ha
    exact ⟨registerRegion s .rdi 96, by simp, output_contains pre bound ha⟩
  have next := state.after_effect pre (by decide) ready agrees writes (by simp [Copy32.components])
  refine ⟨fuel, u, run, next, effect.rip, input.of_bytes_eq (Copy32.copy_bytes effect (Copy.source_readable (copy_output_pre pre state bound srcBound src dst rip)) ?_), agrees⟩
  rw [dst]
  exact ((output_writable pre (by decide) next.allocated).add off bound).toMemReadable

end P256.Proofs.Projective.Add.Output
