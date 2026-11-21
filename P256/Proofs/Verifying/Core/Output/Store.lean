import P256.Proofs.Verifying.Core.Output.Reject

set_option autoImplicit false

namespace P256.Proofs.Verifying.Core.Output

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions.CrossPageStore

theorem store [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (outside : ¬ InProgram boundary.rip) (rip : s.RIP = 0x10e191)
    (writable : Writable s (s.regValue .rax) 8)
    (apart : ∀ off len : Nat, off + len ≤ 118431 →
      RangeApart (s.regValue .rax) 8 (Extracted.textAddress + BitVec.ofNat 64 off) len) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ t.RIP = 0x10e194 ∧
      memLoad t.external (s.regValue .rax) 64 = s.regValue .rcx ∧
      AgreesExcept [.mem (s.regValue .rax) 8, .reg 0, .rip] s t := by
  have addr (q : RamState) : storeAddrAt 0x10e191 (.base 0 .none) 3 q = q.regValue .rax := by
    change q.regValue .rax + 0 = q.regValue .rax
    exact BitVec.add_zero _
  obtain ⟨a, ha, ra, ea⟩ :=
    (mov_m64_r64_effect_step_any 0x10e191 0x48 (by simp [RexWPrefix]) 1
      (.base 0 .none) (by decide) rfl rfl).advances ready
      (programText_slice (programLoaded_codeIn loaded) 0xe191 _
        (by decide) (by decide +kernel))
      ⟨rip, by change Writable s (storeAddrAt 0x10e191 (.base 0 .none) 3 s) 8
               rw [addr]; exact writable,
        by change RangeApart (storeAddrAt 0x10e191 (.base 0 .none) 3 s) 8 0x10e191 3
           rw [addr]; exact apart 0xe191 3 (by decide)⟩
      (boundary_ne_program outside (inProgram_of_textOffset 0xe194 (by decide)))
  have fa : AgreesExcept [.mem (s.regValue .rax) 8, .rip] s a := by
    simpa only [movM64R64Effect_components, AddrMode.tail, Disp.bytes, List.length_nil,
      Nat.add_zero, addr] using ea.agrees
  have tag : memLoad a.external (s.regValue .rax) 64 = s.regValue .rcx := by
    have h : memLoad a.external (storeAddrAt 0x10e191 (.base 0 .none) 3 s) 64 =
        s.regValue .rcx := ea.writes
    simpa only [addr] using h
  exact ⟨a,ha,ra,ea.rip,tag,fa.mono (by simp)⟩

end P256.Proofs.Verifying.Core.Output
