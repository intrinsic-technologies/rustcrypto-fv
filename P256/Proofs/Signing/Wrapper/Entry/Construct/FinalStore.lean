import P256.Proofs.Program.Code
import P256.Proofs.Common.Field.Operations.Run.Compose
import X86Proofs.Instructions.Lea.Triple
import X86Proofs.Instructions.Mov.Triple
import X86Proofs.Instructions.MovLoad.Triple
import P256.Proofs.Common.Instructions.CrossPageStore
import P256.Proofs.Common.EffectCompose.Memory

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Entry.Construct.FinalStore

open P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program P256.Proofs.Common.Field

structure Pre (s : RamState) : Prop where
  rip : s.RIP = 0x1026f4
  readable : ∀ off : Nat, off+8≤520 → MemReadable s (stackPtr s+BitVec.ofNat 64 off) 8
  writable : ∀ off : Nat, off+8≤472 → Common.Instructions.CrossPageStore.Writable s
    (stackPtr s+BitVec.ofNat 64 off) 8
  codeApart : ∀ off co cl : Nat, off+8≤472 → co+cl≤118431 →
    RangeApart (stackPtr s+BitVec.ofNat 64 off) 8
      (Extracted.textAddress+BitVec.ofNat 64 co) cl

def bytes : List UInt8 :=
  [72, 137, 132, 36, 112, 1, 0, 0]

def effect (s : RamState) : Effect :=
  { rip := 0x1026fc
    writes := [⟨(.mem ((Operand.reg 4 : Operand 64).read s+368) : Operand 64),(Operand.reg 0 : Operand 64).read s⟩] }

theorem run [Bindings] (boundary : ReturnBoundary) (outside : ¬InProgram boundary.rip) :
    AdvanceTriple boundary Pre (codeRange 0x1026f4 bytes) (Effect.post effect) := by
  advance_begin (Common.Instructions.CrossPageStore.mov_m64_r64_effect_step_any 0x1026f4 0x48 (by simp [RexWPrefix]) 0 (.sib 4 none 0 (.d32 368)) (by decide) rfl rfl)
  case pre => intro s h; exact ⟨h.rip,h.writable 368 (by decide),h.codeApart 368 0x26f4 8 (by decide) (by decide)⟩
  case next => intro _ _; exact boundary_ne_program outside (inProgram_of_textOffset 0x26fc (by decide))
  case av =>
    intro s h
    apply Effect.avoids_codeRange
    x86_norm [stackPtr]
    exact h.codeApart 368 0x26f4 8 (by decide) (by decide)
  apply AdvanceTriple.block_end
  intro s t hp hh
  apply hh.weaken
  · x86_norm [effect]
  · x86_norm [effect,BitVec.add_assoc]
    all_goals (repeat constructor <;> rfl)
  · intro i; cases i <;> x86_norm [effect]
  · x86_norm [effect]

end P256.Proofs.Signing.Wrapper.Entry.Construct.FinalStore
