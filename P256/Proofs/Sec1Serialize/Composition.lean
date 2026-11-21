import P256.Proofs.Sec1Serialize.Entry
import P256.Proofs.Sec1Serialize.Memory

set_option autoImplicit false

namespace P256.Proofs.Sec1Serialize

open P256.Spec P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

def ConversionCorrect (bindings : Bindings) : Prop :=
  ∀ (s t : RamState) (boundary : ReturnBoundary) (x y : Nat),
    CalleePre s boundary 0x110d70 72 65 328 → FrameState s t 65 328 312 →
    t.RIP = 0x110d88 →
    Field.MontgomeryAt t (s.regValue .rsi) x →
    Field.MontgomeryAt t (s.regValue .rsi + 32) y →
    t.regValue .rsi = s.regValue .rsi → t.regValue .r14 = s.regValue .rsi →
    t.regValue .rdi = s.regValue .rdi → compressionFlag s t →
    ∃ fuel u, Advances boundary fuel t u ∧ FrameState s u 65 328 312 ∧
      u.RIP = 0x110fdc ∧ Converted u x y ∧ u.regValue .rdi = s.regValue .rdi ∧
      compressionFlag s u ∧
      (Operand.mem (stackPtr s - 192) : Operand 64).read u = s.regValue .rsi

def TailCorrect (bindings : Bindings) : Prop :=
  ∀ (s t : RamState) (boundary : ReturnBoundary) (x y : Nat) (infinity : Bool),
    CalleePre s boundary 0x110d70 72 65 328 → FrameState s t 65 328 312 →
    t.RIP = 0x110fdc → Converted t x y →
    x < Operations.domain.p → y < Operations.domain.p →
    t.regValue .rdi = s.regValue .rdi → compressionFlag s t →
    (Operand.mem (stackPtr s - 192) : Operand 64).read t = s.regValue .rsi →
    t.external[s.regValue .rsi + 64]? = some (if infinity then 1 else 0) →
    (∃ n, Advances boundary n s t) →
    ∃ u, CalleeResult s u boundary 65 328 ∧ u.regValue .rax = s.regValue .rdi ∧
      (registerRegion s .rdi 65).HasBytes u.external
        (if infinity then ⟨Array.replicate 65 0⟩ else Points.encode (.affine x y))

theorem contract_of_stages [bindings : Bindings]
    (conversion : ConversionCorrect bindings) (tail : TailCorrect bindings) :
    Contract bindings := by
  intro s boundary point pre input rdx
  obtain ⟨t, run, state, rip, rsi, r14, rdi, compress⟩ := entry_correct pre rdx
  have inputT := affine_at_of_frame pre state input
  have finish (x y : Nat) (infinity : Bool)
      (inputX : Field.MontgomeryAt t (s.regValue .rsi) x)
      (inputY : Field.MontgomeryAt t (s.regValue .rsi + 32) y)
      (flag : s.external[s.regValue .rsi + 64]? = some (if infinity then 1 else 0)) :
      ∃ u, CalleeResult s u boundary 65 328 ∧ u.regValue .rax = s.regValue .rdi ∧
        (registerRegion s .rdi 65).HasBytes u.external
          (if infinity then ⟨Array.replicate 65 0⟩ else Points.encode (.affine x y)) := by
    obtain ⟨fuel, v, convertedRun, stateV, ripV, converted, rdiV, compressV, saved⟩ :=
      conversion s t boundary x y pre state rip inputX inputY rsi r14 rdi compress
    exact tail s v boundary x y infinity pre stateV ripV converted inputX.1 inputY.1
      rdiV compressV saved ((input_byte pre stateV (i := 64) (by decide)).trans flag)
      ⟨9+fuel, run.trans convertedRun⟩
  cases point with
  | infinity =>
    exact finish 0 0 true inputT.1 inputT.2.1 input.2.2
  | affine x y =>
    exact finish x y false inputT.1 inputT.2.1 input.2.2

end P256.Proofs.Sec1Serialize
