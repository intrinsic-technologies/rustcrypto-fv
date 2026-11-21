import P256.Proofs.Sec1Serialize.Tail.Prepare.EncodedPost
import P256.Proofs.Sec1Serialize.Tail.Prepare.Machine

set_option autoImplicit false

namespace P256.Proofs.Sec1Serialize

open P256.Spec P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame

theorem prepare_encoding [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {x y : Nat} {infinity : Bool}
    (pre : CalleePre s boundary 0x110d70 72 65 328)
    (state : FrameState s t 65 328 312) (rip : t.RIP = 0x110fdc)
    (converted : Converted t x y) (_hx : x < Operations.domain.p) (_hy : y < Operations.domain.p)
    (rdi : t.regValue .rdi = s.regValue .rdi) (compress : compressionFlag s t)
    (savedInput : (Operand.mem (stackPtr s - 192) : Operand 64).read t = s.regValue .rsi)
    (inputFlag : t.external[s.regValue .rsi + 64]? = some (if infinity then 1 else 0))
    (execution : ∃ n, Advances boundary n s t) :
    ∃ u, EncodedEntry s u boundary (Points.encode (.affine x y)) infinity := by
  obtain ⟨u, stateu, ⟨fuel, run⟩, effect⟩ := Prepare.prepare_encoding_run pre state rip compress
  obtain ⟨n, executed⟩ := execution
  exact ⟨u, Prepare.encoded_post pre state stateu ⟨n + fuel, executed.trans run⟩
    effect converted rdi savedInput inputFlag⟩

end P256.Proofs.Sec1Serialize
