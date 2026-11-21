import ChaCha20Poly1305.Proofs.Decrypt.Invoke
import ChaCha20Poly1305.Proofs.Decrypt.PolyContext
import ChaCha20Poly1305.Proofs.Decrypt.PolyMulAll
import ChaCha20Poly1305.Proofs.Decrypt.PolyFinishAll
import ChaCha20Poly1305.Proofs.Decrypt.Fill

namespace ChaCha20Poly1305.Proofs.Decrypt
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program
open Poly1305

@[refine_layout] def leafSpec {L : Type} {p : Program (fun _ => _root_.Empty) L (fun _ => 0) 0}
    (e : L) (abi : Lifted.Label → Activation → List Atom) (c : LayoutCore p Empty.semantics lifted Unit)
    (param : c.Params e) (out : c.Result) : Callee :=
  ⟨c.start e,abi (c.start e),fun fr => c.atoms e () fr param,fun fr => c.done () fr out,fun fr => c.footprint () fr⟩

@[refine_layout] def mulFn (x : Mul.Input) := leafSpec .s0 Fn101e30.active (Mul.core x) () ()

theorem mulFnCorrect (x : Mul.Input) : (mulFn x).Correct :=
  provedCallee (p := Mul.program) Mul.Label.s0 Fn101e30.active (Mul.core x) () rfl () rfl (fun _ => rfl) (Mul.blocks x) Mul.executes

@[refine_layout] def finishFn (x : Finish.Input) := leafSpec .s0 Fn101ce0.active (Finish.core x) () ()

theorem finishFnCorrect (x : Finish.Input) : (finishFn x).Correct :=
  provedCallee (p := Finish.program) Finish.Label.s0 Fn101ce0.active (Finish.core x) () rfl () rfl (fun _ => rfl) (Finish.blocks x) Finish.executes

@[refine_layout] def initFn (x : BitVec 256) := leafSpec () Fn101e40.active (Init.core x) () ()

theorem initFnCorrect (x : BitVec 256) : (initFn x).Correct :=
  provedCallee () Fn101e40.active (Init.core x) () rfl () rfl (fun _ => rfl) (Init.blocks x) (.done rfl)

@[refine_layout] def copyFn  := leafSpec () Fn102dc0.active (Copy.core) () ()

theorem copyFnCorrect  : (copyFn).Correct :=
  provedCallee () Fn102dc0.active (Copy.core) () rfl () rfl (fun _ => rfl) (Copy.blocks) (.done rfl)

@[refine_layout] def fillFn  := leafSpec () Fn102d70.active (Fill.core) () ()

theorem fillFnCorrect  : (fillFn).Correct :=
  provedCallee () Fn102d70.active (Fill.core) () rfl () rfl (fun _ => rfl) (Fill.blocks) (.done rfl)

end ChaCha20Poly1305.Proofs.Decrypt
