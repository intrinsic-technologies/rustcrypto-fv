import Sha2.Proofs.Common.SHA256.Instances.Digest.Prefix
import Sha2.Proofs.Common.SHA256.Instances.Digest.Clone
import Sha2.Proofs.Common.SHA256.Instances.Digest.Finalized

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Instances.Digest

open Sha2.Spec Sha2.Spec.Program Sha2.Proofs.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine

theorem pointers [Bindings] {initial p h u absorbedState c q t z : RamState} {data : ByteArray} {v : Wrapper.Variant}
    (push : (Prologue.effect (Segment.prologue.pc v) .five272 initial).Holds initial p)
    (args : (Blocks.Digest.Header.effect (Segment.header.pc v) p).Holds p h)
    (init : Initialize.Post (Initialization.digest.layout v) (rspOf h + 168) h u)
    (input : Absorb.Direct.Finished (absorb v) initial u absorbedState (regions initial v) ⟨initial.regValue .rdi, data⟩)
    (setup : (Blocks.Digest.CloneSetup.effect (Segment.cloneSetup.pc v) absorbedState).Holds absorbedState c)
    (copy : (repMovsqEffect (Segment.clone.pc v) c).Holds c q)
    (normalize : (Blocks.Digest.Normalize.effect (Segment.normalize.pc v) q).Holds q t)
    (finish : Finalize.Finalized (Finalization.digest.layout v) initial t z (regions initial v) data) :
    z.regValue .rbx = initial.regValue .rdx ∧ z.regValue .rbp = initial.regValue .rbp := by
  have preserved (r : BitVec 5) (member : r = 3 ∨ r = 5) :
      (.reg r : Operand 64).read z = (.reg r : Operand 64).read h := by
    calc
      _ = (.reg r : Operand 64).read t := finish.frame.registers r
        (by rcases member with rfl | rfl <;> cases v <;> decide +kernel)
        (by rcases member with rfl | rfl <;> cases v <;> decide +kernel)
      _ = (.reg r : Operand 64).read q := normalize.agrees.read
        (by rcases member with rfl | rfl <;> simp [Blocks.Digest.Normalize.effect, Effect.components])
      _ = (.reg r : Operand 64).read c := copy.agrees.read
        (by rcases member with rfl | rfl <;> simp)
      _ = (.reg r : Operand 64).read absorbedState := setup.agrees.read
        (by rcases member with rfl | rfl <;> simp [Blocks.Digest.CloneSetup.effect, Effect.components])
      _ = (.reg r : Operand 64).read u := input.registers r
        (by rcases member with rfl | rfl <;> cases v <;> decide +kernel)
        (by rcases member with rfl | rfl <;> cases v <;> decide +kernel)
      _ = (.reg r : Operand 64).read h := init.frame.read (by
        change Component.reg r ∉ [.reg 0, .reg 0, .reg 0, .reg 0,
          .mem ((rspOf h + 168) + 64) 32, .mem ((rspOf h + 168) + 96) 8,
          .mem ((rspOf h + 168) + 63) 1, .rip]
        rcases member with rfl | rfl <;> simp)
  constructor
  · have output : h.regValue .rbx = p.regValue .rdx := args.writes.1
    exact (preserved 3 (.inl rfl)).trans (output.trans
      (push.agrees.read (n := 64) (r := 2) (by
        simp [Prologue.effect, Prologue.registers, Epilogue.Layout.six, Effect.components,
          List.zipIdx_cons, List.zipIdx_nil, Write.component, Operand.component])))
  · exact (preserved 5 (.inr rfl)).trans
      ((args.agrees.read (n := 64) (r := 5) (by
        simp [Blocks.Digest.Header.effect, Effect.components])).trans
        (push.agrees.read (n := 64) (r := 5) (by
          simp [Prologue.effect, Prologue.registers, Epilogue.Layout.six, Effect.components,
            List.zipIdx_cons, List.zipIdx_nil, Write.component, Operand.component])))

end Sha2.Proofs.Common.SHA256.Instances.Digest
