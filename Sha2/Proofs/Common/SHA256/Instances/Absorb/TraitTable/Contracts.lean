import Sha2.Proofs.Common.SHA256.Instances.Absorb.TraitTable.Load
import Sha2.Proofs.Common.SHA256.Instances.Absorb.TraitTable.Advance

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Instances.Absorption

open Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.SHA256.Absorb

theorem cloneShape_tableBlocks [bindings : Bindings] {l : Table.Layout}
    (shape : CloneShape l) (boundary : ReturnBoundary)
    (stride : UnitStringStride bindings) (outside : ¬ InProgram boundary.rip) :
    Table.BlockContracts l boundary :=
  ⟨cloneShape_load shape boundary stride outside,
    cloneShape_advance shape boundary stride outside⟩

theorem traitFirst_tableBlocks [bindings : Bindings] (v : Wrapper.Variant)
    (boundary : ReturnBoundary) (stride : UnitStringStride bindings)
    (outside : ¬ InProgram boundary.rip) : Table.BlockContracts (traitFirst v) boundary :=
  cloneShape_tableBlocks (traitFirst_clone_shape v) boundary stride outside

theorem traitLastTable_tableBlocks [bindings : Bindings] (v : Wrapper.Variant)
    (boundary : ReturnBoundary) (stride : UnitStringStride bindings)
    (outside : ¬ InProgram boundary.rip) : Table.BlockContracts (traitLastTable v) boundary :=
  cloneShape_tableBlocks (traitLast_clone_shape v) boundary stride outside

end Sha2.Proofs.Common.SHA256.Instances.Absorption
