import Sha2.Proofs.Common.SHA256.Instances.Absorb.TableLoad
import Sha2.Proofs.Common.SHA256.Instances.Absorb.TableAdvance

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Instances.Absorption

open Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Field Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.SHA256.Absorb

theorem noClone_tableBlocks [bindings : Bindings] {l : Table.Layout}
    (shape : NoCloneShape l) (boundary : ReturnBoundary)
    (stride : UnitStringStride bindings) (outside : ¬ InProgram boundary.rip) :
    Table.BlockContracts l boundary :=
  ⟨noClone_load shape boundary stride outside, noClone_advance shape boundary stride outside⟩

theorem resetDiscarded_tableBlocks [bindings : Bindings] (v : Wrapper.Variant)
    (boundary : ReturnBoundary) (stride : UnitStringStride bindings)
    (outside : ¬ InProgram boundary.rip) : Table.BlockContracts (Sha2.Proofs.Reset.resetDiscarded v) boundary :=
  noClone_tableBlocks (resetDiscarded_noClone v) boundary stride outside

theorem resetFirst_tableBlocks [bindings : Bindings] (v : Wrapper.Variant)
    (boundary : ReturnBoundary) (stride : UnitStringStride bindings)
    (outside : ¬ InProgram boundary.rip) : Table.BlockContracts (Sha2.Proofs.Reset.resetFirst v) boundary :=
  noClone_tableBlocks (resetFirst_noClone v) boundary stride outside

theorem resetSecond_tableBlocks [bindings : Bindings] (v : Wrapper.Variant)
    (boundary : ReturnBoundary) (stride : UnitStringStride bindings)
    (outside : ¬ InProgram boundary.rip) : Table.BlockContracts (Sha2.Proofs.Reset.resetSecond v) boundary :=
  noClone_tableBlocks (resetSecond_noClone v) boundary stride outside

theorem finalizeFirstTable_tableBlocks [bindings : Bindings] (v : Wrapper.Variant)
    (boundary : ReturnBoundary) (stride : UnitStringStride bindings)
    (outside : ¬ InProgram boundary.rip) : Table.BlockContracts (finalizeFirstTable v) boundary :=
  noClone_tableBlocks (finalizeFirst_noClone v) boundary stride outside

theorem finalizeLastTable_tableBlocks [bindings : Bindings] (v : Wrapper.Variant)
    (boundary : ReturnBoundary) (stride : UnitStringStride bindings)
    (outside : ¬ InProgram boundary.rip) : Table.BlockContracts (finalizeLastTable v) boundary :=
  noClone_tableBlocks (finalizeLast_noClone v) boundary stride outside

end Sha2.Proofs.Common.SHA256.Instances.Absorption
