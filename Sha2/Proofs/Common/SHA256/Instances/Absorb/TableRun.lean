import Sha2.Proofs.Common.SHA256.Instances.Absorb.Compose
import Sha2.Proofs.Common.SHA256.Absorb.Table

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Instances.Absorption

open Sha2.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Program
open Sha2.Proofs.Common.Machine
open Sha2.Proofs.Common.Field
open Sha2.Proofs.Common.SHA256.Absorb

theorem load_sites_run [Bindings] {l : Table.Layout} (boundary : ReturnBoundary)
    (sp : BitVec 64) (sites : List Blocks.Site) (code : CodeMap)
    (stride : UnitStringStride (inferInstance : Bindings))
    (outside : ¬ InProgram boundary.rip)
    (inside : ∀ site ∈ sites, BlockInProgram site.pc (Blocks.bytes site.block).length)
    (targets : ∀ site ∈ sites, match site.block with
      | .branch _ disp | .jump disp =>
        InProgram (branchTarget site.pc (Blocks.bytes site.block).length disp.value)
      | _ => True)
    (included : ∀ site ∈ sites, ∀ x ∈ site.code, x ∈ code)
    (sitePre : ∀ s, Table.LoadPre l sp s → Blocks.SitePre code sites s)
    (post : ∀ s t, Table.LoadPre l sp s → Blocks.SiteTrace sites s t →
      Table.LoadPost l sp s t) :
    AdvanceTriple boundary (Table.LoadPre l sp) code (Table.LoadPost l sp) := by
  intro s ready loaded pre
  obtain ⟨fuel, t, run, readyT, loadedT, trace⟩ := Blocks.run_sites boundary sites code
    stride outside inside targets included s ready loaded (sitePre s pre)
  exact ⟨fuel, t, run, readyT, loadedT, post s t pre trace⟩

theorem next_sites_run [Bindings] {l : Table.Layout} (boundary : ReturnBoundary)
    (sp : BitVec 64) (large : Bool) (sites : List Blocks.Site) (code : CodeMap)
    (stride : UnitStringStride (inferInstance : Bindings))
    (outside : ¬ InProgram boundary.rip)
    (inside : ∀ site ∈ sites, BlockInProgram site.pc (Blocks.bytes site.block).length)
    (targets : ∀ site ∈ sites, match site.block with
      | .branch _ disp | .jump disp =>
        InProgram (branchTarget site.pc (Blocks.bytes site.block).length disp.value)
      | _ => True)
    (included : ∀ site ∈ sites, ∀ x ∈ site.code, x ∈ code)
    (sitePre : ∀ s, Table.NextPre l sp large s → Blocks.SitePre code sites s)
    (post : ∀ s t, Table.NextPre l sp large s → Blocks.SiteTrace sites s t →
      Table.NextPost l sp s t) :
    AdvanceTriple boundary (Table.NextPre l sp large) code
      (Table.NextPost l sp) := by
  intro s ready loaded pre
  obtain ⟨fuel, t, run, readyT, loadedT, trace⟩ := Blocks.run_sites boundary sites code
    stride outside inside targets included s ready loaded (sitePre s pre)
  exact ⟨fuel, t, run, readyT, loadedT, post s t pre trace⟩

end Sha2.Proofs.Common.SHA256.Instances.Absorption
