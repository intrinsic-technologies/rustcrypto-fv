import Sha2.Proofs.Common.SHA256.Instances.Absorb.Headers

set_option autoImplicit false

namespace Sha2.Proofs.Common.SHA256.Instances.Absorption

open Sha2.Spec.Program X86 X86.Machine X86.UserProcess X86Proofs
open Sha2.Proofs.Common.Machine Sha2.Proofs.Common.SHA256.Absorb

theorem Loop.calls_bounded (loop : Loop) (v : Wrapper.Variant := .sha256) :
    ∀ call ∈ (loop.calls v),
      call.pc = Extracted.textAddress + BitVec.ofNat 64 (call.pc.toNat - 0x100000) ∧
      call.pc.toNat - 0x100000 + call.encoding.bytes.length ≤ 71757 := by
  cases v <;> cases loop <;> decide +kernel

def siteTarget (site : Blocks.Site) : BitVec 64 :=
  match site.block with
  | .branch _ disp | .jump disp => branchTarget site.pc (Blocks.bytes site.block).length disp.value
  | _ => site.pc

theorem Loop.targets_bounded (loop : Loop) (v : Wrapper.Variant := .sha256) :
    ∀ site ∈ (loop.sites v),
      siteTarget site = Extracted.textAddress + BitVec.ofNat 64 ((siteTarget site).toNat - 0x100000) ∧
      (siteTarget site).toNat - 0x100000 < 71757 := by
  cases v <;> cases loop <;> decide +kernel

set_option maxRecDepth 1000000 in
theorem Loop.site_targets (loop : Loop) (v : Wrapper.Variant := .sha256) (site : Blocks.Site) (member : site ∈ (loop.sites v)) :
    match site.block with
    | .branch _ disp | .jump disp =>
      InProgram (branchTarget site.pc (Blocks.bytes site.block).length disp.value)
    | _ => True := by
  obtain ⟨pc, bound⟩ := loop.targets_bounded v site member
  have target : InProgram (siteTarget site) := by
    rw [pc]
    exact inProgram_of_textOffset _ bound
  cases eq : site.block <;> simp [siteTarget, eq] at *
  all_goals exact target

theorem Loop.codeFacts (loop : Loop) (v : Wrapper.Variant := .sha256) : CodeFacts (loop.chunk v) := by
  constructor
  · intro stage s loaded x member
    obtain ⟨site, siteMember, member⟩ := List.mem_flatMap.mp member
    exact loop.sites_loaded s loaded v site (loop.chunk_sites stage v site siteMember) x member
  · intro call member s loaded
    have h : call ∈ (loop.calls v) := by cases v <;> cases loop <;> exact member
    obtain ⟨pc, bound⟩ := loop.calls_bounded v call h
    rw [pc]
    exact programText_slice (programLoaded_codeIn loaded) _ _ bound (loop.calls_fit v call h)
  · intro stage
    let offset := ((loop.chunk v).pc stage).toNat - 0x100000
    have pc : (loop.chunk v).pc stage = Extracted.textAddress + BitVec.ofNat 64 offset := by
      cases v <;> cases loop <;> cases stage <;> decide +kernel
    rw [pc]
    apply inProgram_of_textOffset
    cases v <;> cases loop <;> cases stage <;> decide +kernel
  · constructor
    · let offset := (loop.chunk v).smallExit.toNat - 0x100000
      have pc : (loop.chunk v).smallExit = Extracted.textAddress + BitVec.ofNat 64 offset := by
        cases v <;> cases loop <;> decide +kernel
      rw [pc]
      apply inProgram_of_textOffset
      cases v <;> cases loop <;> decide +kernel
    · let offset := (loop.chunk v).largeExit.toNat - 0x100000
      have pc : (loop.chunk v).largeExit = Extracted.textAddress + BitVec.ofNat 64 offset := by
        cases v <;> cases loop <;> decide +kernel
      rw [pc]
      apply inProgram_of_textOffset
      cases v <;> cases loop <;> decide +kernel

end Sha2.Proofs.Common.SHA256.Instances.Absorption
