import Sha3.Proofs.Finalize.Reset.Code
import Sha3.Proofs.Finalize.Reset.Contract
import Sha3.Proofs.X86.Instructions.Branch.IndirectJump

namespace Sha3.Proofs.Finalize.Reset

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

theorem tail_steps {keccak fullState : Bool} [inst : Bindings] (hstride : UnitStringStride inst)
    (boundary : ReturnBoundary) (hboundary : ¬ InProgram boundary.rip)
    (v : Variant) (ptr sp target : BitVec 64) (s : RamState)
    (hready : ReadyToStep s) (hcode : CodeIn Extracted.programImage s)
    (hp : Pre (keccak := keccak) (fullState := fullState) boundary v ptr sp target s) :
    ∃ t, Advances boundary 52 s t ∧ Done ptr sp target s t := by
  obtain ⟨a, hsa, hra, hca, hia, hpa⟩ :=
    prefix_steps boundary (epilogueAddress (keccak := keccak) (fullState := fullState) v true) ptr
        sp (prefix_subset (keccak := keccak) (fullState := fullState) v)
      (prefix_boundary (keccak := keccak) (fullState := fullState) boundary hboundary v) s hready
          hcode hp.toPrefixPre
  obtain ⟨hgot, hvalue⟩ := memset_pointer_data hca
  have hjump := jmp_m64_rip_effect_step (epilogueAddress (keccak := keccak) (fullState := fullState)
      v true + 17) (jumpDisplacement (keccak := keccak) (fullState := fullState) v)
  have hpre : a.RIP = epilogueAddress (keccak := keccak) (fullState := fullState) v true + (17 :
      BitVec 64) ∧
      MemReadable a ((epilogueAddress (keccak := keccak) (fullState := fullState) v true + 17) + 6 +
          (jumpDisplacement (keccak := keccak) (fullState := fullState) v).signExtend 64) 8 ∧
      ((Operand.mem ((epilogueAddress (keccak := keccak) (fullState := fullState) v true + 17) + 6 +
        (jumpDisplacement (keccak := keccak) (fullState := fullState) v).signExtend 64) : Operand
            64).read a).toNat < 2^32 := by
    rw [jump_pointer (keccak := keccak) (fullState := fullState) v]
    exact ⟨hia, hgot, by rw [hvalue]; decide +kernel⟩
  have hne : (Operand.mem ((epilogueAddress (keccak := keccak) (fullState := fullState) v true + 17)
      + 6 +
      (jumpDisplacement (keccak := keccak) (fullState := fullState) v).signExtend 64) : Operand
          64).read a ≠ boundary.rip := by
    rw [jump_pointer (keccak := keccak) (fullState := fullState) v, hvalue]
    intro he
    apply hboundary
    rw [← he]
    exact Permutation.inProgram_text_offset 0x6a20 (by decide +kernel)
  obtain ⟨b, hab, hrb, heb⟩ := hjump.advances hra (hca.mono (jump_subset (keccak := keccak)
      (fullState := fullState) v)) hpre hne
  have hip : b.RIP = 0x106a20 := by
    have hi := heb.rip
    simpa only [jump_pointer (keccak := keccak) (fullState := fullState) v, hvalue] using hi
  have hread (r : BitVec 5) :
      (Operand.reg r : Operand 64).read b = (Operand.reg r : Operand 64).read a :=
    heb.agrees.read (by change Component.reg r ∉ [Component.rip]; simp)
  have hag : AgreesExcept scalarChanges a b := heb.agrees.mono (by
    change ∀ c ∈ [Component.rip], c ∈ scalarChanges
    simp [scalarChanges])
  have hcb := hca.of_external_eq (scalarChanges_external hag)
  have hpb : PrefixDone ptr sp s b := {
    pointer := (hread 7).trans hpa.pointer
    length := (hread 2).trans hpa.length
    value := (hread 6).trans hpa.value
    stack := (hread 4).trans hpa.stack
    rbx := (hread 3).trans hpa.rbx
    r14 := (hread 14).trans hpa.r14
    agrees := (hpa.agrees.trans hag).mono (by
      intro c hc; simpa only [List.mem_append, or_self] using hc) }
  obtain ⟨t, hbt, ht⟩ := finish hstride boundary hboundary hp hrb hcb hpb hip
  exact ⟨t, hsa.trans (hab.trans hbt), ht⟩

end Sha3.Proofs.Finalize.Reset
