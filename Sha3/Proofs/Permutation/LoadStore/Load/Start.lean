import Sha3.Proofs.Permutation.LoadStore.Load.Basic
import Sha3.Proofs.Permutation.LoadStore.Load.Instructions
import Sha3.Proofs.Permutation.LoadStore.FrameBridge

namespace Sha3.Proofs.Permutation.Load

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

variable {copy : Copy}

theorem allocation_progress {initial s t : RamState} (hs : PushProgress copy initial 6 s)
    (he : (subR64Imm32Effect (entryAddress copy + 0xa) 4 216 s).Holds s t) :
    Progress initial (Values.initial initial) (entryAddress copy + 0x11) t := by
  have hm : t.external = s.external := he.agrees.external (by
    simp only [subR64Imm32Effect_components, List.mem_cons, List.not_mem_nil, or_false]
    rintro c (rfl | rfl | rfl) x <;> exact not_false)
  have hread (address : BitVec 64) :
      (Operand.mem address : Operand 64).read t = (Operand.mem address : Operand 64).read s := by
    change memLoad t.external address 64 = memLoad s.external address 64
    rw [hm]
  refine ⟨he.rip.trans (by cases copy <;> rfl),
    ?_, ?_, ?_, ?_, (hread _).trans hs.returnSlot, ?_,
    fun address hx ↦ he.agrees.grow address (hs.grow address hx),
    (he.agrees.scalarFrame_eq (by simp [Effect.components, x86_compose])).trans hs.rest⟩
  · have hw : stackPtr t = stackPtr s - 216 := he.writes
    rw [hw, hs.stack]
    change initial.regValue .rsp - 48 - 216 = initial.regValue .rsp - 264
    rw [BitVec.sub_sub]
    rfl
  · intro r hr
    apply Eq.trans (he.agrees.read ?_) (hs.registers r hr)
    simp only [subR64Imm32Effect_components, List.mem_cons, List.not_mem_nil,
      Component.reg.injEq, reduceCtorEq, or_false]
    exact hr
  · intro i value hslot
    cases hslot
  · intro i
    exact (hread _).trans (hs.savedRegisters i)
  · intro address hout
    change t.external[address]? = initial.external[address]?
    rw [hm]
    exact hs.memory address hout

theorem allocation_advance (copy : Copy) [Bindings] (initial : RamState) (boundary : ReturnBoundary)
    (hboundary : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary 1 (PushProgress copy initial 6) Extracted.programImage
      (fun _ t ↦ Progress initial (Values.initial initial) (entryAddress copy + 0x11) t) := by
  intro s hready hcode hs
  have hsub : ∀ x ∈ codeRange (entryAddress copy + 0xa) (encodeSubR64Imm32 4 216),
      x ∈ Extracted.programImage := fun x hx ↦
    loadCode_subset_programImage copy x (loadInstruction_code_subset copy
      ((entryAddress copy + 0xa), encodeSubR64Imm32 4 216) (by cases copy <;> decide +kernel) x hx)
  have hn : (subR64Imm32Effect (entryAddress copy + 0xa) 4 216 s).rip ≠
      boundary.rip := by
    intro heq
    have hin := loadInstruction_next_inProgram copy (pc := (entryAddress copy + 0xa))
      (bytes := encodeSubR64Imm32 4 216) (by cases copy <;> decide +kernel)
    exact hboundary (heq ▸ hin)
  obtain ⟨t, hrun, hr, he⟩ := (step_00a copy).advances hready (hcode.mono hsub) hs.rip hn
  exact ⟨t, hrun, hr,
    he.codeIn (subR64Imm32Effect_avoids (entryAddress copy + 0xa) 4 216 s _) hcode,
    allocation_progress hs he⟩

theorem entry_advance (copy : Copy) [Bindings] (boundary : ReturnBoundary)
    (hboundary : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary 7 (EntryStackPre copy) Extracted.programImage
      (fun initial t ↦ Progress initial (Values.initial initial) (entryAddress copy + 0x11) t) := by
  intro initial hready hcode hp
  obtain ⟨s, hpush, hs, hcode', hprogress⟩ :=
    pushes_advance_program copy boundary hboundary initial hready hcode hp
  obtain ⟨t, halloc, ht, hcode'', hprogress'⟩ :=
    allocation_advance copy initial boundary hboundary s hs hcode' hprogress
  exact ⟨t, hpush.trans halloc, ht, hcode'', hprogress'⟩

end Sha3.Proofs.Permutation.Load
