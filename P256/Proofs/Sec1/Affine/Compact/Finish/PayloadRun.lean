import P256.Proofs.Sec1.Affine.Compact.Finish.Payload
import P256.Proofs.Sec1.Affine.State
import P256.Proofs.Program.ScalarFrame.Memory
import P256.Proofs.Program.ScalarFrame.Output
import X86Proofs.Program.ReadWrite.Bytes

set_option autoImplicit false

namespace P256.Proofs.Sec1.Affine.Compact.Finish.Payload

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open ScalarFrame

theorem copy_bytes {s t : RamState} (effect : (copyEffect s).Holds s t)
    (input : MemReadable s (stackPtr s + 96) 64)
    (output : MemReadable t (s.regValue .rbx) 64) :
    ∀ i < 64, t.external[s.regValue .rbx + BitVec.ofNat 64 i]? =
      s.external[stackPtr s + 96 + BitVec.ofNat 64 i]? := by
  have limbs (j : Nat) (hj : j < 8) :
      memLoad t.external (s.regValue .rbx + BitVec.ofNat 64 (8*j)) 64 =
      memLoad s.external (stackPtr s + 96 + BitVec.ofNat 64 (8*j)) 64 := by
    have values := effect.writes
    simp only [copyEffect, Write.AllHold] at values
    have cases : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 5 ∨ j = 6 ∨ j = 7 := by omega
    rcases cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals simp only [Nat.reduceMul, BitVec.ofNat_eq_ofNat, BitVec.add_zero, BitVec.add_assoc, BitVec.reduceAdd]
    · have h : memLoad t.external (s.regValue .rbx + (0 : BitVec 64)) 64 =
          memLoad s.external (stackPtr s + 96) 64 := values.2.2.1
      simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using h
    · exact values.2.2.2.1
    · exact values.2.2.2.2.1
    · exact values.2.2.2.2.2.1
    · exact values.2.2.2.2.2.2.1
    · exact values.2.2.2.2.2.2.2.1
    · exact values.2.2.2.2.2.2.2.2.1
    · exact values.2.2.2.2.2.2.2.2.2
  intro i hi
  have bytes {v : RamState} {address : BitVec 64} (readable : MemReadable v address 64) :
      Bytes v.external (address + BitVec.ofNat 64 (8*(i/8))) 8
        (storedByte (memLoad v.external (address + BitVec.ofNat 64 (8*(i/8))) 64)) := by
    apply Bytes.of_memLoad (n := 64)
    intro k hk
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
    exact readable.mem _ (by omega)
  have ht := bytes output (i%8) (by omega)
  have hs := bytes input (i%8) (by omega)
  rw [limbs _ (by omega)] at ht
  simpa only [BitVec.add_assoc, ← BitVec.ofNat_add, show 8*(i/8)+i%8 = i by omega] using ht.trans hs.symm

def components (s : RamState) : List Component :=
  [.reg 1,.reg 2,.rip,.mem (s.regValue .rbx) 64]

theorem copy_frame {s t : RamState} (effect : (copyEffect s).Holds s t) :
    AgreesExcept (components s) s t := by
  apply effect.agrees.widen
  · intro c hc hm
    simp only [copyEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
    all_goals try simp [components]
    all_goals simp [Component.isMem] at hm
  · intro a c hc ha
    simp only [copyEffect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
    all_goals try exact ha.elim
    all_goals
      obtain ⟨i,hi,rfl⟩ := ha
      refine ⟨.mem (s.regValue .rbx) 64, by simp [components], ?_⟩
    · refine ⟨i,by omega,?_⟩
      change s.regValue .rbx + 0 + BitVec.ofNat 64 i = _
      simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero]
    · exact ⟨8+i,by omega,by rw [BitVec.ofNat_add,BitVec.add_assoc]; rfl⟩
    · exact ⟨16+i,by omega,by rw [BitVec.ofNat_add,BitVec.add_assoc]; rfl⟩
    · exact ⟨24+i,by omega,by rw [BitVec.ofNat_add,BitVec.add_assoc]; rfl⟩
    · exact ⟨32+i,by omega,by rw [BitVec.ofNat_add,BitVec.add_assoc]; rfl⟩
    · exact ⟨40+i,by omega,by rw [BitVec.ofNat_add,BitVec.add_assoc]; rfl⟩
    · exact ⟨48+i,by omega,by rw [BitVec.ofNat_add,BitVec.add_assoc]; rfl⟩
    · exact ⟨56+i,by omega,by rw [BitVec.ofNat_add,BitVec.add_assoc]; rfl⟩

theorem run [Bindings] {s t : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}
    (pre : AffineDecodePre s boundary bytes) (state : Frame s t)
    (rip : t.RIP = 0x1105b7) (output : t.regValue .rbx = s.regValue .rdi) :
    ∃ fuel u, Advances boundary fuel t u ∧ Frame s u ∧ u.RIP = 0x11060a ∧
      AgreesExcept (components t) t u ∧
      ∀ i < 64, u.external[s.regValue .rdi + BitVec.ofNat 64 i]? =
        t.external[stackPtr s - 664 + BitVec.ofNat 64 i]? := by
  have cp : CopyPre t := by
    refine ⟨rip,?_,?_,?_,?_⟩
    · intro i hi
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals exact stack_readable pre.toCalleePre state (by decide) (by decide)
    · intro i hi
      change P256.Proofs.Common.Instructions.CrossPageStore.Writable t (t.regValue .rbx+i) 8
      rw [output]
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals exact (output_writable pre.toCalleePre (by decide) state.allocated).add _ (by decide)
    · intro i hi off len hb
      change RangeApart (t.regValue .rbx+i) 8 _ _
      rw [output]
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals exact P256.Proofs.Common.Instructions.RangeApart.add_left (output_code pre.toCalleePre hb) _ (by decide)
    · intro i hi j hj k hk l hl eq
      change t.regValue .rbx + i + BitVec.ofNat 64 k = stackPtr t + j + BitVec.ofNat 64 l at eq
      rw [output] at eq
      have ho : (registerRegion s .rdi 80).Contains (s.regValue .rdi+i+BitVec.ofNat 64 k).toNat := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals exact output_contains pre.toCalleePre (by decide) ⟨k,hk,rfl⟩
      have hs : (Stack.region s 3360).Contains (stackPtr t+j+BitVec.ofNat 64 l).toNat := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
        rcases hj with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · have addr : stackPtr t + 96 = stackPtr s - 664 :=
            scalar_stack_address state.rsp (offset := 96) (by decide) (by decide)
          rw [addr]
          exact stack_contains pre.toCalleePre (by decide) (by decide) ⟨l,hl,rfl⟩
        · have addr : stackPtr t + 104 = stackPtr s - 656 :=
            scalar_stack_address state.rsp (offset := 104) (by decide) (by decide)
          rw [addr]
          exact stack_contains pre.toCalleePre (by decide) (by decide) ⟨l,hl,rfl⟩
        · have addr : stackPtr t + 112 = stackPtr s - 648 :=
            scalar_stack_address state.rsp (offset := 112) (by decide) (by decide)
          rw [addr]
          exact stack_contains pre.toCalleePre (by decide) (by decide) ⟨l,hl,rfl⟩
        · have addr : stackPtr t + 120 = stackPtr s - 640 :=
            scalar_stack_address state.rsp (offset := 120) (by decide) (by decide)
          rw [addr]
          exact stack_contains pre.toCalleePre (by decide) (by decide) ⟨l,hl,rfl⟩
        · have addr : stackPtr t + 128 = stackPtr s - 632 :=
            scalar_stack_address state.rsp (offset := 128) (by decide) (by decide)
          rw [addr]
          exact stack_contains pre.toCalleePre (by decide) (by decide) ⟨l,hl,rfl⟩
        · have addr : stackPtr t + 136 = stackPtr s - 624 :=
            scalar_stack_address state.rsp (offset := 136) (by decide) (by decide)
          rw [addr]
          exact stack_contains pre.toCalleePre (by decide) (by decide) ⟨l,hl,rfl⟩
        · have addr : stackPtr t + 144 = stackPtr s - 616 :=
            scalar_stack_address state.rsp (offset := 144) (by decide) (by decide)
          rw [addr]
          exact stack_contains pre.toCalleePre (by decide) (by decide) ⟨l,hl,rfl⟩
        · have addr : stackPtr t + 152 = stackPtr s - 608 :=
            scalar_stack_address state.rsp (offset := 152) (by decide) (by decide)
          rw [addr]
          exact stack_contains pre.toCalleePre (by decide) (by decide) ⟨l,hl,rfl⟩

      rw [eq] at ho
      exact (pre.separation (1 : Fin 3) (2 : Fin 3) (by decide)) _ ho hs
  obtain ⟨fuel,u,run,ready,_,effect⟩ := copy boundary pre.outerBoundary t
    (readyToStep state.machine state.bindingsSupported)
    (programText_slice (programLoaded_codeIn state.loaded) 0x105b7 copyBytes (by decide) (by decide +kernel)) cp
  have agrees := copy_frame effect
  have writes : WritesWithin (components t) #v[registerRegion s .rdi 80,workRegion s 3360] := by
    intro c hc a ha
    simp only [components,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl
    all_goals try exact ha.elim
    rw [output] at ha
    exact ⟨_,by simp,output_contains pre.toCalleePre (offset := 0) (len := 64) (by decide) (by simpa using ha)⟩
  have finished := state.after_effect pre.toCalleePre (by decide) ready agrees writes (by simp [components])
  refine ⟨fuel,u,run,finished,effect.rip,agrees,?_⟩
  have copied := copy_bytes effect (stack_readable pre.toCalleePre state (by decide) (by decide))
    (by rw [output]; simpa only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] using ((output_writable pre.toCalleePre (by decide) finished.allocated).add 0 (len := 64) (by decide)).toMemReadable)
  intro i hi
  have addr : stackPtr t + 96 = stackPtr s - 664 :=
    scalar_stack_address state.rsp (offset := 96) (by decide) (by decide)
  simpa only [output,addr] using copied i hi

end P256.Proofs.Sec1.Affine.Compact.Finish.Payload
