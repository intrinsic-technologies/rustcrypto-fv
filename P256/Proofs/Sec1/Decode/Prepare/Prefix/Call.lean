import P256.Proofs.Sec1.Decode.Prepare.Memory
import P256.Proofs.Program.CalleeStackInput
import P256.Proofs.Program.Copy.Pointer
import X86Proofs.Program.ReadWrite.Bytes

set_option autoImplicit false

namespace P256.Proofs.Sec1.Decode.Prepare

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [Bindings] {s t v u : RamState} {boundary : ReturnBoundary} {bytes : ByteArray}

def memoryCall (copy : Bool) : BitVec 64 := if copy then 0x10e55b else 0x10e54c
def memoryReturn (copy : Bool) : BitVec 64 := if copy then 0x10e561 else 0x10e552
def memoryTarget (copy : Bool) : BitVec 64 := if copy then 0x11c930 else 0x11c810

theorem push_address (state : Frame s t) : pushAddr t = stackPtr s - 320#64 := by
  simp only [pushAddr, state.rsp, BitVec.sub_sub]
  rfl

theorem push_writes (pre : DecodePre s boundary bytes) (state : Frame s t)
    {target : RamState → BitVec 64} {ret : BitVec 64} :
    WritesWithin (callEffect target ret t).components
      #v[registerRegion s .rdi 80, ScalarFrame.Work.region s 3680 32] := by
  intro c hc a ha
  simp only [pushEffect_components, List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl | rfl
  · exact ha.elim
  · rw [push_address state] at ha
    exact ⟨ScalarFrame.Work.region s 3680 32, by simp, ScalarFrame.Work.contains pre.toCalleePre (by decide) (by decide) ha⟩
  · exact ha.elim

theorem push_loaded (pre : DecodePre s boundary bytes) (state : Frame s t)
    {target : RamState → BitVec 64} {ret : BitVec 64}
    (effect : (callEffect target ret t).Holds t v) : ProgramLoaded v :=
  ScalarFrame.loaded_of_frame pre.toCalleePre (memoryWriteFrame_trans state.frame
    (ScalarFrame.Work.frame pre.toCalleePre (effect.agrees.memoryWriteFrame (push_writes pre state))))

theorem memory_call (copy : Bool) (pre : DecodePre s boundary bytes) (state : Frame s t)
    (rip : t.RIP = memoryCall copy) :
    ∃ v, Advances boundary 1 t v ∧ ReadyToStep v ∧
      (callEffect (fun _ ↦ memoryTarget copy) (memoryReturn copy) t).Holds t v := by
  let disp : BitVec 32 := if copy then 0xf5f97 else 0xf5ffe
  have pointer : MemReadable t (if copy then 0x2044f8 else 0x204550) 8 ∧
      (Operand.mem (if copy then 0x2044f8 else 0x204550) : Operand 64).read t = memoryTarget copy := by
    cases copy
    · have hbytes : ∀ i : Fin 8,
          Extracted.programSections.fetchByte (0x204550 + BitVec.ofNat 64 i.val) =
            some (storedByte (0x11c810 : BitVec 64) i.val) := by decide +kernel
      have hb : Bytes t.external 0x204550 8 (storedByte (0x11c810 : BitVec 64)) :=
        fun i hi ↦ state.loaded _ _ (hbytes ⟨i,hi⟩)
      exact ⟨hb.readable (by decide), hb.memLoad (by decide) (by decide)⟩
    · exact memcpy_pointer state.loaded
  have target : callMemPtr (memoryCall copy) (.rip disp) t = memoryTarget copy := by
    cases copy <;> exact pointer.2
  have writable : MemWritable t (pushAddr t) 8 := by
    rw [push_address state]
    exact writable_of_grow (stack_sub_writable8 pre.stack
      (fun a ha ht ↦ pre.avoids _ (by simp) a ha (.inr ht)) (offset := 320)
      (by decide) (by decide)) state.allocated
  have apart : RangeApart (pushAddr t) 8 (memoryCall copy) 6 := by
    rw [push_address state]
    intro i hi j hj he
    apply pre.avoids (Stack.region s 3680) (by simp) _
      (ScalarFrame.stack_contains pre.toCalleePre (offset := 320) (by decide) (by decide) ⟨i,hi,rfl⟩)
    apply Or.inl
    change InProgram (stackPtr s - 320#64 + BitVec.ofNat 64 i)
    rw [he]
    cases copy
    · have h := inProgram_of_textOffset (0xe54c+j) (by omega)
      simpa only [BitVec.ofNat_add, ← BitVec.add_assoc, memoryCall,
        Bool.false_eq_true, ite_false, ite_true, Extracted.textAddress, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using h
    · have h := inProgram_of_textOffset (0xe55b+j) (by omega)
      simpa only [BitVec.ofNat_add, ← BitVec.add_assoc, memoryCall,
        Bool.false_eq_true, ite_false, ite_true, Extracted.textAddress, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using h
  have code : CodeIn (codeRange (memoryCall copy) (encodeCallM64 (.rip disp))) t := by
    cases copy
    · exact programText_slice (programLoaded_codeIn state.loaded) 0xe54c _
        (by decide) (by decide +kernel)
    · exact programText_slice (programLoaded_codeIn state.loaded) 0xe55b _
        (by decide) (by decide +kernel)
  obtain ⟨v, step, ready, effect⟩ := call_m64_effect_step (memoryCall copy) (.rip disp)
    trivial rfl rfl t (readyToStep state.machine state.bindingsSupported) code
    ⟨⟨⟨rip,writable,apart⟩, by rw [target]; cases copy <;> decide⟩,
      by cases copy <;> exact pointer.1⟩
  have eff : (callEffect (fun _ ↦ memoryTarget copy) (memoryReturn copy) t).Holds t v := by
    have ret : memoryCall copy + 6 = memoryReturn copy := by cases copy <;> rfl
    have len : BitVec.ofNat 64 (callMemLen (.rip disp)) = 6 := rfl
    simpa only [callEffect, pushEffect, target, len, ret] using effect
  refine ⟨v, Advances.of_step step (.inl ?_), ready, eff⟩
  rw [eff.rip]
  cases copy
  · exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1c810 (by decide))
  · exact boundary_ne_program pre.outerBoundary (inProgram_of_textOffset 0x1c930 (by decide))

theorem result_memory (pre : DecodePre s boundary bytes) (state : Frame s t)
    {target ret : BitVec 64} {offset count : Nat}
    (effect : (callEffect (fun _ ↦ target) ret t).Holds t v)
    (destination : v.regValue .rdi = stackPtr s - BitVec.ofNat 64 offset)
    (bound : offset ≤ 312) (extent : count + 32 ≤ offset)
    (result : CalleeResult v u boundary count 0) :
    MemoryWriteFrame t u #v[registerRegion s .rdi 80, ScalarFrame.Work.region s 3680 32] := by
  apply memoryWriteFrame_trans (effect.agrees.memoryWriteFrame (push_writes pre state))
  have sp : stackPtr v = stackPtr s - 320#64 := by
    exact effect.writes.1.trans (push_address state)
  have bounds := stack_bounds pre.stack
  have sv : (stackPtr v).toNat = (stackPtr s).toNat - 320 := by
    rw [sp]; exact stack_sub_toNat pre.stack (by decide)
  have dv : (v.regValue .rdi).toNat = (stackPtr s).toNat - offset := by
    rw [destination]; exact stack_sub_toNat pre.stack (by omega)
  intro a ha
  apply result.frame a
  intro region hr hin
  have cases : region = registerRegion v .rdi count ∨ region = Stack.region v 0 := by simpa using hr
  apply ha (ScalarFrame.Work.region s 3680 32) (by simp)
  change (stackPtr s).toNat - 3680 ≤ a.toNat ∧
    a.toNat < (stackPtr s).toNat - 3680 + (3680 - 32)
  rcases cases with rfl | rfl
  · change (v.regValue .rdi).toNat ≤ a.toNat ∧ a.toNat < (v.regValue .rdi).toNat + count at hin
    rw [dv] at hin
    constructor <;> omega
  · change (stackPtr v).toNat - 0 ≤ a.toNat ∧
      a.toNat < (Stack.region v 0).start + (Stack.region v 0).size at hin
    rw [stack_region_end, sv] at hin
    constructor <;> omega

end P256.Proofs.Sec1.Decode.Prepare
