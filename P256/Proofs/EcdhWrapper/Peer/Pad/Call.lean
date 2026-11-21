import P256.Proofs.EcdhWrapper.Peer.Pad.Memory
import P256.Proofs.Program.Copy.Pointer
import X86Proofs.Program.ReadWrite.Bytes

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Peer.Pad

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

variable [Bindings] {initial t : RamState} {secret peer : ByteArray} {slices : Array Input}

def memoryCall (copy : Bool) : BitVec 64 := if copy then 0x106a37 else 0x106a23
def memoryReturn (copy : Bool) : BitVec 64 := if copy then 0x106a3d else 0x106a29
def memoryTarget (copy : Bool) : BitVec 64 := if copy then 0x11c930 else 0x11c810

theorem memory_call (copy : Bool) (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices)
    (outside : ¬ InProgram (returnBoundary initial).rip)
    (readyT : ReadyToStep t) (loaded : ProgramLoaded t)
    (grow : ∀ a : BitVec 64, (initial.external[a]?).isSome → (t.external[a]?).isSome)
    (rsp : stackPtr t=stackPtr initial-504)
    (rip : t.RIP = memoryCall copy) :
    ∃ v, Advances (returnBoundary initial) 1 t v ∧ ReadyToStep v ∧
      (callEffect (fun _ ↦ memoryTarget copy) (memoryReturn copy) t).Holds t v := by
  have push : pushAddr t=stackPtr initial-512#64 := by
    rw [pushAddr,rsp,BitVec.sub_sub]; rfl
  let disp : BitVec 32 := if copy then 0xfdabb else 0xfdb27
  have pointer : MemReadable t (if copy then 0x2044f8 else 0x204550) 8 ∧
      (Operand.mem (if copy then 0x2044f8 else 0x204550) : Operand 64).read t = memoryTarget copy := by
    cases copy
    · have hbytes : ∀ i : Fin 8,
          Extracted.programSections.fetchByte (0x204550 + BitVec.ofNat 64 i.val) =
            some (storedByte (0x11c810 : BitVec 64) i.val) := by decide +kernel
      have hb : Bytes t.external 0x204550 8 (storedByte (0x11c810 : BitVec 64)) :=
        fun i hi ↦ loaded _ _ (hbytes ⟨i,hi⟩)
      exact ⟨hb.readable (by decide), hb.memLoad (by decide) (by decide)⟩
    · exact memcpy_pointer loaded
  have target : callMemPtr (memoryCall copy) (.rip disp) t = memoryTarget copy := by
    cases copy <;> exact pointer.2
  have writable : MemWritable t (pushAddr t) 8 := by
    rw [push]
    exact writable_of_grow (stack_sub_writable8 call.stackAvailable.1
      (fun a ha ht ↦ call_stack_avoids call a ha (.inr ht)) (offset := 512)
      (by decide) (by decide)) grow
  have apart : RangeApart (pushAddr t) 8 (memoryCall copy) 6 := by
    rw [push]
    intro i hi j hj he
    apply call_stack_avoids call (stackPtr initial-512#64+BitVec.ofNat 64 i)
      (by
        apply memoryRegion_contains_add call.stackAvailable.1.1 (len := 8) _ _ hi
        · rw [stack_sub_toNat call.stackAvailable.1 (by decide : 512 ≤ 4104)]
          change (stackPtr initial).toNat-4104 ≤ (stackPtr initial).toNat-512
          omega
        · rw [stack_region_end,stack_sub_toNat call.stackAvailable.1 (by decide : 512 ≤ 4104)]
          omega)
    apply Or.inl
    change InProgram (stackPtr initial - 512#64 + BitVec.ofNat 64 i)
    rw [he]
    cases copy
    · have h := inProgram_of_textOffset (0x6a23+j) (by omega)
      simpa only [BitVec.ofNat_add, ← BitVec.add_assoc, memoryCall,
        Bool.false_eq_true, ite_false, ite_true, Extracted.textAddress, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using h
    · have h := inProgram_of_textOffset (0x6a37+j) (by omega)
      simpa only [BitVec.ofNat_add, ← BitVec.add_assoc, memoryCall,
        Bool.false_eq_true, ite_false, ite_true, Extracted.textAddress, BitVec.reduceAdd, BitVec.ofNat_eq_ofNat] using h
  have code : CodeIn (codeRange (memoryCall copy) (encodeCallM64 (.rip disp))) t := by
    cases copy
    · exact programText_slice (programLoaded_codeIn loaded) 0x6a23 _
        (by decide) (by decide +kernel)
    · exact programText_slice (programLoaded_codeIn loaded) 0x6a37 _
        (by decide) (by decide +kernel)
  obtain ⟨v, step, ready, effect⟩ := call_m64_effect_step (memoryCall copy) (.rip disp)
    trivial rfl rfl t readyT code
    ⟨⟨⟨rip,writable,apart⟩, by rw [target]; cases copy <;> decide⟩,
      by cases copy <;> exact pointer.1⟩
  have eff : (callEffect (fun _ ↦ memoryTarget copy) (memoryReturn copy) t).Holds t v := by
    have ret : memoryCall copy + 6 = memoryReturn copy := by cases copy <;> rfl
    have len : BitVec.ofNat 64 (callMemLen (.rip disp)) = 6 := rfl
    simpa only [callEffect, pushEffect, target, len, ret] using effect
  refine ⟨v, Advances.of_step step (.inl ?_), ready, eff⟩
  rw [eff.rip]
  cases copy
  · exact boundary_ne_program outside (inProgram_of_textOffset 0x1c810 (by decide))
  · exact boundary_ne_program outside (inProgram_of_textOffset 0x1c930 (by decide))

end P256.Proofs.EcdhWrapper.Peer.Pad
