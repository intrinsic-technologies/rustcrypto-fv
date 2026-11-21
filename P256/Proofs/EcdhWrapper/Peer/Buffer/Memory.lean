import P256.Proofs.Program.StackBuffer
import P256.Proofs.Program.ScalarFrame.Memory
import P256.Proofs.Sec1.Decode.Prepare.Copy.Memory
import P256.Proofs.EcdhWrapper.Copy.Support

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Peer.Buffer

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

def components (base : BitVec 64) : List Component :=
  [.reg 0,.reg 1,.reg 2,.reg 6,.reg 7,.reg 8,.reg 9,.rip,
    .mem (base+48) 54,.mem (base+112) 54,.mem (base+240) 65]

variable [Bindings] {initial s t : RamState} {secret peer : ByteArray} {slices : Array Input}

omit [Bindings] in
theorem address (rsp : stackPtr s=stackPtr initial-504) {off : Nat} (h : off≤504) :
    stackPtr s+BitVec.ofNat 64 off = stackPtr initial-BitVec.ofNat 64 (504-off) :=
  ScalarFrame.scalar_stack_address (frameOffset := 504) rsp (by decide) h

theorem readable (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices)
    (grow : ∀ a : BitVec 64, (initial.external[a]?).isSome → (s.external[a]?).isSome)
    (rsp : stackPtr s=stackPtr initial-504) {off len : Nat} (bound : off+len≤504) :
    MemReadable s (stackPtr s+BitVec.ofNat 64 off) len := by
  rw [address rsp (by omega)]
  exact readable_of_grow (stack_sub_readable (show Stack.Valid initial 4104 from call.stackAvailable.1) (by omega) (by omega)) grow

theorem writable (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices)
    (grow : ∀ a : BitVec 64, (initial.external[a]?).isSome → (s.external[a]?).isSome)
    (rsp : stackPtr s=stackPtr initial-504) {off len : Nat} (bound : off+len≤504) (pos : 0<len) :
    CrossPageStore.Writable s (stackPtr s+BitVec.ofNat 64 off) len := by
  rw [address rsp (by omega)]
  have avoids : (Stack.region initial 4104).Avoids (fun a => InProgram a ∨ InPageTables a) := by
    intro a ha hp
    exact call_stack_avoids call a ha hp
  exact stack_buffer_writable (show Stack.Valid initial 4104 from call.stackAvailable.1) avoids grow
    (by omega) (by omega) pos

theorem byte_writable (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices)
    (grow : ∀ a : BitVec 64, (initial.external[a]?).isSome → (s.external[a]?).isSome)
    (rsp : stackPtr s=stackPtr initial-504) {off : Nat} (bound : off+1≤504) :
    MemWritable s (stackPtr s+BitVec.ofNat 64 off) 1 := by
  have hw := writable call grow rsp bound (by decide : 0<1)
  exact ⟨hw.low, hw.mem, hw.tables⟩

theorem code_apart (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices)
    (rsp : stackPtr s=stackPtr initial-504) {off len pc n : Nat} (bound : off+len≤504)
    (code : pc+n≤118431) : RangeApart (stackPtr s+BitVec.ofNat 64 off) len
      (Extracted.textAddress+BitVec.ofNat 64 pc) n := by
  rw [address rsp (by omega)]
  have avoids : (Stack.region initial 4104).Avoids (fun a => InProgram a ∨ InPageTables a) := by
    intro a ha hp
    exact call_stack_avoids call a ha hp
  exact stack_buffer_code_apart (show Stack.Valid initial 4104 from call.stackAvailable.1) avoids
    (by omega) (by omega) code

omit [Bindings] in
theorem store_agrees {base : BitVec 64} {off len : Nat}
    (ag : AgreesExcept [.mem (base+BitVec.ofNat 64 off) len,.rip] s t)
    (bound : (48≤off ∧ off+len≤102) ∨ (112≤off ∧ off+len≤166) ∨
      (240≤off ∧ off+len≤305)) : AgreesExcept (components base) s t := by
  apply ag.widen
  · intro c hc hm
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl
    · simp [Component.isMem] at hm
    · simp [components]
  · intro a c hc ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl
    · obtain ⟨i,hi,rfl⟩ := ha
      rcases bound with h | h | h
      · refine ⟨.mem (base+48) 54,by simp [components],off-48+i,by omega,?_⟩
        change base+BitVec.ofNat 64 off+BitVec.ofNat 64 i =
          base+BitVec.ofNat 64 48+BitVec.ofNat 64 (off-48+i)
        simp only [BitVec.add_assoc,←BitVec.ofNat_add]
        rw [show off+i=48+(off-48+i) by omega]
      · refine ⟨.mem (base+112) 54,by simp [components],off-112+i,by omega,?_⟩
        change base+BitVec.ofNat 64 off+BitVec.ofNat 64 i =
          base+BitVec.ofNat 64 112+BitVec.ofNat 64 (off-112+i)
        simp only [BitVec.add_assoc,←BitVec.ofNat_add]
        rw [show off+i=112+(off-112+i) by omega]
      · refine ⟨.mem (base+240) 65,by simp [components],off-240+i,by omega,?_⟩
        change base+BitVec.ofNat 64 off+BitVec.ofNat 64 i =
          base+BitVec.ofNat 64 240+BitVec.ofNat 64 (off-240+i)
        simp only [BitVec.add_assoc,←BitVec.ofNat_add]
        rw [show off+i=240+(off-240+i) by omega]
    · exact ha.elim

theorem inside (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices)
    (rsp : stackPtr s=stackPtr initial-504) {off len : Nat} (bound : off+len≤504)
    {a : BitVec 64} (cover : (Component.mem (stackPtr s+BitVec.ofNat 64 off) len).Covers a) :
    (Stack.region initial 4104).Contains a.toNat := by
  obtain ⟨i,hi,rfl⟩ := cover
  rw [address rsp (by omega)]
  exact stack_buffer_contains (show Stack.Valid initial 4104 from call.stackAvailable.1)
    (by omega) (by omega)
    (memoryRegion_contains_add (stack_buffer_bounded
      (show Stack.Valid initial 4104 from call.stackAvailable.1) (by omega) (by omega))
      (Nat.le_refl _) (Nat.le_refl _) hi)

theorem loaded_after (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices)
    (loaded : ProgramLoaded s) (rsp : stackPtr s=stackPtr initial-504)
    (ag : AgreesExcept (components (stackPtr s)) s t) : ProgramLoaded t := by
  intro a b hb
  rw [ag.byte ?_]
  · exact loaded a b hb
  · intro c hc cover
    simp only [components,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact cover.elim
    all_goals exact call_stack_avoids call a (inside call rsp (by decide) cover) (.inl ⟨b,hb⟩)

end P256.Proofs.EcdhWrapper.Peer.Buffer
