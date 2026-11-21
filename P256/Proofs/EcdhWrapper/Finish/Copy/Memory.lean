import P256.Proofs.EcdhWrapper.Model
import P256.Proofs.EcdhWrapper.Peer.Buffer.Memory
import P256.Proofs.Program.WrapperMemory
import P256.Proofs.Program.Output
import X86Proofs.Instructions.Cmp.Generated.Imm8.Triple
import P256.Proofs.Common.Der.Decode.Header.Control

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Finish.Copy

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Common.Instructions

variable [Bindings] {initial s t : RamState} {secret peer : ByteArray} {slices : Array Input}

omit [Bindings] in
theorem output_eq : outputRegion ecdhDiffieHellman initial [secret,peer]=
    registerRegion initial .rcx 40 := by
  change registerRegion initial .rcx (8+(P256.Spec.Ecdh.diffieHellman #[secret,peer]).size)=_
  rw [diffieHellman_size]

theorem capacity (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices) :
    40≤(initial.regValue .r8).toNat := by
  have h := call.outputSufficesIfAccepted rfl
  change 8+(P256.Spec.Ecdh.diffieHellman #[secret,peer]).size≤_ at h
  simpa only [diffieHellman_size] using h

theorem output_bound (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices) :
    (registerRegion initial .rcx 40).Bounded := by
  have h := (call.outputInMemoryIfAccepted rfl).2.1
  rwa [output_eq] at h

theorem output_contains (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices)
    {off len : Nat} {a : BitVec 64} (bound : off+len≤40)
    (covered : (Component.mem (initial.regValue .rcx+BitVec.ofNat 64 off) len).Covers a) :
    (registerRegion initial .rcx 40).Contains a.toNat := by
  obtain ⟨i,hi,rfl⟩ := covered
  rw [BitVec.add_assoc,←BitVec.ofNat_add]
  exact memoryRegion_contains_add (output_bound call) (Nat.le_refl _) (Nat.le_refl _) (by change off+i<40; omega)

theorem output_avoids (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices) :
    (registerRegion initial .rcx 40).Avoids (fun a => InProgram a ∨ InPageTables a) := by
  have h := ((call.outputSeparationIfAccepted rfl).2
    (outputRegion ecdhDiffieHellman initial [secret,peer]) (by simp)).2
  rwa [output_eq] at h

theorem output_writable (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices)
    (grow : ∀ a : BitVec 64, (initial.external[a]?).isSome → (s.external[a]?).isSome) :
    CrossPageStore.Writable s (initial.regValue .rcx) 40 := by
  have allocated : (registerRegion initial .rcx 40).Allocated initial.external := by
    have h := (call.outputInMemoryIfAccepted rfl).2.2
    rwa [output_eq] at h
  have hr := readable_of_grow
    (memoryRegion_memReadable (output_bound call) allocated (Nat.le_refl _) (Nat.le_refl _)) grow
  refine ⟨hr,tables_of_not_reserved (by decide) hr.low ?_⟩
  intro i hi hp
  exact output_avoids call _ (output_contains call (off := 0) (len := 40) (by decide)
    (by simpa only [BitVec.add_zero] using (show (Component.mem (initial.regValue .rcx) 40).Covers
      (initial.regValue .rcx+BitVec.ofNat 64 i) from ⟨i,hi,rfl⟩))) (.inr hp)

theorem output_code (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices)
    {off len pc n : Nat} (bound : off+len≤40) (code : pc+n≤118431) :
    RangeApart (initial.regValue .rcx+BitVec.ofNat 64 off) len
      (Extracted.textAddress+BitVec.ofNat 64 pc) n := by
  intro i hi j hj he
  apply output_avoids call _ (output_contains call bound ⟨i,hi,rfl⟩)
  rw [he]
  exact .inl (by simpa only [BitVec.ofNat_add,BitVec.add_assoc] using
    inProgram_of_textOffset (pc+j) (by omega))

theorem output_stack (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices)
    {off len outOff outLen : Nat} (bound : off≤4104) (extent : len≤off+8)
    (output : outOff+outLen≤40) : RangeApart
      (initial.regValue .rcx+BitVec.ofNat 64 outOff) outLen
      (stackPtr initial-BitVec.ofNat 64 off) len := by
  intro i hi j hj he
  have sep := (call.outputSeparationIfAccepted rfl).1 (0 : Fin 5) (4 : Fin 5) (by decide)
  apply sep _
  · rw [output_eq]
    exact output_contains call output ⟨i,hi,rfl⟩
  · rw [he]
    exact stack_component_within call.stackAvailable.1 bound extent ⟨j,hj,rfl⟩

def components (initial : RamState) : List Component :=
  [.reg 0,.reg 1,.reg 2,.reg 8,.flags,.rip,.mem (initial.regValue .rcx+8) 32]

theorem loaded_after (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices)
    (loaded : ProgramLoaded s) (ag : AgreesExcept (components initial) s t) : ProgramLoaded t := by
  intro a b hb
  rw [ag.byte ?_]
  · exact loaded a b hb
  · intro c hc cover
    simp only [components,List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals try exact cover.elim
    exact output_avoids call a (output_contains call (off := 8) (len := 32) (by decide) cover) (.inl ⟨b,hb⟩)

theorem stack_read (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices)
    (ag : AgreesExcept (components initial) s t) {off n : Nat}
    (bound : off≤4104) (extent : n/8≤off+8) :
    memLoad t.external (stackPtr initial-BitVec.ofNat 64 off) n=
      memLoad s.external (stackPtr initial-BitVec.ofNat 64 off) n := by
  apply memLoad_agrees_apart ag
  intro a len hm
  simp only [components,List.mem_cons,List.not_mem_nil,or_false,false_or,Component.mem.injEq,reduceCtorEq] at hm
  rcases hm with ⟨rfl,rfl⟩
  exact output_stack call (outOff := 8) (outLen := 32) bound extent (by decide)

omit [Bindings] in
theorem store_agrees {off : Nat} (bound : 8≤off ∧ off+8≤40)
    (ag : AgreesExcept [.mem (initial.regValue .rcx+BitVec.ofNat 64 off) 8,.rip] s t) :
    AgreesExcept (components initial) s t := by
  apply ag.widen
  · intro c hc hn
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl
    · simp [Component.isMem] at hn
    · simp [components]
  · intro a c hc ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl
    · obtain ⟨i,hi,rfl⟩ := ha
      refine ⟨.mem (initial.regValue .rcx+8) 32,by simp [components],off-8+i,by omega,?_⟩
      change initial.regValue .rcx+BitVec.ofNat 64 off+BitVec.ofNat 64 i=
        initial.regValue .rcx+BitVec.ofNat 64 8+BitVec.ofNat 64 (off-8+i)
      simp only [BitVec.add_assoc,←BitVec.ofNat_add]
      rw [show off+i=8+(off-8+i) by omega]
    · exact ha.elim

omit [Bindings] in
theorem offsets_apart {base : BitVec 64} {a b : Nat}
    (ha : a+8≤40) (hb : b+8≤40) (sep : a+8≤b ∨ b+8≤a) :
    RangeApart (base+BitVec.ofNat 64 a) 8 (base+BitVec.ofNat 64 b) 8 := by
  intro i hi j hj eq
  have h := (BitVec.add_right_inj base).mp (by
    simpa only [BitVec.add_assoc,←BitVec.ofNat_add] using eq)
  have hn := congrArg BitVec.toNat h
  simp only [BitVec.toNat_ofNat] at hn
  omega

end P256.Proofs.EcdhWrapper.Finish.Copy
