import P256.Proofs.EcdhWrapper.Scalar.Prefix.Memory
import X86Proofs.Instructions.MovStore.Triple

set_option autoImplicit false

namespace P256.Proofs.EcdhWrapper.Finish.Return

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def zeroOffset (n : Nat) := 0x6c0c + 5*n - if n=0 then 0 else 1

def zeroDisp (n : Nat) : Disp := if n=0 then .none else .d8 (BitVec.ofNat 8 n)

def zeroBytes (n : Nat) : List UInt8 :=
  let am := AddrMode.sib 4 none 0 (zeroDisp n)
  0xc6 :: am.modrm 0 :: (am.tail ++ immBytes 8 0)

set_option maxRecDepth 2048 in
theorem zero_code : ∀ n : Fin 32,
    Extracted.textBytes.toListFrom (zeroOffset n) (zeroBytes n).length=zeroBytes n ∧
    zeroOffset n+(3+(AddrMode.sib 4 none 0 (zeroDisp n)).tail.length)=zeroOffset (n+1) ∧
    (zeroDisp n).value=BitVec.ofNat 64 n := by decide +kernel

set_option maxRecDepth 2048 in
theorem zero [Bindings] {initial s : RamState} {secret peer : ByteArray} {slices : Array Input}
    (call : ValidCallWithSlices ecdhDiffieHellman initial [secret,peer] slices)
    (outside : ¬ InProgram (returnBoundary initial).rip)
    (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (grow : ∀ a : BitVec 64, (initial.external[a]?).isSome → (s.external[a]?).isSome)
    (rsp : stackPtr s=stackPtr initial-504) (rip : s.RIP=0x106c0c) :
    ∃ t, Advances (returnBoundary initial) 32 s t ∧ ReadyToStep t ∧
      ProgramLoaded t ∧ t.RIP=0x106cab ∧
      AgreesExcept [.mem (stackPtr initial-504) 32,.rip] s t := by
  have stack : Stack.Valid initial 4104 := call.stackAvailable.1
  have covers {a : BitVec 64} (h : (Component.mem (stackPtr initial-504) 32).Covers a) :
      (callStack ecdhDiffieHellman initial).Contains a.toNat :=
    stack_component_within (routine := ecdhDiffieHellman) stack (offset := 504) (by decide) (by decide) h
  have loop : ∀ n≤32, ∃ t, Advances (returnBoundary initial) n s t ∧ ReadyToStep t ∧
      ProgramLoaded t ∧ t.RIP=Extracted.textAddress+BitVec.ofNat 64 (zeroOffset n) ∧
      AgreesExcept [.mem (stackPtr initial-504) 32,.rip] s t := by
    intro n hn
    induction n with
    | zero => exact ⟨s,(by simp),ready,loaded,rip,AgreesExcept.refl _ _⟩
    | succ n ih =>
      obtain ⟨t,run,rt,lt,ip,g⟩ := ih (by omega)
      have hcode := zero_code ⟨n,by omega⟩
      have sp : stackPtr t=stackPtr initial-504 := (g.read (n := 64) (r := 4) (by simp)).trans rsp
      let am := AddrMode.sib 4 none 0 (zeroDisp n)
      let pc := Extracted.textAddress+BitVec.ofNat 64 (zeroOffset n)
      have address (ip : BitVec 64) : am.addr t ip=stackPtr initial-BitVec.ofNat 64 (504-n) := by
        change stackPtr t+(zeroDisp n).value=_
        rw [hcode.2.2,sp,← BitVec.ofNat_sub_ofNat_of_le 504 n (by omega) (by omega)]
        simp only [BitVec.sub_eq_add_neg,BitVec.neg_add,BitVec.neg_neg,BitVec.add_assoc,BitVec.ofNat_eq_ofNat]
      have writable : MemWritable t (stackPtr initial-BitVec.ofNat 64 (504-n)) 1 := by
        have hr := readable_of_grow (stack_sub_readable stack (offset := 504-n)
          (len := 1) (by omega) (by omega)) (fun a h ↦ g.grow a (grow a h))
        apply MemWritable.of_not_reserved (by decide) hr.low hr.mem
        intro i hi hp
        exact call_stack_avoids call _ (by
          apply memoryRegion_contains_add stack.1 (len := 1) _ _ hi
          · rw [stack_sub_toNat stack (by omega : 504-n≤4104)]
            change (stackPtr initial).toNat-4104≤_
            omega
          · rw [stack_region_end,stack_sub_toNat stack (by omega : 504-n≤4104)]
            have := stack_bounds stack
            omega) (.inr hp)
      have apart : RangeApart (stackPtr initial-BitVec.ofNat 64 (504-n)) 1 pc (3+am.tail.length) := by
        intro i hi j hj eq
        apply (call.separation.2 (callStack ecdhDiffieHellman initial) (by simp)).2 _
          (stack_component_within (routine := ecdhDiffieHellman) stack (offset := 504-n) (by change 504-n≤4104; omega) (by omega) ⟨i,hi,rfl⟩) (.inl ?_)
        rw [eq]
        change InProgram (Extracted.textAddress+BitVec.ofNat 64 (zeroOffset n)+BitVec.ofNat 64 j)
        rw [BitVec.add_assoc,← BitVec.ofNat_add]
        exact inProgram_of_textOffset _ (by have := hcode.2.1; dsimp only [am,zeroOffset] at *; omega)
      have next : pc+BitVec.ofNat 64 (3+am.tail.length)=
          Extracted.textAddress+BitVec.ofNat 64 (zeroOffset (n+1)) := by
        change Extracted.textAddress+BitVec.ofNat 64 (zeroOffset n)+BitVec.ofNat 64 (3+am.tail.length)=_
        rw [BitVec.add_assoc,← BitVec.ofNat_add,hcode.2.1]
      obtain ⟨u,step,ru,e⟩ := (mov_m8_imm8_effect_step pc am
        (by by_cases h : n=0 <;> simp [am,zeroDisp,h,AddrMode.Valid,regLow]) rfl rfl 0).advances (boundary := returnBoundary initial) rt
        (programText_slice (programLoaded_codeIn lt) (zeroOffset n) _
          (by have := hcode.2.1; change zeroOffset n+(zeroBytes n).length≤118431
              simp only [zeroBytes,List.length_cons,List.length_append,immBytes_length]
              dsimp only [am,zeroOffset] at *; omega) hcode.1)
        ⟨ip,by change MemWritable t (am.addr t _) 1; rw [address]; exact writable,
          by change RangeApart (am.addr t _) 1 pc _; rw [address]; exact apart⟩
        (by change pc+BitVec.ofNat 64 (3+am.tail.length)≠_; rw [next]; exact boundary_ne_program outside (inProgram_of_textOffset _
          (by dsimp only [zeroOffset]; omega)))
      have small : AgreesExcept [.mem (stackPtr initial-BitVec.ofNat 64 (504-n)) 1,.rip] t u := by
        simpa only [movM8Imm8Effect_components,storeAddrAt,address] using e.agrees
      have wide : AgreesExcept [.mem (stackPtr initial-504) 32,.rip] t u := by
        apply small.widen
        · intro c hc hm
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
          rcases hc with rfl | rfl
          · simp [Component.isMem] at hm
          · simp
        · intro a c hc hv
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
          rcases hc with rfl | rfl
          · obtain ⟨i,hi,rfl⟩ := hv
            refine ⟨.mem (stackPtr initial-504) 32,by simp,n+i,by omega,?_⟩
            rw [BitVec.ofNat_add,← BitVec.add_assoc]
            congr 1
            rw [← BitVec.ofNat_sub_ofNat_of_le 504 n (by omega) (by omega)]
            simp only [BitVec.sub_eq_add_neg,BitVec.neg_add,BitVec.neg_neg,BitVec.add_assoc,BitVec.ofNat_eq_ofNat]
          · exact hv.elim
      have total : AgreesExcept [.mem (stackPtr initial-504) 32,.rip] s u := (g.trans wide).mono (by simp)
      refine ⟨u,run.trans step,ru,?_,e.rip.trans next,total⟩
      intro a b hb
      rw [wide.byte ?_]
      · exact lt a b hb
      · intro c hc hv
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
        rcases hc with rfl | rfl
        · exact (call.separation.2 (callStack ecdhDiffieHellman initial) (by simp)).2
            a (covers hv) (.inl ⟨b,hb⟩)
        · exact hv.elim
  exact loop 32 (by decide)

end P256.Proofs.EcdhWrapper.Finish.Return
