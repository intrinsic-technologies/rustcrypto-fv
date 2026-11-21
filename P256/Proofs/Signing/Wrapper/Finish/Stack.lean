import P256.Proofs.Signing.Wrapper.Finish.State
import P256.Proofs.Program.WrapperMemory
import X86Proofs.Instructions.MovStore.Triple
import X86Proofs.Instructions.MovLoad.Triple

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Finish

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem after_stack_store [Bindings] {initial s t : RamState} {off : Nat}
    (pre : Pre initial) (state : State initial s) (ready : ReadyToStep t)
    (agrees : AgreesExcept [.mem (stackPtr initial-BitVec.ofNat 64 off) 8,.rip] s t)
    (lo : 56 ≤ off) (hi : off ≤ 520)
    (slots : off+8 ≤ 200 ∨ 216 ≤ off) : State initial t := by
  have words (k : Nat) (hk : k ≤ 48 ∨ k = 200 ∨ k = 208) :
      memLoad t.external (stackPtr initial-BitVec.ofNat 64 k) 64 =
      memLoad s.external (stackPtr initial-BitVec.ofNat 64 k) 64 := by
    apply memLoad_agrees_apart agrees
    intro a n hn
    have he : Component.mem a n = .mem (stackPtr initial-BitVec.ofNat 64 off) 8 := by
      simpa using hn
    cases he
    exact stack_sub_apart pre.stack (by omega) (by omega) (by omega) (by omega) (by omega)
  have frame : MemoryWriteFrame s t #v[Stack.region initial 5112] := by
    apply agrees.memoryWriteFrame
    intro c hc a ha
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
    rcases hc with rfl | rfl
    · exact ⟨_,by simp,stack_contains pre (by omega) (by omega) ha⟩
    · exact ha.elim
  refine ⟨bindingsSupported_of_ready_agrees state.bindingsSupported ready agrees,
    supportedMachine_of_ready_agrees state.machine ready agrees, ?_,
    agrees.directionFlagClear (by simp) state.directionFlag,
    (agrees.read (n := 64) (r := 4) (by simp)).trans state.rsp,
    (words 208 (by simp)).trans state.output,
    (words 200 (by simp)).trans state.capacity,
    (words 48 (by decide)).trans state.savedRbx,
    (words 40 (by decide)).trans state.savedR12,
    (words 32 (by decide)).trans state.savedR13,
    (words 24 (by decide)).trans state.savedR14,
    (words 16 (by decide)).trans state.savedR15,
    (words 8 (by decide)).trans state.savedRbp, ?_,
    (agrees.read (n := 64) (r := 5) (by simp)).trans state.rbp,
    fun a ha => agrees.grow a (state.allocated a ha)⟩
  · intro a b hb
    rw [frame a]
    · exact state.loaded a b hb
    · intro r hr ha
      have he : r = Stack.region initial 5112 := by simpa using hr
      subst r
      exact pre.avoids _ (by simp) a ha (.inl ⟨b,hb⟩)
  · have h := words 0 (by decide)
    simp only [BitVec.sub_zero] at h
    exact h.trans state.returnAddress

theorem stack_code_apart {initial : RamState} (pre : Pre initial) {off pc len : Nat}
    (low : off ≤ 5112) (high : 8 ≤ off) (bound : pc+len ≤ 118431) :
    RangeApart (stackPtr initial-BitVec.ofNat 64 off) 8
      (Extracted.textAddress+BitVec.ofNat 64 pc) len := by
  intro i hi j hj he
  apply pre.avoids _ (by simp) _ (stack_contains pre low (by omega) ⟨i,hi,rfl⟩)
  left
  rw [he,BitVec.add_assoc,← BitVec.ofNat_add]
  exact inProgram_of_textOffset _ (by omega)

def stackStoreBytes (zero : Bool) (d : Disp) : List UInt8 :=
  if zero then [0x48, 0xc7, (AddrMode.sib 4 none 0 d).modrm 0] ++
    (AddrMode.sib 4 none 0 d).tail ++ immBytes 32 0
  else [0x48, 0x89, (AddrMode.sib 4 none 0 d).modrm 0] ++ (AddrMode.sib 4 none 0 d).tail

theorem store_stack [Bindings] {initial s : RamState}
    (pre : Pre initial) (st : State initial s)
    (pc : Nat) (zero : Bool) (d : Disp) (offset : Nat)
    (hd : d.value = BitVec.ofNat 64 (520 - offset)) (ho : offset ≤ 520)
    (high : 56 ≤ offset) (align : offset % 8 = 0)
    (slots : offset+8 ≤ 200 ∨ 216 ≤ offset)
    (rip : s.RIP = Extracted.textAddress + BitVec.ofNat 64 pc)
    (code : Extracted.textBytes.toListFrom pc (stackStoreBytes zero d).length = stackStoreBytes zero d)
    (bound : pc + ((if zero then 7 else 3) + (AddrMode.sib 4 none 0 d).tail.length) < 118431)
    : ∃ t, Advances (returnBoundary initial) 1 s t ∧ State initial t ∧
      t.RIP = Extracted.textAddress + BitVec.ofNat 64
        (pc + ((if zero then 7 else 3) + (AddrMode.sib 4 none 0 d).tail.length)) ∧
      t.regValue .r11 = s.regValue .r11 ∧
      MemoryWriteFrame s t #v[Stack.region initial 5112] := by
  let p := Extracted.textAddress + BitVec.ofNat 64 pc
  let am := AddrMode.sib 4 none 0 d
  have address (ip : BitVec 64) : am.addr s ip = stackPtr initial - BitVec.ofNat 64 offset :=
    by
      change stackPtr s + d.value = _
      rw [hd,stack_address st.rsp (by omega)]
      congr 2
      omega
  have hw : MemWritable s (stackPtr initial - BitVec.ofNat 64 offset) 8 :=
    writable_of_grow (stack_sub_writable8 pre.stack (fun a ha hp => pre.avoids _ (by simp) a ha (.inr hp)) (by omega) align) st.allocated
  have finish {t : RamState} {len : Nat} (run : Advances (returnBoundary initial) 1 s t)
      (ready : ReadyToStep t) (ip : t.RIP = p + BitVec.ofNat 64 len)
      (frame : AgreesExcept [.mem (stackPtr initial - BitVec.ofNat 64 offset) 8, .rip] s t) :
      Advances (returnBoundary initial) 1 s t ∧ State initial t ∧
      t.RIP = Extracted.textAddress + BitVec.ofNat 64 (pc+len) ∧
      t.regValue .r11 = s.regValue .r11 ∧
      MemoryWriteFrame s t #v[Stack.region initial 5112] := by
    refine ⟨run,after_stack_store pre st ready frame high ho slots,?_,frame.read (n := 64) (r := 11) (by simp),?_⟩
    · simpa only [p,BitVec.ofNat_add,BitVec.add_assoc] using ip
    · apply frame.memoryWriteFrame
      intro c hc a ha
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hc
      rcases hc with rfl | rfl
      · exact ⟨_,by simp,stack_contains pre (by omega) (by omega) ha⟩
      · exact ha.elim
  cases zero
  · change pc + (3 + am.tail.length) < 118431 at bound
    obtain ⟨t, run, ready, effect⟩ :=
      (mov_m64_r64_effect_step p 0x48 (by simp [RexWPrefix]) 0 am
        (by simp [am, AddrMode.Valid, regLow]) rfl rfl).advances
        (boundary := returnBoundary initial) (readyToStep st.machine st.bindingsSupported)
        (programText_slice (programLoaded_codeIn st.loaded) pc _
          (by change pc + (am.tail.length + 1 + 1 + 1) ≤ 118431; omega) code)
        ⟨rip, by change MemWritable s (am.addr s _) 8; rwa [address],
          by change RangeApart (am.addr s _) 8 p _; rw [address]
             exact stack_code_apart pre (by omega) (by omega) (by omega)⟩
        (by change p + BitVec.ofNat 64 (3 + am.tail.length) ≠ _
            rw [show p + BitVec.ofNat 64 (3 + am.tail.length) =
              Extracted.textAddress + BitVec.ofNat 64 (pc + (3 + am.tail.length)) by
                simp only [p, BitVec.ofNat_add, BitVec.add_assoc]]
            exact boundary_ne_program pre.outside
              (inProgram_of_textOffset _ bound))
    refine ⟨t, finish run ready effect.rip ?_⟩
    simpa only [movM64R64Effect_components, storeAddrAt, address] using effect.agrees
  · change pc + (7 + am.tail.length) < 118431 at bound
    obtain ⟨t, run, ready, effect⟩ :=
      (mov_m64_imm32_effect_step p 0x48 (by simp [RexWPrefix]) am
        (by simp [am, AddrMode.Valid, regLow]) rfl rfl 0).advances
        (boundary := returnBoundary initial) (readyToStep st.machine st.bindingsSupported)
        (programText_slice (programLoaded_codeIn st.loaded) pc _
          (by simp only [List.length_cons, List.length_append, immBytes_length]; omega) code)
        ⟨rip, by change MemWritable s (am.addr s _) 8; rwa [address],
          by change RangeApart (am.addr s _) 8 p _; rw [address]
             exact stack_code_apart pre (by omega) (by omega) (by omega)⟩
        (by change p + BitVec.ofNat 64 (7 + am.tail.length) ≠ _
            rw [show p + BitVec.ofNat 64 (7 + am.tail.length) =
              Extracted.textAddress + BitVec.ofNat 64 (pc + (7 + am.tail.length)) by
                simp only [p, BitVec.ofNat_add, BitVec.add_assoc]]
            exact boundary_ne_program pre.outside
              (inProgram_of_textOffset _ bound))
    refine ⟨t, finish run ready effect.rip ?_⟩
    simpa only [movM64Imm32Effect_components, storeAddrAt, address] using effect.agrees


def stackLoadBytes (d : Disp) : List UInt8 :=
  [0x48,0x8b,(AddrMode.sib 4 none 0 d).modrm 0] ++ (AddrMode.sib 4 none 0 d).tail

theorem load_stack [Bindings] {initial s : RamState}
    (pre : Pre initial) (st : State initial s) (pc : Nat) (d : Disp) (off : Nat)
    (hd : d.value = BitVec.ofNat 64 off) (bound : off+8 ≤ 472)
    (rip : s.RIP = Extracted.textAddress+BitVec.ofNat 64 pc)
    (code : Extracted.textBytes.toListFrom pc (stackLoadBytes d).length = stackLoadBytes d)
    (size : pc+(3+(AddrMode.sib 4 none 0 d).tail.length) < 118431) :
    ∃ t, Advances (returnBoundary initial) 1 s t ∧ State initial t ∧
      t.RIP = Extracted.textAddress+BitVec.ofNat 64 (pc+(3+(AddrMode.sib 4 none 0 d).tail.length)) ∧
      t.regValue .r11 = s.regValue .r11 ∧
      MemoryWriteFrame s t #v[Stack.region initial 5112] := by
  let am := AddrMode.sib 4 none 0 d
  let p := Extracted.textAddress+BitVec.ofNat 64 pc
  change pc+(3+am.tail.length) < 118431 at size
  have address (ip : BitVec 64) : am.addr s ip = stackPtr s+BitVec.ofNat 64 off := by
    change stackPtr s+d.value = _
    rw [hd]
  obtain ⟨t,run,ready,effect⟩ := (mov_r64_m64_effect_step p 0x48
    (by simp [RexWPrefix]) 0 am (by simp [am,AddrMode.Valid,regLow]) rfl rfl).advances
    (boundary := returnBoundary initial) (readyToStep st.machine st.bindingsSupported)
    (programText_slice (programLoaded_codeIn st.loaded) pc _
      (by change pc+(am.tail.length+1+1+1) ≤ 118431; omega) code)
    ⟨rip,by change MemReadable s (am.addr s _) 8; rw [address]; exact stack_readable pre st bound⟩
    (by change p+BitVec.ofNat 64 (3+am.tail.length) ≠ _
        rw [show p+BitVec.ofNat 64 (3+am.tail.length) =
          Extracted.textAddress+BitVec.ofNat 64 (pc+(3+am.tail.length)) by
            simp only [p,BitVec.ofNat_add,BitVec.add_assoc]]
        exact boundary_ne_program pre.outside (inProgram_of_textOffset _ size))
  have ag : AgreesExcept [.reg 0,.rip] s t := effect.agrees
  refine ⟨t,run,st.after_registers ready ag (by simp [Component.Covers]) (by simp) (by simp),?_,ag.read (n := 64) (r := 11) (by simp),?_⟩
  · have hip : t.RIP = p+BitVec.ofNat 64 (3+am.tail.length) := effect.rip
    simpa only [p,BitVec.ofNat_add,BitVec.add_assoc] using hip
  · intro a _
    rw [ag.external (by simp [Component.Covers])]

end P256.Proofs.Signing.Wrapper.Finish
