import Sha3.Proofs.Permutation.Layout
import Sha3.Proofs.Permutation.LoadStore.Push
import Sha3.Proofs.Permutation.Compose

namespace Sha3.Proofs.Permutation

open X86 X86.Machine X86.UserProcess X86Proofs Prelude Sha3.Spec.Program

variable {copy : Copy}

structure EntryStackPre (copy : Copy) (s : RamState) : Prop where
  rip : s.RIP = entryAddress copy
  stack : Stack.Valid s frameBytes
  avoid : (Stack.region s frameBytes).Avoids fun address ↦
    InProgram address ∨ InPageTables address

def pushBytes : List UInt8 := [0x55, 0x41, 0x57, 0x41, 0x56, 0x41, 0x55, 0x41, 0x54, 0x53]

theorem pushBytes_fetch (copy : Copy) : ∀ i : Fin pushBytes.length,
    Extracted.programSections.fetchByte (entryAddress copy + BitVec.ofNat 64 i.val) =
      some pushBytes[i.val] := by cases copy <;> decide +kernel

theorem pushBytes_inProgram (copy : Copy) (x : BitVec 64 × UInt8)
    (hx : x ∈ codeRange (entryAddress copy) pushBytes) : InProgram x.1 := by
  obtain ⟨i, rfl⟩ := (mem_codeRange_iff _ _ _).mp hx
  exact ⟨_, imageSections_mem_toCodeMap_of_fetchByte (pushBytes_fetch copy i)⟩

theorem EntryStackPre.readable {s : RamState} (h : EntryStackPre copy s) {offset : Nat}
    (h8 : 8 ≤ offset) (hoff : offset ≤ frameBytes) :
    MemReadable s (s.regValue .rsp - BitVec.ofNat 64 offset) 8 := by
  refine ⟨?_, fun i hi ↦ ?_⟩
  · have := stack_sub_low h.stack hoff
    change _ + offset < 2^32 at this
    omega
  · exact Option.isSome_iff_exists.mpr (stack_sub_allocated h.stack hoff (by omega))

theorem EntryStackPre.slot_avoid {s : RamState} (h : EntryStackPre copy s) {offset : Nat}
    (h8 : 8 ≤ offset) (hoff : offset ≤ frameBytes) {i : Nat} (hi : i < 8) :
    ¬ (InProgram (s.regValue .rsp - BitVec.ofNat 64 offset + BitVec.ofNat 64 i) ∨
      InPageTables (s.regValue .rsp - BitVec.ofNat 64 offset + BitVec.ofNat 64 i)) :=
  h.avoid _ (stack_sub_contains h.stack hoff (by omega))

theorem EntryStackPre.page {s : RamState} (h : EntryStackPre copy s) {offset : Nat}
    (hoff : offset ≤ frameBytes) (halign : offset % 8 = 0) :
    (s.regValue .rsp - BitVec.ofNat 64 offset).toNat % 4096 + 8 ≤ 4096 := by
  rw [stack_sub_toNat h.stack.2.2.1 hoff]
  have ha := h.stack.2.2.2
  change (s.regValue .rsp).toNat % 16 = 8 at ha
  have hb := h.stack.2.2.1
  change frameBytes ≤ (s.regValue .rsp).toNat at hb
  omega

theorem EntryStackPre.apart {s : RamState} (h : EntryStackPre copy s) {offset : Nat}
    (h8 : 8 ≤ offset) (hoff : offset ≤ frameBytes) :
    RangeApart (s.regValue .rsp - BitVec.ofNat 64 offset) 8
      (entryAddress copy) pushBytes.length := by
  intro i hi j hj he
  exact h.slot_avoid h8 hoff hi (.inl (he ▸
    pushBytes_inProgram copy _ (mem_codeRange (entryAddress copy) pushBytes j hj)))

def pushPC (copy : Copy) (k : Nat) : BitVec 64 :=
  entryAddress copy + match k with
    | 0 => 0
    | 1 => 1
    | 2 => 3
    | 3 => 5
    | 4 => 7
    | 5 => 9
    | _ => 10

def pushReg (i : Fin 6) : BitVec 4 := #v[5, 15, 14, 13, 12, 3][i]

def pushSlot (initial : RamState) (k : Nat) : BitVec 64 :=
  initial.regValue .rsp - BitVec.ofNat 64 (8 * k)

structure PushProgress (copy : Copy) (initial : RamState) (k : Nat) (s : RamState) : Prop where
  rip : s.RIP = pushPC copy k
  stack : stackPtr s = pushSlot initial k
  registers : ∀ r : BitVec 5, r ≠ 4 →
    (Operand.reg r : Operand 64).read s = (Operand.reg r : Operand 64).read initial
  saved : ∀ i : Fin 6, i.val < k →
    (Operand.mem (pushSlot initial (i.val + 1)) : Operand 64).read s =
      (Operand.reg ((pushReg i).setWidth 5) : Operand 64).read initial
  memory : MemoryWriteFrame initial s #v[⟨(frameBase initial).toNat, frameBytes⟩]
  grow : ∀ address : BitVec 64, (initial.external[address]?).isSome → (s.external[address]?).isSome
  rest : scalarFrame s = scalarFrame initial
  returnSlot : (Operand.mem (initial.regValue .rsp) : Operand 64).read s =
    (Operand.mem (initial.regValue .rsp) : Operand 64).read initial

theorem pushSlot_succ (initial : RamState) (k : Nat) :
    pushSlot initial k - 8 = pushSlot initial (k + 1) := by
  simp only [pushSlot, Nat.mul_add, Nat.mul_one, BitVec.ofNat_add, BitVec.sub_sub]
  rfl

theorem pushReg_ne_rsp (i : Fin 6) : (pushReg i).setWidth 5 ≠ 4 := by
  revert i
  decide +kernel

theorem pushPC_next (copy : Copy) (i : Fin 6) :
    pushPC copy i.val + BitVec.ofNat 64 (encodePushR64 (pushReg i)).length =
      pushPC copy (i.val + 1) := by
  cases copy <;> finite_cases i <;> rfl

theorem pushPC_inProgram (copy : Copy) (k : Nat) (hk : k ≤ 6) : InProgram (pushPC copy k) := by
  have h : ∀ k : Fin 7,
      (Extracted.programSections.fetchByte (pushPC copy k.val)).isSome := by
    cases copy <;> decide +kernel
  obtain ⟨byte, hb⟩ := Option.isSome_iff_exists.mp (h ⟨k, by omega⟩)
  exact ⟨byte, imageSections_mem_toCodeMap_of_fetchByte hb⟩

theorem push_step_code (copy : Copy) (i : Fin 6) :
    ∀ x ∈ codeRange (pushPC copy i.val) (encodePushR64 (pushReg i)),
      x ∈ codeRange (entryAddress copy) pushBytes := by
  cases copy <;> finite_cases i <;> decide +kernel

theorem pushSlot_apart (initial : RamState) {j k : Nat} (hjk : j < k) (hk : k ≤ 6) :
    RangeApart (pushSlot initial k) 8 (pushSlot initial j) 8 := by
  have h64 : 8 * k < 2^64 := by omega
  have hj64 : 8 * j < 2^64 := by omega
  have ho : OffsetsApart (-BitVec.ofNat 64 (8 * k)) 8
      (-BitVec.ofNat 64 (8 * j)) 8 := by
    simp only [OffsetsApart, BitVec.toNat_sub, BitVec.toNat_neg, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt h64, Nat.mod_eq_of_lt hj64]
    omega
  intro i hi l hl
  simpa only [pushSlot, BitVec.sub_eq_add_neg] using ho.ne
    (initial.regValue .rsp) hi hl (by decide)

theorem effect_read_mem_of_apart {s t : RamState} {e : Effect} {addr other : BitVec 64}
    (he : e.Holds s t) (hc : e.components = [.reg 4, .mem addr 8, .rip])
    (ha : RangeApart addr 8 other 8) :
    (Operand.mem other : Operand 64).read t = (Operand.mem other : Operand 64).read s := by
  apply memLoad_congr
  intro i hi
  simp only [memByte, PhysicalMemory.read]
  apply congrArg (fun x : Option UInt8 ↦ x.getD 0)
  apply he.agrees.byte
  intro c hmem hcov
  rw [hc] at hmem
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl
  · exact hcov
  · obtain ⟨j, hj, hjx⟩ := hcov
    exact ha j hj i hi hjx.symm
  · exact hcov

theorem PushProgress.initial {s : RamState} (h : EntryStackPre copy s) :
    PushProgress copy s 0 s := by
  refine ⟨by cases copy <;> exact h.rip, ?_, fun _ _ ↦ rfl, ?_,
    memoryWriteFrame_refl _ _,
    fun _ hx ↦ hx, rfl, rfl⟩
  · simp only [pushSlot, Nat.mul_zero, BitVec.sub_zero]
    rfl
  · intro i hi
    omega

theorem PushProgress.pre {initial s : RamState} (hp : EntryStackPre copy initial)
    (i : Fin 6) (hs : PushProgress copy initial i.val s) :
    PushPreReadable (pushPC copy i.val) s := by
  have ha : pushAddr s = pushSlot initial (i.val + 1) := by
    change stackPtr s - 8 = _
    rw [hs.stack, pushSlot_succ]
  have hi8 : 8 ≤ 8 * (i.val + 1) := by omega
  have hi264 : 8 * (i.val + 1) ≤ frameBytes := by
    have := i.isLt
    change _ ≤ 264
    omega
  refine ⟨⟨⟨hs.rip, ?_⟩, ?_⟩, ?_⟩
  · rw [ha]
    have hr := hp.readable hi8 hi264
    exact ⟨hr.low, fun j hj ↦ hs.grow _ (hr.mem j hj)⟩
  · rw [ha]
    exact fun j hj ht ↦ hp.slot_avoid hi8 hi264 hj (.inr ht)
  · rw [ha]
    exact hp.page hi264 (by omega)

theorem EntryStackPre.slot_frame {initial : RamState} (hp : EntryStackPre copy initial)
    (i : Fin 6) {j : Nat} (hj : j < 8) :
    (⟨(frameBase initial).toNat, frameBytes⟩ : MemoryRegion).Contains
      (pushSlot initial (i.val + 1) + BitVec.ofNat 64 j).toNat := by
  have hi : 8 * (i.val + 1) ≤ frameBytes := by
    have := i.isLt
    change _ ≤ 264
    omega
  have hn := hp.stack.2.2.1
  change frameBytes ≤ (initial.regValue .rsp).toNat at hn
  have hsp := (initial.regValue .rsp).isLt
  have hb : (frameBase initial).toNat = (initial.regValue .rsp).toNat - frameBytes :=
    stack_sub_toNat hn (Nat.le_refl frameBytes)
  simp only [MemoryRegion.Contains, hb, pushSlot, BitVec.toNat_add,
    stack_sub_toNat hn hi, BitVec.toNat_ofNat]
  have := i.isLt
  omega

theorem PushProgress.step {initial s t : RamState} (hp : EntryStackPre copy initial)
    (i : Fin 6) (hs : PushProgress copy initial i.val s)
    (he : (pushR64Effect (pushPC copy i.val) (encodePushR64 (pushReg i)).length
      ((pushReg i).setWidth 5) s).Holds s t) :
    PushProgress copy initial (i.val + 1) t := by
  have ha : pushAddr s = pushSlot initial (i.val + 1) := by
    change stackPtr s - 8 = _
    rw [hs.stack, pushSlot_succ]
  have hc := pushR64Effect_components (pushPC copy i.val)
    (encodePushR64 (pushReg i)).length ((pushReg i).setWidth 5) s
  refine ⟨he.rip.trans (pushPC_next copy i), he.writes.1.trans ha, ?_, ?_, ?_,
    fun address hx ↦ he.agrees.grow address (hs.grow address hx),
    (he.agrees.scalarFrame_eq (by simp [Effect.components, x86_compose])).trans hs.rest, ?_⟩
  · intro r hr
    apply Eq.trans (he.agrees.read ?_) (hs.registers r hr)
    simp only [hc, List.mem_cons, List.not_mem_nil, Component.reg.injEq,
      reduceCtorEq, or_false]
    exact hr
  · intro j hj
    by_cases hji : j = i
    · subst j
      rw [← ha]
      exact he.writes.2.trans (hs.registers _ (pushReg_ne_rsp i))
    · have hjlt : j.val < i.val := by
        have hne : j.val ≠ i.val := fun h ↦ hji (Fin.ext h)
        omega
      apply Eq.trans (effect_read_mem_of_apart he hc ?_) (hs.saved j hjlt)
      rw [ha]
      exact pushSlot_apart initial (by omega) (by have := i.isLt; omega)
  · intro address hout
    apply Eq.trans (he.agrees.byte ?_) (hs.memory address hout)
    intro c hmem hcov
    rw [hc] at hmem
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
    rcases hmem with rfl | rfl | rfl
    · exact hcov
    · obtain ⟨j, hj, haddr⟩ := hcov
      rw [ha] at haddr
      exact hout ⟨(frameBase initial).toNat, frameBytes⟩ (by simp)
        (haddr ▸ hp.slot_frame i hj)
    · exact hcov
  · apply Eq.trans (effect_read_mem_of_apart he hc ?_) hs.returnSlot
    rw [ha]
    have h := pushSlot_apart initial (j := 0) (k := i.val + 1)
      (by omega) (by have := i.isLt; omega)
    simpa only [pushSlot, Nat.mul_zero, BitVec.ofNat_eq_ofNat, BitVec.sub_zero] using h

theorem pushes_advance (copy : Copy) [Bindings] (boundary : ReturnBoundary)
    (hboundary : ¬ InProgram boundary.rip) :
    AdvanceTriple boundary 6 (EntryStackPre copy) (codeRange (entryAddress copy) pushBytes)
      (fun s t ↦ PushProgress copy s 6 t) := by
  intro initial hready hcode hp
  have hbody (i : Nat) (hi : i < 6) :
      AdvanceTriple boundary 1 (PushProgress copy initial i)
        (codeRange (entryAddress copy) pushBytes)
        (fun _ t ↦ PushProgress copy initial (i + 1) t) := by
    intro s hr hc hs
    let j : Fin 6 := ⟨i, hi⟩
    have hpre := hs.pre hp j
    have hn : (pushR64Effect (pushPC copy i) (encodePushR64 (pushReg j)).length
        ((pushReg j).setWidth 5) s).rip ≠ boundary.rip := by
      change pushPC copy i + BitVec.ofNat 64 (encodePushR64 (pushReg j)).length ≠ boundary.rip
      rw [pushPC_next copy j]
      exact fun he ↦ hboundary (he ▸ pushPC_inProgram copy (i + 1) (by omega))
    obtain ⟨t, hrun, ht, he⟩ :=
      (push_r64_encoded_effect_step_of_readable (pushPC copy i) (pushReg j)).advances
        hr (hc.mono (push_step_code copy j)) hpre hn
    have ha : pushAddr s = pushSlot initial (i + 1) := by
      change stackPtr s - 8 = _
      rw [hs.stack, pushSlot_succ]
    have hav : (pushR64Effect (pushPC copy i) (encodePushR64 (pushReg j)).length
        ((pushReg j).setWidth 5) s).Avoids (codeRange (entryAddress copy) pushBytes) := by
      apply Effect.avoids_of_components_reg_mem_rip (pushR64Effect_components _ _ _ s)
      rw [ha]
      exact hp.apart (by omega) (by change _ ≤ 264; omega)
    exact ⟨t, hrun, ht, he.codeIn hav hc, hs.step hp j he⟩
  exact (AdvanceTriple.iterate 6 1 hbody) initial hready hcode (PushProgress.initial hp)


end Sha3.Proofs.Permutation
