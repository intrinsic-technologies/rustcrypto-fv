import P256.Proofs.HMAC.Pad.Memory

set_option autoImplicit false

namespace P256.Proofs.HMAC.Pad

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs
open P256.Proofs.Program

def xorPrefix (f : Nat → UInt8) (mask : UInt8) (count i : Nat) : UInt8 :=
  if i < count then f i ^^^ mask else f i

structure Position (loop : Loop) (s : RamState) (n i : Nat) (f : Nat → UInt8) : Prop
    extends Memory loop s where
  rip : s.RIP = loop.address i
  counter : s.regValue .rax = BitVec.ofNat 64 (4 * n + 3)
  bytes : Bytes s.external (buffer loop s) 64 (xorPrefix f loop.mask (4 * n + i))

theorem xorPrefix_write {s t : RamState} {a : BitVec 64} {f : Nat → UInt8} {mask : UInt8}
    {k : Nat} (hk : k < 64)
    (bytes : Bytes s.external a 64 (xorPrefix f mask k))
    (agrees : AgreesExcept [.mem (a + BitVec.ofNat 64 k) 1, .flags, .rip] s t)
    (written : t.external[a + BitVec.ofNat 64 k]? = some (f k ^^^ mask)) :
    Bytes t.external a 64 (xorPrefix f mask (k + 1)) := by
  intro i hi
  by_cases eq : i = k
  · subst i
    simpa only [xorPrefix, Nat.lt_succ_self, reduceIte] using written
  · rw [agrees.byte]
    · rw [bytes i hi]
      congr 1
      unfold xorPrefix
      have he : (i < k + 1) = (i < k) := propext (by omega)
      simp only [he]
    · intro c hc covered
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl | rfl
      · obtain ⟨j, hj, haddr⟩ := covered
        have hj0 : j = 0 := by omega
        subst j
        simp only [BitVec.add_zero] at haddr
        have h := congrArg BitVec.toNat ((BitVec.add_right_inj a).mp haddr)
        simp only [BitVec.toNat_ofNat] at h
        rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h
        omega
      · exact covered.elim
      · exact covered.elim

theorem xor_step [Bindings] {loop : Loop} {s : RamState} {boundary : ReturnBoundary}
    {n i : Nat} {f : Nat → UInt8} (ready : ReadyToStep s) (loaded : ProgramLoaded s)
    (outside : ¬ InProgram boundary.rip) (state : Position loop s n i f)
    (hn : n < 16) (hi : i < 4) :
    ∃ t, Advances boundary 1 s t ∧ ReadyToStep t ∧ ProgramLoaded t ∧
      Position loop t n (i + 1) f ∧ AgreesExcept (footprint loop s) s t := by
  have index : 4 * n + i < 64 := by omega
  have addr := mode_address loop i n hi state.counter
  have length : loop.position i + (3 + (loop.mode i).tail.length) ≤ loop.length := by
    rw [xor_length loop i hi]
    exact position_le loop (i + 1) (by omega)
  obtain ⟨t, run, readyT, effect⟩ :=
    (xor_m8_imm8_effect_step (loop.address i) (loop.mode i) (mode_valid loop i)
      (mode_rexX loop i) (mode_rexB loop i) loop.mask).advances ready
      (xor_code loaded loop i hi)
      ⟨state.rip, by rw [addr]; exact state.toMemory.byte_writable _ index,
        by rw [addr]; exact state.toMemory.byte_code _ _ _ index length⟩
      (by change loop.address i + BitVec.ofNat 64 (3 + (loop.mode i).tail.length) ≠ _
          rw [xor_next loop i hi]
          exact boundary_ne_program outside (address_inProgram loop _ (position_le loop _ (by omega))))
  have single : AgreesExcept
      [.mem (buffer loop s + BitVec.ofNat 64 (4 * n + i)) 1, .flags, .rip] s t := by
    have h := effect.agrees
    rw [xorM8Imm8Effect_components, addr] at h
    exact h
  have agrees := byte_agrees index single
  have written : t.external[buffer loop s + BitVec.ofNat 64 (4 * n + i)]? =
      some (f (4 * n + i) ^^^ loop.mask) := by
    have word := effect.writes
    change memLoad t.external ((loop.mode i).addr s _) 8 =
      memLoad s.external ((loop.mode i).addr s _) 8 ^^^ loop.mask.toBitVec at word
    rw [addr, state.bytes.loadByte _ index] at word
    simp only [xorPrefix, Nat.lt_irrefl, reduceIte] at word
    have bs := Bytes.of_memLoad (n := 8) (fun j hj => single.grow _
      ((state.toMemory.byte_writable _ index).mem j hj))
    rw [word] at bs
    simpa [storedByte, BitVec.extractLsb', BitVec.setWidth_eq] using bs 0 (by decide)
  have out := xorPrefix_write index state.bytes single written
  refine ⟨t, run, readyT, state.toMemory.loaded_after loaded agrees, ?_, agrees⟩
  refine ⟨state.toMemory.after agrees, effect.rip.trans (xor_next loop i hi), ?_, ?_⟩
  · exact (single.read (n := 64) (r := 0) (by simp)).trans state.counter
  · rw [buffer_of_agrees agrees]
    simpa only [Nat.add_assoc] using out

end P256.Proofs.HMAC.Pad
