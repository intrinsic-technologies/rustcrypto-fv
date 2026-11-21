import P256.Proofs.Signing.Wrapper.Entry.Decode.Copy.Run

set_option autoImplicit false

namespace P256.Proofs.Signing.Wrapper.Entry.Decode.Copy

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem frame {s t : RamState} (h : (effect s).Holds s t) :
    AgreesExcept (copyComponents s) s t := by
  apply h.agrees.widen
  · intro c hc hm
    simp only [effect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
    all_goals try simp [copyComponents]
    all_goals simp [Component.isMem] at hm
  · intro a c hc ha
    simp only [effect, Effect.components, List.map_cons, List.map_nil,
      Write.component, Operand.component, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | rfl
    all_goals try exact ha.elim
    all_goals
      obtain ⟨i, hi, rfl⟩ := ha
      refine ⟨.mem (stackPtr s + 336) 32, by simp [copyComponents], ?_⟩
    · exact ⟨2+i, by omega, by rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl⟩
    · exact ⟨i, by omega, by simp [stackPtr, Operand.read_reg64, gprIndex]⟩
    · exact ⟨7+i, by omega, by rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl⟩
    · exact ⟨15+i, by omega, by rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl⟩
    · exact ⟨23+i, by omega, by rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl⟩
    · exact ⟨31+i, by omega, by rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl⟩
    · exact ⟨3+i, by omega, by rw [BitVec.ofNat_add, BitVec.add_assoc]; rfl⟩

theorem chunk_bytes {s t : RamState} {input : ByteArray}
    {sourceRegister : Syntax.Reg} {entry : BitVec 64}
    (pre : CopyPre input s sourceRegister entry)
    (grow : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome)
    (off n : Nat) (hlen : off + n/8 ≤ 32)
    (he : memLoad t.external ((stackPtr s + 336) + BitVec.ofNat 64 off) n =
      memLoad s.external (s.regValue sourceRegister + BitVec.ofNat 64 off) n) :
    ∀ i < n/8,
      t.external[(stackPtr s + 336) + BitVec.ofNat 64 (off+i)]? =
      s.external[s.regValue sourceRegister + BitVec.ofNat 64 (off+i)]? := by
  have hs := Bytes.of_memLoad (pre.readable off (n/8) hlen).mem
  have ht := Bytes.of_memLoad (a := (stackPtr s + 336) + BitVec.ofNat 64 off) (n := n) (fun i hi => grow _
    (by
    simpa only [BitVec.ofNat_add, BitVec.add_assoc] using pre.writable.mem (off+i) (by omega)))
  intro i hi
  have a := ht i hi
  have b := hs i hi
  rw [he] at a
  simpa only [BitVec.ofNat_add, BitVec.add_assoc] using a.trans b.symm

theorem chunks_hasBytes {s t : RamState} {input : ByteArray}
    {sourceRegister : Syntax.Reg} {entry : BitVec 64}
    (pre : CopyPre input s sourceRegister entry)
    (grow : ∀ a : BitVec 64, (s.external[a]?).isSome → (t.external[a]?).isSome)
    (h2 : memLoad t.external ((stackPtr s + 336) + 2) 8 =
      memLoad s.external (s.regValue sourceRegister + 2) 8)
    (h0 : memLoad t.external ((stackPtr s + 336) + 0) 16 =
      memLoad s.external (s.regValue sourceRegister + 0) 16)
    (h7 : memLoad t.external ((stackPtr s + 336) + 7) 64 =
      memLoad s.external (s.regValue sourceRegister + 7) 64)
    (h15 : memLoad t.external ((stackPtr s + 336) + 15) 64 =
      memLoad s.external (s.regValue sourceRegister + 15) 64)
    (h23 : memLoad t.external ((stackPtr s + 336) + 23) 64 =
      memLoad s.external (s.regValue sourceRegister + 23) 64)
    (h31 : memLoad t.external ((stackPtr s + 336) + 31) 8 =
      memLoad s.external (s.regValue sourceRegister + 31) 8)
    (h3 : memLoad t.external ((stackPtr s + 336) + 3) 32 =
      memLoad s.external (s.regValue sourceRegister + 3) 32) :
    (MemoryRegion.mk (stackPtr s + 336).toNat 32).HasBytes t.external input := by
  have hc2 := chunk_bytes pre grow 2 8 (by decide) h2
  have hc0 := chunk_bytes pre grow 0 16 (by decide) h0
  have hc7 := chunk_bytes pre grow 7 64 (by decide) h7
  have hc15 := chunk_bytes pre grow 15 64 (by decide) h15
  have hc23 := chunk_bytes pre grow 23 64 (by decide) h23
  have hc31 := chunk_bytes pre grow 31 8 (by decide) h31
  have hc3 := chunk_bytes pre grow 3 32 (by decide) h3
  refine ⟨pre.sourceBytes.1, ?_⟩
  intro i
  have hi : i.val < 32 := by
    have hsize : input.size = 32 := pre.sourceBytes.1
    omega
  have he : t.external[(stackPtr s + 336) + BitVec.ofNat 64 i.val]? =
      s.external[s.regValue sourceRegister + BitVec.ofNat 64 i.val]? := by
    by_cases a : i.val < 2
    · simpa only [Nat.zero_add] using hc0 i.val a
    by_cases b : i.val = 2
    · simpa only [b] using hc2 0 (by decide)
    by_cases c : i.val < 7
    · simpa only [Nat.add_sub_of_le (show 3 ≤ i.val by omega)] using
        hc3 (i.val-3) (by omega)
    by_cases d : i.val < 15
    · simpa only [Nat.add_sub_of_le (show 7 ≤ i.val by omega)] using
        hc7 (i.val-7) (by omega)
    by_cases e : i.val < 23
    · simpa only [Nat.add_sub_of_le (show 15 ≤ i.val by omega)] using
        hc15 (i.val-15) (by omega)
    by_cases f : i.val < 31
    · simpa only [Nat.add_sub_of_le (show 23 ≤ i.val by omega)] using
        hc23 (i.val-23) (by omega)
    have hi31 : i.val = 31 := by omega
    simpa only [hi31] using hc31 0 (by decide)
  have hs := pre.sourceBytes.2 i
  change t.external[BitVec.ofNat 64 ((stackPtr s + 336).toNat + i.val)]? = _
  change s.external[BitVec.ofNat 64 ((s.regValue sourceRegister).toNat + i.val)]? = _ at hs
  simp only [BitVec.ofNat_add, BitVec.ofNat_toNat, BitVec.setWidth_eq] at hs ⊢
  exact he.trans hs

theorem hasBytes {s t : RamState} {input : ByteArray} (pre : CopyPre input s)
    (h : (effect s).Holds s t) :
    (MemoryRegion.mk (stackPtr s + 336).toNat 32).HasBytes t.external input := by
  have hw := h.writes
  change _ ∧ _ ∧ _ ∧
    memLoad t.external ((stackPtr s + 336) + 2) 8 = memLoad s.external (s.regValue .rax + 2) 8 ∧
    memLoad t.external ((stackPtr s + 336) + 0) 16 = memLoad s.external (s.regValue .rax + 0) 16 ∧
    memLoad t.external ((stackPtr s + 336) + 7) 64 = memLoad s.external (s.regValue .rax + 7) 64 ∧
    memLoad t.external ((stackPtr s + 336) + 15) 64 = memLoad s.external (s.regValue .rax + 15) 64 ∧
    memLoad t.external ((stackPtr s + 336) + 23) 64 = memLoad s.external (s.regValue .rax + 23) 64 ∧
    memLoad t.external ((stackPtr s + 336) + 31) 8 = memLoad s.external (s.regValue .rax + 31) 8 ∧
    memLoad t.external ((stackPtr s + 336) + 3) 32 = memLoad s.external (s.regValue .rax + 3) 32 at hw
  obtain ⟨_, _, _, h2, h0, h7, h15, h23, h31, h3⟩ := hw
  exact chunks_hasBytes pre (frame h).grow h2 h0 h7 h15 h23 h31 h3

end P256.Proofs.Signing.Wrapper.Entry.Decode.Copy
