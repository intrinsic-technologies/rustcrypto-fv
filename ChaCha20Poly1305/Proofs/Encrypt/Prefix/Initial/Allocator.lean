import ChaCha20Poly1305.Proofs.Wrapper
import ChaCha20Poly1305.Proofs.Encrypt.Prefix.Initial.Data
import X86Proofs.Instructions.Add.Generated.RM.Triple

namespace ChaCha20Poly1305.Proofs.Encrypt.Prefix

open ChaCha20Poly1305.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Wrapper MemoryRoutines.Machine

def allocatorChanges : List Component :=
  [.reg 0, .reg 8, .reg 12, .reg 13, .flags, .rip, .mem 0x300000 16]

theorem initialize_allocator [Bindings] {s : RamState} {boundary : ReturnBoundary}
    (outside : ¬ InProgram boundary.rip)
    (track : GTrack allocatorChanges s s)
    (entry : s.RIP = 0x10174e)
    (capacity : MemReadable s (stackPtr s + 192) 8)
    (length : MemReadable s (stackPtr s + 184) 8)
    (allocator : MemWritable s 0x300000 16)
    (away : ∀ a, (Component.mem 0x300000 16).Covers a → ¬ InProgram a)
    (sep : ∀ i < 16, ¬ (Component.mem 0x300000 16).Covers
      (stackPtr s + 184 + BitVec.ofNat 64 i)) :
    ∃ t, Advances boundary 7 s t ∧ GTrack allocatorChanges s t ∧
      t.RIP = 0x10177a ∧ rd t 12 = rd s 1 ∧
      rd t 13 = wd s (stackPtr s + 184) ∧
      wd t 0x300000 = rd s 8 ∧
      wd t 0x300008 =
        (let cap := wd s (stackPtr s + 192)
         if (rd s 8).toNat + cap.toNat < 2^64 then rd s 8 + cap
         else BitVec.allOnes 64) := by
  have cover (a : BitVec 64) (ha : a = 0x300000 ∨ a = 0x300008) :
      ∀ i < 8, (Component.mem 0x300000 16).Covers (a + BitVec.ofNat 64 i) := by
    intro i hi
    rcases ha with rfl | rfl
    · exact ⟨i, by omega, rfl⟩
    · refine ⟨8 + i, by omega, ?_⟩
      bv_omega
  have fitGlobal (a : BitVec 64) (ha : a = 0x300000 ∨ a = 0x300008) :
      Fits allocatorChanges [.mem a 8, .rip] := by
    intro c hc
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl
    · right
      refine ⟨rfl, ?_⟩
      intro x hx
      obtain ⟨i, hi, rfl⟩ := hx
      have h := cover a ha i hi
      exact ⟨⟨.mem 0x300000 16, by simp [allocatorChanges], h⟩, away _ h⟩
    · exact .inl ⟨rfl, by simp [allocatorChanges]⟩
  have writable {u : RamState} (T : GTrack allocatorChanges s u)
      (a : BitVec 64) (ha : a = 0x300000 ∨ a = 0x300008) : MemWritable u a 8 := by
    rcases ha with rfl | rfl
    · refine ⟨by decide, fun i hi => T.agrees.grow _ (allocator.mem i (by omega)),
        by decide +kernel⟩
    · refine ⟨by decide, ?_, by decide +kernel⟩
      intro i hi
      apply T.agrees.grow
      rw [show (0x300008 : BitVec 64) + BitVec.ofNat 64 i =
        0x300000 + BitVec.ofNat 64 (8 + i) from by bv_omega]
      exact allocator.mem _ (by omega)
  have apart (a : BitVec 64) (ha : a = 0x300000 ∨ a = 0x300008)
      (p : BitVec 64) (n : Nat) (hp : ∀ j < n, InProgram (p + BitVec.ofNat 64 j)) :
      RangeApart a 8 p n := by
    intro i hi j hj he
    exact away _ (cover a ha i hi) (he ▸ hp j hj)
  have spkeep {u : RamState} (T : GTrack allocatorChanges s u) : stackPtr u = stackPtr s :=
    sp_keep T.agrees (by simp [allocatorChanges]) rfl
  have stackload {u : RamState} (T : GTrack allocatorChanges s u)
      (d : Nat) (hd : d = 184 ∨ d = 192) :
      wd u (stackPtr s + BitVec.ofNat 64 d) =
        wd s (stackPtr s + BitVec.ofNat 64 d) := by
    apply gload T.agrees
    intro c hc i hi
    simp only [allocatorChanges, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact nonmem_not_covers rfl _
      | (rcases hd with rfl | rfl
         · exact sep i (by omega)
         · have he : stackPtr s + BitVec.ofNat 64 192 + BitVec.ofNat 64 i =
               stackPtr s + 184 + BitVec.ofNat 64 (8 + i) := by bv_omega
           rw [he]
           exact sep _ (by omega))
  obtain ⟨s1, a1, T1, e1⟩ := gtrack_step
    (mov_r64_r64_effect_step 0x10174e 0x49 0xcc
      (by unfold RexWPrefix; decide) (by decide))
    track (program_text_slice track.code 0x174e 3 (by decide +kernel)) entry
    (code_ne_boundary outside 0x1751 (by omega)) (by fits [allocatorChanges])
  change (movR64R64Effect 0x10174e 12 1 s).Holds s s1 at e1
  have A2 (u : RamState) :
      (AddrMode.rip 0x1fe8a8).addr u (0x101751 + BitVec.ofNat 64 7) = 0x300000 := rfl
  obtain ⟨s2, a2, T2, e2⟩ := gtrack_step
    (mov_m64_r64_effect_step 0x101751 0x4c (by unfold RexWPrefix; decide) 0
      (.rip 0x1fe8a8) (by decide) (by decide) (by decide))
    T1 (program_text_slice T1.code 0x1751 7 (by decide +kernel))
    ⟨e1.rip, writable T1 0x300000 (.inl rfl),
      apart 0x300000 (.inl rfl) _ _ (code_inProgram 0x1751 7 (by omega))⟩
    (code_ne_boundary outside 0x1758 (by omega))
    (by simp only [movM64R64Effect_components, storeAddrAt]
        exact fitGlobal 0x300000 (.inl rfl))
  change (movM64R64Effect 0x101751 8 (.rip 0x1fe8a8) s1).Holds s1 s2 at e2
  have M2 : wd s2 0x300000 = rd s 8 :=
    e2.writes.trans (e1.agrees.read (r := 8) (by simp))
  have A3 (x : BitVec 64) : (AddrMode.sib 4 none 0 (.d32 192)).addr s2 x =
      stackPtr s + 192 := by
    change rd s2 4 + 192 = stackPtr s + 192
    exact congrArg (fun p : BitVec 64 => p + 192) (spkeep T2)
  obtain ⟨s3, a3, T3, e3⟩ := gtrack_step
    (add_r64_m64_effect_step 0x101758 0x4c (by unfold RexWPrefix; decide) 0
      (.sib 4 none 0 (.d32 192)) (by decide) (by decide) (by decide))
    T2 (program_text_slice T2.code 0x1758 8 (by decide +kernel))
    ⟨e2.rip, by rw [A3]; exact ⟨capacity.low, fun i hi =>
      T2.agrees.grow _ (capacity.mem i hi)⟩⟩
    (code_ne_boundary outside 0x1760 (by omega))
    (by fits [addR64M64Effect_components, allocatorChanges])
  change (addR64M64Effect 0x101758 8 (.sib 4 none 0 (.d32 192)) s2).Holds s2 s3 at e3
  have R2 : rd s2 8 = rd s 8 :=
    (e2.agrees.read (r := 8) (by simp)).trans (e1.agrees.read (r := 8) (by simp))
  have C2 : wd s2 ((AddrMode.sib 4 none 0 (.d32 192)).addr s2
      (0x101758 + BitVec.ofNat 64 8)) = wd s (stackPtr s + 192) := by
    rw [A3]
    exact stackload T2 192 (.inr rfl)
  have R3 : rd s3 8 = rd s 8 + wd s (stackPtr s + 192) := by
    have h : rd s3 8 = rd s2 8 + wd s2
        ((AddrMode.sib 4 none 0 (.d32 192)).addr s2 (0x101758 + BitVec.ofNat 64 8)) :=
      e3.writes
    rw [h, R2, C2]
  have CF3 : (!(StatusFlags.ofRFLAGS s3.RFLAGS).CF) =
      decide ((rd s 8).toNat + (wd s (stackPtr s + 192)).toNat < 2^64) := by
    have h := e3.flags.1
    change (StatusFlags.ofRFLAGS s3.RFLAGS).CF = (addSpec (rd s2 8)
      (wd s2 ((AddrMode.sib 4 none 0 (.d32 192)).addr s2
        (0x101758 + BitVec.ofNat 64 8)))).2.CF at h
    rw [h, R2, C2]
    exact add_no_carry _ _
  obtain ⟨s4, a4, T4, e4⟩ := gtrack_step
    (mov_r64_imm32_effect_step 0x101760 0x48 0xc0
      (by unfold RexWPrefix; decide) (by decide) (by decide) 0xffffffff)
    T3 (program_text_slice T3.code 0x1760 7 (by decide +kernel)) e3.rip
    (code_ne_boundary outside 0x1767 (by omega))
    (by fits [movR64Imm32Effect_components, allocatorChanges])
  change (movR64Imm32Effect 0x101760 0 0xffffffff s3).Holds s3 s4 at e4
  have cond : condHolds 3 (StatusFlags.ofRFLAGS s4.RFLAGS) =
      decide ((rd s 8).toNat + (wd s (stackPtr s + 192)).toNat < 2^64) := by
    rw [flags_keep e4.agrees (by simp), condHolds_3]
    exact CF3
  obtain ⟨s5, a5, T5, e5⟩ := gtrack_step
    (cmov_r64_r64_effect_step 0x101767 3 0x49 (by unfold RexWPrefix; decide)
      0xc0 (by decide) _)
    T4 (program_text_slice T4.code 0x1767 4 (by decide +kernel)) ⟨e4.rip, cond⟩
    (code_ne_boundary outside 0x176b (by omega))
    (by fits [cmovR64R64Effect_components, allocatorChanges])
  change (cmovR64R64Effect 0x101767 4 0 8
    (decide ((rd s 8).toNat + (wd s (stackPtr s + 192)).toNat < 2^64)) s4).Holds s4 s5 at e5
  have R5 : rd s5 0 = if (rd s 8).toNat + (wd s (stackPtr s + 192)).toNat < 2^64
      then rd s 8 + wd s (stackPtr s + 192) else BitVec.allOnes 64 := by
    have h : rd s5 0 = if decide ((rd s 8).toNat +
        (wd s (stackPtr s + 192)).toNat < 2^64) then rd s4 8 else rd s4 0 := e5.writes
    have h8 : rd s4 8 = rd s 8 + wd s (stackPtr s + 192) :=
      (e4.agrees.read (r := 8) (by simp)).trans R3
    have h0 : rd s4 0 = BitVec.allOnes 64 := e4.writes
    simpa only [decide_eq_true_eq, h8, h0] using h
  have A6 (x : BitVec 64) : (AddrMode.sib 4 none 0 (.d32 184)).addr s5 x =
      stackPtr s + 184 := by
    change rd s5 4 + 184 = stackPtr s + 184
    exact congrArg (fun p : BitVec 64 => p + 184) (spkeep T5)
  obtain ⟨s6, a6, T6, e6⟩ := gtrack_step
    (mov_r64_m64_effect_step 0x10176b 0x4c (by unfold RexWPrefix; decide) 5
      (.sib 4 none 0 (.d32 184)) (by decide) (by decide) (by decide))
    T5 (program_text_slice T5.code 0x176b 8 (by decide +kernel))
    ⟨e5.rip, by rw [A6]; exact ⟨length.low, fun i hi => T5.agrees.grow _ (length.mem i hi)⟩⟩
    (code_ne_boundary outside 0x1773 (by omega)) (by fits [allocatorChanges])
  change (movR64M64Effect 0x10176b 13 (.sib 4 none 0 (.d32 184)) s5).Holds s5 s6 at e6
  have R6 : rd s6 13 = wd s (stackPtr s + 184) := by
    have h : rd s6 13 = wd s5 ((AddrMode.sib 4 none 0 (.d32 184)).addr s5
      (0x10176b + BitVec.ofNat 64 8)) := e6.writes
    rw [h, A6]
    exact stackload T5 184 (.inl rfl)
  have A7 (u : RamState) :
      (AddrMode.rip 0x1fe88e).addr u (0x101773 + BitVec.ofNat 64 7) = 0x300008 := rfl
  obtain ⟨s7, a7, T7, e7⟩ := gtrack_step
    (mov_m64_r64_effect_step 0x101773 0x48 (by unfold RexWPrefix; decide) 0
      (.rip 0x1fe88e) (by decide) (by decide) (by decide))
    T6 (program_text_slice T6.code 0x1773 7 (by decide +kernel))
    ⟨e6.rip, writable T6 0x300008 (.inr rfl),
      apart 0x300008 (.inr rfl) _ _ (code_inProgram 0x1773 7 (by omega))⟩
    (code_ne_boundary outside 0x177a (by omega))
    (by simp only [movM64R64Effect_components, storeAddrAt]
        exact fitGlobal 0x300008 (.inr rfl))
  change (movM64R64Effect 0x101773 0 (.rip 0x1fe88e) s6).Holds s6 s7 at e7
  have M7 : wd s7 0x300008 = rd s6 0 := e7.writes
  refine ⟨s7, a1.trans (a2.trans (a3.trans (a4.trans (a5.trans (a6.trans a7))))),
    T7, e7.rip, ?_, ?_, ?_, ?_⟩
  · exact (((((e2.agrees.trans e3.agrees).trans e4.agrees).trans e5.agrees).trans
      e6.agrees).trans e7.agrees).read (r := 12) (by simp) |>.trans e1.writes
  · exact (e7.agrees.read (r := 13) (by simp)).trans R6
  · have keep7 : wd s7 0x300000 = wd s6 0x300000 := by
      apply gload e7.agrees
      intro c hc i hi
      simp only [movM64R64Effect_components, storeAddrAt] at hc
      change c ∈ [.mem 0x300008 8, .rip] at hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl
      · apply mem_not_covers <;>
          simp only [BitVec.toNat_add, BitVec.toNat_ofNat,
            show (0x300000 : BitVec 64).toNat = 0x300000 from rfl,
            show (0x300008 : BitVec 64).toNat = 0x300008 from rfl] <;> omega
      · exact nonmem_not_covers rfl _
    exact keep7.trans ((mem_keep e6.agrees (by simp [Component.isMem]) _).trans
      ((mem_keep e5.agrees (by simp [Component.isMem]) _).trans
      ((mem_keep e4.agrees (by simp [Component.isMem]) _).trans
      ((mem_keep e3.agrees (by simp [addR64M64Effect_components, Component.isMem]) _).trans M2))))
  · exact M7.trans ((e6.agrees.read (r := 0) (by simp)).trans R5)


end ChaCha20Poly1305.Proofs.Encrypt.Prefix
