import Sha1.Proofs.Buffered.Finalize.Digest.BlockCopy.Properties

namespace Sha1.Proofs.Buffered.Finalize.Digest.BlockCopy

open Sha1.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
open Sha1.Proofs.Compress.Machine

theorem stack_byte_some {s : RamState} (hs : Storage .digestCopy s) (j : Nat) (hj : j < 280) :
    (s.external[stackPtr s + BitVec.ofNat 64 j]?).isSome := by
  have := (hs.stackWritable j 1 (by simp only [Kind.stackBytes]; omega)).mem 0 (by decide)
  rwa [BitVec.add_zero] at this

theorem word_bytes {s t : RamState} (hs : Storage .digestCopy s) (ht : Storage .digestCopy t)
    (hsp : stackPtr t = stackPtr s) (d src : Nat) (hd : d + 8 ≤ 280) (hsrc : src + 8 ≤ 280)
    (h : (Operand.mem (stackPtr s + BitVec.ofNat 64 d) : Operand 64).read t =
      (Operand.mem (stackPtr s + BitVec.ofNat 64 src) : Operand 64).read s) :
    ∀ k < 8, t.external[stackPtr s + BitVec.ofNat 64 (d + k)]? =
      s.external[stackPtr s + BitVec.ofNat 64 (src + k)]? := by
  intro k hk
  have hs3 (a j : Nat) : stackPtr s + BitVec.ofNat 64 a + BitVec.ofNat 64 j =
      stackPtr s + BitVec.ofNat 64 (a + j) := by
    rw [BitVec.add_assoc, ← BitVec.ofNat_add]
  have ha : ∀ i < 64 / 8, (t.external[stackPtr s + BitVec.ofNat 64 d + BitVec.ofNat 64 i]?).isSome := by
    intro i hi
    rw [hs3, ← hsp]
    exact stack_byte_some ht (d + i) (by omega)
  have hb : ∀ i < 64 / 8, (s.external[stackPtr s + BitVec.ofNat 64 src + BitVec.ofNat 64 i]?).isSome := by
    intro i hi
    rw [hs3]
    exact stack_byte_some hs (src + i) (by omega)
  have key := Digest.bytes_eq_of_read_eq (n := 64) ha hb h k hk
  rwa [hs3, hs3] at key

theorem cover_shift {base x : BitVec 64} {d len off total : Nat}
    (h : Component.Covers (.mem (base + BitVec.ofNat 64 d) len) x) (hle : off ≤ d)
    (hend : d + len ≤ off + total) :
    Component.Covers (.mem (base + BitVec.ofNat 64 off) total) x := by
  obtain ⟨j, hj, rfl⟩ := h
  refine ⟨d - off + j, by omega, ?_⟩
  rw [BitVec.add_assoc, BitVec.add_assoc, ← BitVec.ofNat_add, ← BitVec.ofNat_add,
    show d + j = off + (d - off + j) by omega]

theorem arguments_run [Bindings] {boundary : ReturnBoundary} {s : RamState} {p : BitVec 64}
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s)
    (hout : ¬ InProgram boundary.rip) (hp : p = 0x1001a1 ∨ p = 0x100265) (hip : s.RIP = p) :
    ∃ fuel t, Advances boundary fuel s t ∧ ReadyToStep t ∧
      CodeIn Extracted.programImage t ∧ (argumentEffect p s).Holds s t := by
  rcases hp with rfl | rfl
  · have hb : CodeIn (codeRange 0x1001a1 argumentBytes) s :=
      program_text_slice hc 0x1a1 13 (by decide +kernel)
    obtain ⟨n, t, ha, ht, _, he⟩ := longArguments_execution boundary hout s hr hb hip
    exact ⟨n, t, ha, ht, he.codeIn (Effect.Avoids.of_noMem (by
      simp [argumentEffect, Effect.components, Component.Covers]) _) hc, he⟩
  · have hb : CodeIn (codeRange 0x100265 argumentBytes) s :=
      program_text_slice hc 0x265 13 (by decide +kernel)
    obtain ⟨n, t, ha, ht, _, he⟩ := finalArguments_execution boundary hout s hr hb hip
    exact ⟨n, t, ha, ht, he.codeIn (Effect.Avoids.of_noMem (by
      simp [argumentEffect, Effect.components, Component.Covers]) _) hc, he⟩

structure LongCopied [Bindings] (boundary : ReturnBoundary) (s t : RamState) : Prop where
  advances : ∃ fuel, Advances boundary fuel s t
  ready : ReadyToStep t
  code : CodeIn Extracted.programImage t
  rip : t.RIP = 0x1001ae
  rsp : stackPtr t = stackPtr s
  rdi : (Operand.reg 7 : Operand 64).read t = stackPtr s
  rsi : (Operand.reg 6 : Operand 64).read t = stackPtr s + 120
  rdx : (Operand.reg 2 : Operand 64).read t = 1
  copy : ∀ i < 64, t.external[stackPtr s + BitVec.ofNat 64 (120 + i)]? =
    s.external[stackPtr s + BitVec.ofNat 64 (24 + i)]?
  agrees : AgreesExcept [.reg 0, .reg 1, .reg 2, .reg 6, .reg 7, .rip,
    .mem (stackPtr s + 120) 64] s t

set_option maxHeartbeats 1000000 in
theorem long_copy [Bindings] {boundary : ReturnBoundary} {s : RamState}
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s)
    (hout : ¬ InProgram boundary.rip) (h : PartPre 0x10013c s) :
    ∃ t, LongCopied boundary s t := by
  obtain ⟨n1, u1, h1, hr1, hc1, hA⟩ := longA_run hr hc hout h
  have hsp1 := longA_rsp hA
  have hs1 := h.toStorage.of_agrees hA.agrees hsp1
  obtain ⟨n2, u2, h2, hr2, hc2, hB⟩ := longB_run hr1 hc1 hout ⟨hs1, hA.rip⟩
  have hsp2 := longB_rsp hB
  have hs2 := hs1.of_agrees hB.agrees hsp2
  obtain ⟨n3, t, h3, hr3, hc3, hC⟩ := arguments_run hr2 hc2 hout (.inl rfl) hB.rip
  have hext : t.external = u2.external := hC.agrees.external (by
    simp [argumentEffect, Effect.components, Component.Covers])
  have hwA := hA.writes
  simp only [longAEffect, Write.AllHold] at hwA
  have hwB := hB.writes
  simp only [longBEffect, Write.AllHold] at hwB
  have hwC := hC.writes
  simp only [argumentEffect, Write.AllHold] at hwC
  have hsp3 : stackPtr t = stackPtr u2 := hC.agrees.read (n := 64) (r := 4) (by
    simp [argumentEffect, Effect.components])
  have hcopy : ∀ i < 64, t.external[stackPtr s + BitVec.ofNat 64 (120 + i)]? =
      s.external[stackPtr s + BitVec.ofNat 64 (24 + i)]? := by
    intro i hi
    rcases (show i < 8 ∨ (8 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 24) ∨ (24 ≤ i ∧ i < 32) ∨ (32 ≤ i ∧ i < 40) ∨ (40 ≤ i ∧ i < 48) ∨ (48 ≤ i ∧ i < 56) ∨ (56 ≤ i ∧ i < 64) by omega) with hw | hw | hw | hw | hw | hw | hw | hw
    · have hk : i - 0 < 8 := by omega
      have e1 := word_bytes hs1 hs2 hsp2 120 24 (by decide) (by decide) hwB.2.2.2.2.2 (i - 0) hk
      rw [hsp1, show 120 + (i - 0) = 120 + i by omega, show 24 + (i - 0) = 24 + i by omega] at e1
      rw [hext, e1]
      have e2 := longA_byte hA (24 + i) (by omega) (by omega)
      exact e2
    · have hk : i - 8 < 8 := by omega
      have e1 := word_bytes hs1 hs2 hsp2 128 32 (by decide) (by decide) hwB.2.2.2.2.1 (i - 8) hk
      rw [hsp1, show 128 + (i - 8) = 120 + i by omega, show 32 + (i - 8) = 24 + i by omega] at e1
      rw [hext, e1]
      have e2 := longA_byte hA (24 + i) (by omega) (by omega)
      exact e2
    · have hk : i - 16 < 8 := by omega
      have e1 := word_bytes hs1 hs2 hsp2 136 40 (by decide) (by decide) hwB.2.2.2.1 (i - 16) hk
      rw [hsp1, show 136 + (i - 16) = 120 + i by omega, show 40 + (i - 16) = 24 + i by omega] at e1
      rw [hext, e1]
      have e2 := longA_byte hA (24 + i) (by omega) (by omega)
      exact e2
    · have hk : i - 24 < 8 := by omega
      have e1 := word_bytes hs1 hs2 hsp2 144 48 (by decide) (by decide) hwB.2.2.1 (i - 24) hk
      rw [hsp1, show 144 + (i - 24) = 120 + i by omega, show 48 + (i - 24) = 24 + i by omega] at e1
      rw [hext, e1]
      have e2 := longA_byte hA (24 + i) (by omega) (by omega)
      exact e2
    · have hk : i - 32 < 8 := by omega
      have e1 := word_bytes h.toStorage hs1 hsp1 152 56 (by decide) (by decide) hwA.2.2.2.2 (i - 32) hk
      rw [show 152 + (i - 32) = 120 + i by omega, show 56 + (i - 32) = 24 + i by omega] at e1
      rw [hext]
      have e2 := longB_byte hB (120 + i) (by omega) (by omega)
      rw [hsp1] at e2
      rw [e2, e1]
    · have hk : i - 40 < 8 := by omega
      have e1 := word_bytes h.toStorage hs1 hsp1 160 64 (by decide) (by decide) hwA.2.2.2.1 (i - 40) hk
      rw [show 160 + (i - 40) = 120 + i by omega, show 64 + (i - 40) = 24 + i by omega] at e1
      rw [hext]
      have e2 := longB_byte hB (120 + i) (by omega) (by omega)
      rw [hsp1] at e2
      rw [e2, e1]
    · have hk : i - 48 < 8 := by omega
      have e1 := word_bytes h.toStorage hs1 hsp1 168 72 (by decide) (by decide) hwA.2.2.1 (i - 48) hk
      rw [show 168 + (i - 48) = 120 + i by omega, show 72 + (i - 48) = 24 + i by omega] at e1
      rw [hext]
      have e2 := longB_byte hB (120 + i) (by omega) (by omega)
      rw [hsp1] at e2
      rw [e2, e1]
    · have hk : i - 56 < 8 := by omega
      have e1 := word_bytes h.toStorage hs1 hsp1 176 80 (by decide) (by decide) hwA.2.1 (i - 56) hk
      rw [show 176 + (i - 56) = 120 + i by omega, show 80 + (i - 56) = 24 + i by omega] at e1
      rw [hext]
      have e2 := longB_byte hB (120 + i) (by omega) (by omega)
      rw [hsp1] at e2
      rw [e2, e1]
  have hag : AgreesExcept [.reg 0, .reg 1, .reg 2, .reg 6, .reg 7, .rip,
      .mem (stackPtr s + 120) 64] s t := by
    have hA' : AgreesExcept [.reg 0, .reg 1, .reg 2, .reg 6, .reg 7, .rip,
        .mem (stackPtr s + 120) 64] s u1 := by
      apply hA.agrees.widen
      · intro c hc hm
        simp only [longAEffect, Effect.components, List.map_cons, List.map_nil,
          List.cons_append, List.nil_append, Write.component, Operand.component,
          List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
        all_goals simp_all [Component.isMem]
      · intro x c hc hcov
        refine ⟨.mem (stackPtr s + 120) 64, by simp, ?_⟩
        simp only [longAEffect, Effect.components, List.map_cons, List.map_nil,
          List.cons_append, List.nil_append, Write.component, Operand.component,
          List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
        all_goals try exact hcov.elim
        · exact cover_shift (d := 176) (len := 8) hcov (by decide) (by decide)
        · exact cover_shift (d := 168) (len := 8) hcov (by decide) (by decide)
        · exact cover_shift (d := 160) (len := 8) hcov (by decide) (by decide)
        · exact cover_shift (d := 152) (len := 8) hcov (by decide) (by decide)
    have hB' : AgreesExcept [.reg 0, .reg 1, .reg 2, .reg 6, .reg 7, .rip,
        .mem (stackPtr s + 120) 64] u1 u2 := by
      apply hB.agrees.widen
      · intro c hc hm
        simp only [longBEffect, Effect.components, List.map_cons, List.map_nil,
          List.cons_append, List.nil_append, Write.component, Operand.component,
          List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals simp_all [Component.isMem]
      · intro x c hc hcov
        refine ⟨.mem (stackPtr s + 120) 64, by simp, ?_⟩
        simp only [longBEffect, Effect.components, List.map_cons, List.map_nil,
          List.cons_append, List.nil_append, Write.component, Operand.component,
          List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals try exact hcov.elim
        all_goals rw [hsp1] at hcov
        · exact cover_shift (d := 144) (len := 8) hcov (by decide) (by decide)
        · exact cover_shift (d := 136) (len := 8) hcov (by decide) (by decide)
        · exact cover_shift (d := 128) (len := 8) hcov (by decide) (by decide)
        · exact cover_shift (d := 120) (len := 8) hcov (by decide) (by decide)
    have hC' : AgreesExcept [.reg 0, .reg 1, .reg 2, .reg 6, .reg 7, .rip,
        .mem (stackPtr s + 120) 64] u2 t := by
      apply hC.agrees.widen
      · intro c hc hm
        simp only [argumentEffect, Effect.components, List.map_cons, List.map_nil,
          List.cons_append, List.nil_append, Write.component, Operand.component,
          List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl
        all_goals simp_all [Component.isMem]
      · intro x c hc hcov
        simp only [argumentEffect, Effect.components, List.map_cons, List.map_nil,
          List.cons_append, List.nil_append, Write.component, Operand.component,
          List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl
        all_goals exact hcov.elim
    exact (hA'.trans (hB'.trans hC')).mono (by simp)
  refine ⟨t, ⟨⟨n1 + (n2 + n3), h1.trans (h2.trans h3)⟩, hr3, hc3, hC.rip, ?_, ?_, ?_, hwC.2.2,
    hcopy, hag⟩⟩
  · rw [hsp3, hsp2, hsp1]
  · rw [hwC.1, hsp2, hsp1]
  · rw [hwC.2.1, hsp2, hsp1]

structure FinalCopied [Bindings] (boundary : ReturnBoundary) (s t : RamState) : Prop where
  advances : ∃ fuel, Advances boundary fuel s t
  ready : ReadyToStep t
  code : CodeIn Extracted.programImage t
  rip : t.RIP = 0x100272
  rsp : stackPtr t = stackPtr s
  rdi : (Operand.reg 7 : Operand 64).read t = stackPtr s
  rsi : (Operand.reg 6 : Operand 64).read t = stackPtr s + 120
  rdx : (Operand.reg 2 : Operand 64).read t = 1
  copy : ∀ i < 56, t.external[stackPtr s + BitVec.ofNat 64 (120 + i)]? =
    s.external[stackPtr s + BitVec.ofNat 64 (24 + i)]?
  length : ∀ k < 8, t.external[stackPtr s + BitVec.ofNat 64 (176 + k)]? =
    some (storedByte (lengthValue s) k)
  agrees : AgreesExcept [.reg 0, .reg 1, .reg 2, .reg 6, .reg 7, .reg 12, .reg 15, .flags, .rip, .mem (stackPtr s + 80) 8, .mem (stackPtr s + 120) 64] s t

set_option maxHeartbeats 1000000 in
theorem final_copy [Bindings] {boundary : ReturnBoundary} {s : RamState}
    (hr : ReadyToStep s) (hc : CodeIn Extracted.programImage s)
    (hout : ¬ InProgram boundary.rip) (h : PartPre 0x1001f2 s) :
    ∃ t, FinalCopied boundary s t := by
  obtain ⟨n0, u0, h0, hr0, hc0, hL⟩ := length_run hr hc hout h
  have hsp0 := length_rsp hL
  have hs0 := h.toStorage.of_agrees hL.agrees hsp0
  obtain ⟨n1, u1, h1, hr1, hc1, hA⟩ := finalA_run hr0 hc0 hout ⟨hs0, hL.rip⟩
  have hsp1 := finalA_rsp hA
  have hs1 := hs0.of_agrees hA.agrees hsp1
  obtain ⟨n2, u2, h2, hr2, hc2, hB⟩ := finalB_run hr1 hc1 hout ⟨hs1, hA.rip⟩
  have hsp2 := finalB_rsp hB
  have hs2 := hs1.of_agrees hB.agrees hsp2
  obtain ⟨n3, t, h3, hr3, hc3, hC⟩ := arguments_run hr2 hc2 hout (.inr rfl) hB.rip
  have hext : t.external = u2.external := hC.agrees.external (by
    simp [argumentEffect, Effect.components, Component.Covers])
  have hwL := hL.writes
  simp only [lengthEffect, Write.AllHold] at hwL
  have hwA := hA.writes
  simp only [finalAEffect, Write.AllHold] at hwA
  have hwB := hB.writes
  simp only [finalBEffect, Write.AllHold] at hwB
  have hwC := hC.writes
  simp only [argumentEffect, Write.AllHold] at hwC
  have hsp3 : stackPtr t = stackPtr u2 := hC.agrees.read (n := 64) (r := 4) (by
    simp [argumentEffect, Effect.components])
  have hcopy : ∀ i < 56, t.external[stackPtr s + BitVec.ofNat 64 (120 + i)]? =
      s.external[stackPtr s + BitVec.ofNat 64 (24 + i)]? := by
    intro i hi
    rcases (show i < 8 ∨ (8 ≤ i ∧ i < 16) ∨ (16 ≤ i ∧ i < 24) ∨ (24 ≤ i ∧ i < 32) ∨ (32 ≤ i ∧ i < 40) ∨ (40 ≤ i ∧ i < 48) ∨ (48 ≤ i ∧ i < 56) by omega) with hw | hw | hw | hw | hw | hw | hw
    · have hk : i - 0 < 8 := by omega
      have e1 := word_bytes hs1 hs2 hsp2 120 24 (by decide) (by decide) hwB.2.2.2.2.2 (i - 0) hk
      rw [hsp1, hsp0, show 120 + (i - 0) = 120 + i by omega, show 24 + (i - 0) = 24 + i by omega] at e1
      rw [hext, e1]
      have e2 := finalA_byte hA (24 + i) (by omega) (by omega)
      rw [hsp0] at e2
      rw [e2]
      exact length_byte hL (24 + i) (by omega) (by omega)
    · have hk : i - 8 < 8 := by omega
      have e1 := word_bytes hs1 hs2 hsp2 128 32 (by decide) (by decide) hwB.2.2.2.2.1 (i - 8) hk
      rw [hsp1, hsp0, show 128 + (i - 8) = 120 + i by omega, show 32 + (i - 8) = 24 + i by omega] at e1
      rw [hext, e1]
      have e2 := finalA_byte hA (24 + i) (by omega) (by omega)
      rw [hsp0] at e2
      rw [e2]
      exact length_byte hL (24 + i) (by omega) (by omega)
    · have hk : i - 16 < 8 := by omega
      have e1 := word_bytes hs1 hs2 hsp2 136 40 (by decide) (by decide) hwB.2.2.2.1 (i - 16) hk
      rw [hsp1, hsp0, show 136 + (i - 16) = 120 + i by omega, show 40 + (i - 16) = 24 + i by omega] at e1
      rw [hext, e1]
      have e2 := finalA_byte hA (24 + i) (by omega) (by omega)
      rw [hsp0] at e2
      rw [e2]
      exact length_byte hL (24 + i) (by omega) (by omega)
    · have hk : i - 24 < 8 := by omega
      have e1 := word_bytes hs1 hs2 hsp2 144 48 (by decide) (by decide) hwB.2.2.1 (i - 24) hk
      rw [hsp1, hsp0, show 144 + (i - 24) = 120 + i by omega, show 48 + (i - 24) = 24 + i by omega] at e1
      rw [hext, e1]
      have e2 := finalA_byte hA (24 + i) (by omega) (by omega)
      rw [hsp0] at e2
      rw [e2]
      exact length_byte hL (24 + i) (by omega) (by omega)
    · have hk : i - 32 < 8 := by omega
      have e1 := word_bytes hs0 hs1 hsp1 152 56 (by decide) (by decide) hwA.2.2.2 (i - 32) hk
      rw [hsp0, show 152 + (i - 32) = 120 + i by omega, show 56 + (i - 32) = 24 + i by omega] at e1
      rw [hext]
      have e2 := finalB_byte hB (120 + i) (by omega) (by omega)
      rw [hsp1, hsp0] at e2
      rw [e2, e1]
      exact length_byte hL (24 + i) (by omega) (by omega)
    · have hk : i - 40 < 8 := by omega
      have e1 := word_bytes hs0 hs1 hsp1 160 64 (by decide) (by decide) hwA.2.2.1 (i - 40) hk
      rw [hsp0, show 160 + (i - 40) = 120 + i by omega, show 64 + (i - 40) = 24 + i by omega] at e1
      rw [hext]
      have e2 := finalB_byte hB (120 + i) (by omega) (by omega)
      rw [hsp1, hsp0] at e2
      rw [e2, e1]
      exact length_byte hL (24 + i) (by omega) (by omega)
    · have hk : i - 48 < 8 := by omega
      have e1 := word_bytes hs0 hs1 hsp1 168 72 (by decide) (by decide) hwA.2.1 (i - 48) hk
      rw [hsp0, show 168 + (i - 48) = 120 + i by omega, show 72 + (i - 48) = 24 + i by omega] at e1
      rw [hext]
      have e2 := finalB_byte hB (120 + i) (by omega) (by omega)
      rw [hsp1, hsp0] at e2
      rw [e2, e1]
      exact length_byte hL (24 + i) (by omega) (by omega)
  have hlength : ∀ k < 8, t.external[stackPtr s + BitVec.ofNat 64 (176 + k)]? =
      some (storedByte (lengthValue s) k) := by
    intro k hk
    rw [hext]
    have e2 := finalB_byte hB (176 + k) (by omega) (by omega)
    rw [hsp1, hsp0] at e2
    rw [e2]
    have e3 := finalA_byte hA (176 + k) (by omega) (by omega)
    rw [hsp0] at e3
    rw [e3]
    have hrd : ∀ i < 64 / 8, (u0.external[stackPtr s + BitVec.ofNat 64 176 + BitVec.ofNat 64 i]?).isSome := by
      intro i hi
      rw [BitVec.add_assoc, ← BitVec.ofNat_add, ← hsp0]
      exact stack_byte_some hs0 (176 + i) (by omega)
    have hb := Bytes.of_memLoad hrd k hk
    have hv : memLoad u0.external (stackPtr s + BitVec.ofNat 64 176) 64 = lengthValue s := hwL.2.2.2
    rw [hv, BitVec.add_assoc, ← BitVec.ofNat_add] at hb
    exact hb
  have hag : AgreesExcept [.reg 0, .reg 1, .reg 2, .reg 6, .reg 7, .reg 12, .reg 15, .flags, .rip, .mem (stackPtr s + 80) 8, .mem (stackPtr s + 120) 64] s t := by
    have hL' : AgreesExcept [.reg 0, .reg 1, .reg 2, .reg 6, .reg 7, .reg 12, .reg 15, .flags, .rip, .mem (stackPtr s + 80) 8, .mem (stackPtr s + 120) 64] s u0 := by
      apply hL.agrees.widen
      · intro c hc hm
        simp only [lengthEffect, Effect.components, List.map_cons, List.map_nil,
          List.cons_append, List.nil_append, Write.component, Operand.component,
          List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
        all_goals simp_all [Component.isMem]
      · intro x c hc hcov
        simp only [lengthEffect, Effect.components, List.map_cons, List.map_nil,
          List.cons_append, List.nil_append, Write.component, Operand.component,
          List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl
        all_goals try exact hcov.elim
        · exact ⟨.mem (stackPtr s + 80) 8, by simp, hcov⟩
        · exact ⟨.mem (stackPtr s + 120) 64, by simp,
            cover_shift (d := 176) (len := 8) hcov (by decide) (by decide)⟩
    have hA' : AgreesExcept [.reg 0, .reg 1, .reg 2, .reg 6, .reg 7, .reg 12, .reg 15, .flags, .rip, .mem (stackPtr s + 80) 8, .mem (stackPtr s + 120) 64] u0 u1 := by
      apply hA.agrees.widen
      · intro c hc hm
        simp only [finalAEffect, Effect.components, List.map_cons, List.map_nil,
          List.cons_append, List.nil_append, Write.component, Operand.component,
          List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl
        all_goals simp_all [Component.isMem]
      · intro x c hc hcov
        refine ⟨.mem (stackPtr s + 120) 64, by simp, ?_⟩
        simp only [finalAEffect, Effect.components, List.map_cons, List.map_nil,
          List.cons_append, List.nil_append, Write.component, Operand.component,
          List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl
        all_goals try exact hcov.elim
        all_goals rw [hsp0] at hcov
        · exact cover_shift (d := 168) (len := 8) hcov (by decide) (by decide)
        · exact cover_shift (d := 160) (len := 8) hcov (by decide) (by decide)
        · exact cover_shift (d := 152) (len := 8) hcov (by decide) (by decide)
    have hB' : AgreesExcept [.reg 0, .reg 1, .reg 2, .reg 6, .reg 7, .reg 12, .reg 15, .flags, .rip, .mem (stackPtr s + 80) 8, .mem (stackPtr s + 120) 64] u1 u2 := by
      apply hB.agrees.widen
      · intro c hc hm
        simp only [finalBEffect, Effect.components, List.map_cons, List.map_nil,
          List.cons_append, List.nil_append, Write.component, Operand.component,
          List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals simp_all [Component.isMem]
      · intro x c hc hcov
        refine ⟨.mem (stackPtr s + 120) 64, by simp, ?_⟩
        simp only [finalBEffect, Effect.components, List.map_cons, List.map_nil,
          List.cons_append, List.nil_append, Write.component, Operand.component,
          List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals try exact hcov.elim
        all_goals rw [hsp1, hsp0] at hcov
        · exact cover_shift (d := 144) (len := 8) hcov (by decide) (by decide)
        · exact cover_shift (d := 136) (len := 8) hcov (by decide) (by decide)
        · exact cover_shift (d := 128) (len := 8) hcov (by decide) (by decide)
        · exact cover_shift (d := 120) (len := 8) hcov (by decide) (by decide)
    have hC' : AgreesExcept [.reg 0, .reg 1, .reg 2, .reg 6, .reg 7, .reg 12, .reg 15, .flags, .rip, .mem (stackPtr s + 80) 8, .mem (stackPtr s + 120) 64] u2 t := by
      apply hC.agrees.widen
      · intro c hc hm
        simp only [argumentEffect, Effect.components, List.map_cons, List.map_nil,
          List.cons_append, List.nil_append, Write.component, Operand.component,
          List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl
        all_goals simp_all [Component.isMem]
      · intro x c hc hcov
        simp only [argumentEffect, Effect.components, List.map_cons, List.map_nil,
          List.cons_append, List.nil_append, Write.component, Operand.component,
          List.mem_cons, List.not_mem_nil, or_false] at hc
        rcases hc with rfl | rfl | rfl | rfl
        all_goals exact hcov.elim
    exact (hL'.trans (hA'.trans (hB'.trans hC'))).mono (by simp)
  refine ⟨t, ⟨⟨n0 + (n1 + (n2 + n3)), h0.trans (h1.trans (h2.trans h3))⟩, hr3, hc3, hC.rip,
    ?_, ?_, ?_, hwC.2.2, hcopy, hlength, hag⟩⟩
  · rw [hsp3, hsp2, hsp1, hsp0]
  · rw [hwC.1, hsp2, hsp1, hsp0]
  · rw [hwC.2.1, hsp2, hsp1, hsp0]

end Sha1.Proofs.Buffered.Finalize.Digest.BlockCopy
