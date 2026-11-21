import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.LoadStep
import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.StoreStep
import P256.Proofs.Sec1.SquareRoot.Exponent.Initialize.InputMemory

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.ExponentInitialize

open P256.Spec.Program P256.Spec.Program.Routines P256.Proofs.Program
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

def inputCopyMemory (s : RamState) (memory : Ram) : Ram :=
  [ (24, 0x310), (16, 0x308), (8, 0x300), (0, 0x2f8) ].foldl
    (fun m pair => memStore m (exponentFrameBase s + BitVec.ofNat 64 pair.2)
      (memLoad s.external (s.regValue .rsi + BitVec.ofNat 64 pair.1) 64)) memory

def inputCopyComponents (s : RamState) : List Component :=
  [.reg 0, .reg 8, .rip, .mem (exponentFrameBase s + 0x310) 8,
    .mem (exponentFrameBase s + 0x308) 8, .mem (exponentFrameBase s + 0x300) 8,
    .mem (exponentFrameBase s + 0x2f8) 8]

set_option maxRecDepth 2048 in
set_option maxHeartbeats 800000 in
theorem copy_input [Bindings] {s t : RamState} {boundary : ReturnBoundary} {x : Nat}
    (ctx : ExponentPre s boundary x) (hf : Frame s t) (rip : t.RIP = 0x114bb4)
    (input : t.regValue .rsi = s.regValue .rsi) :
    ∃ u, Advances boundary 8 t u ∧ Frame s u ∧ u.RIP = 0x114be3 ∧
      AgreesExcept (inputCopyComponents s) t u ∧
      u.external = inputCopyMemory s t.external := by
  have input1 : t.regValue .rsi = s.regValue .rsi := input
  have addr1 : (AddrMode.base 6 (.d8 24)).addr t (Extracted.textAddress + BitVec.ofNat 64 (84916+3+(AddrMode.base 6 (.d8 24)).tail.length)) =
      s.regValue .rsi + 24 := by
    change t.regValue .rsi + 24 = _
    rw [input1]
  obtain ⟨t1, a1, f1, ip1, v1, g1, m1⟩ :=
    frame_load_r64 ctx.outerBoundary hf 0x14bb4 0x48 0
      (.base 6 (.d8 24)) (by simp [RexWPrefix]) (by decide) rfl rfl (by decide)
      rip (by decide) (by decide +kernel) (by
        rw [addr1]
        exact input_readable ctx hf (offset := 24) (by decide))
  change AgreesExcept [.reg 0, .rip] t t1 at g1
  have value1 : (Operand.reg 0 : Operand 64).read t1 =
      memLoad s.external (s.regValue .rsi + 24) 64 := by
    rw [addr1] at v1
    exact v1.trans (input_memLoad_of_frame ctx hf (offset := 24) (by decide))
  have source2 : (Operand.reg 0 : Operand 64).read t1 =
      memLoad s.external (s.regValue .rsi + 24) 64 := by
    exact value1
  obtain ⟨t2, a2, f2, ip2, _, g2, m2⟩ :=
    frame_store_r64 ctx.toCalleePre f1 0x14bb8 0x310 (.d32 0x310)
      0x48 0 (by simp [RexWPrefix]) rfl rfl rfl (by decide)
      ip1 (by decide) (by decide +kernel)
  have memory2 : t2.external = memStore t1.external
      (exponentFrameBase s + 0x310)
      (memLoad s.external (s.regValue .rsi + 24) 64) := by
    exact m2.trans (congrArg (memStore t1.external _) source2)
  have input3 : t2.regValue .rsi = s.regValue .rsi := (g2.read (n := 64) (r := 6) (by simp)).trans ((g1.read (n := 64) (r := 6) (by simp)).trans (input))
  have addr3 : (AddrMode.base 6 (.d8 16)).addr t2 (Extracted.textAddress + BitVec.ofNat 64 (84928+3+(AddrMode.base 6 (.d8 16)).tail.length)) =
      s.regValue .rsi + 16 := by
    change t2.regValue .rsi + 16 = _
    rw [input3]
  obtain ⟨t3, a3, f3, ip3, v3, g3, m3⟩ :=
    frame_load_r64 ctx.outerBoundary f2 0x14bc0 0x48 0
      (.base 6 (.d8 16)) (by simp [RexWPrefix]) (by decide) rfl rfl (by decide)
      ip2 (by decide) (by decide +kernel) (by
        rw [addr3]
        exact input_readable ctx f2 (offset := 16) (by decide))
  change AgreesExcept [.reg 0, .rip] t2 t3 at g3
  have value3 : (Operand.reg 0 : Operand 64).read t3 =
      memLoad s.external (s.regValue .rsi + 16) 64 := by
    rw [addr3] at v3
    exact v3.trans (input_memLoad_of_frame ctx f2 (offset := 16) (by decide))
  have source4 : (Operand.reg 0 : Operand 64).read t3 =
      memLoad s.external (s.regValue .rsi + 16) 64 := by
    exact value3
  obtain ⟨t4, a4, f4, ip4, _, g4, m4⟩ :=
    frame_store_r64 ctx.toCalleePre f3 0x14bc4 0x308 (.d32 0x308)
      0x48 0 (by simp [RexWPrefix]) rfl rfl rfl (by decide)
      ip3 (by decide) (by decide +kernel)
  have memory4 : t4.external = memStore t3.external
      (exponentFrameBase s + 0x308)
      (memLoad s.external (s.regValue .rsi + 16) 64) := by
    exact m4.trans (congrArg (memStore t3.external _) source4)
  have input5 : t4.regValue .rsi = s.regValue .rsi := (g4.read (n := 64) (r := 6) (by simp)).trans ((g3.read (n := 64) (r := 6) (by simp)).trans ((g2.read (n := 64) (r := 6) (by simp)).trans ((g1.read (n := 64) (r := 6) (by simp)).trans (input))))
  have addr5 : (AddrMode.base 6 .none).addr t4 (Extracted.textAddress + BitVec.ofNat 64 (84940+3+(AddrMode.base 6 .none).tail.length)) =
      s.regValue .rsi + 0 := by
    change t4.regValue .rsi + 0 = _
    rw [input5]
  obtain ⟨t5, a5, f5, ip5, v5, g5, m5⟩ :=
    frame_load_r64 ctx.outerBoundary f4 0x14bcc 0x48 0
      (.base 6 .none) (by simp [RexWPrefix]) (by decide) rfl rfl (by decide)
      ip4 (by decide) (by decide +kernel) (by
        rw [addr5]
        exact input_readable ctx f4 (offset := 0) (by decide))
  change AgreesExcept [.reg 0, .rip] t4 t5 at g5
  have value5 : (Operand.reg 0 : Operand 64).read t5 =
      memLoad s.external (s.regValue .rsi + 0) 64 := by
    rw [addr5] at v5
    exact v5.trans (input_memLoad_of_frame ctx f4 (offset := 0) (by decide))
  have input6 : t5.regValue .rsi = s.regValue .rsi := (g5.read (n := 64) (r := 6) (by simp)).trans ((g4.read (n := 64) (r := 6) (by simp)).trans ((g3.read (n := 64) (r := 6) (by simp)).trans ((g2.read (n := 64) (r := 6) (by simp)).trans ((g1.read (n := 64) (r := 6) (by simp)).trans (input)))))
  have addr6 : (AddrMode.base 6 (.d8 8)).addr t5 (Extracted.textAddress + BitVec.ofNat 64 (84943+3+(AddrMode.base 6 (.d8 8)).tail.length)) =
      s.regValue .rsi + 8 := by
    change t5.regValue .rsi + 8 = _
    rw [input6]
  obtain ⟨t6, a6, f6, ip6, v6, g6, m6⟩ :=
    frame_load_r64 ctx.outerBoundary f5 0x14bcf 0x4c 0
      (.base 6 (.d8 8)) (by simp [RexWPrefix]) (by decide) rfl rfl (by decide)
      ip5 (by decide) (by decide +kernel) (by
        rw [addr6]
        exact input_readable ctx f5 (offset := 8) (by decide))
  change AgreesExcept [.reg 8, .rip] t5 t6 at g6
  have value6 : (Operand.reg 8 : Operand 64).read t6 =
      memLoad s.external (s.regValue .rsi + 8) 64 := by
    rw [addr6] at v6
    exact v6.trans (input_memLoad_of_frame ctx f5 (offset := 8) (by decide))
  have source7 : (Operand.reg 8 : Operand 64).read t6 =
      memLoad s.external (s.regValue .rsi + 8) 64 := by
    exact value6
  obtain ⟨t7, a7, f7, ip7, _, g7, m7⟩ :=
    frame_store_r64 ctx.toCalleePre f6 0x14bd3 0x300 (.d32 0x300)
      0x4c 0 (by simp [RexWPrefix]) rfl rfl rfl (by decide)
      ip6 (by decide) (by decide +kernel)
  have memory7 : t7.external = memStore t6.external
      (exponentFrameBase s + 0x300)
      (memLoad s.external (s.regValue .rsi + 8) 64) := by
    exact m7.trans (congrArg (memStore t6.external _) source7)
  have source8 : (Operand.reg 0 : Operand 64).read t7 =
      memLoad s.external (s.regValue .rsi + 0) 64 := by
    rw [g7.read (by simp), g6.read (by decide), value5]
  obtain ⟨t8, a8, f8, ip8, _, g8, m8⟩ :=
    frame_store_r64 ctx.toCalleePre f7 0x14bdb 0x2f8 (.d32 0x2f8)
      0x48 0 (by simp [RexWPrefix]) rfl rfl rfl (by decide)
      ip7 (by decide) (by decide +kernel)
  have memory8 : t8.external = memStore t7.external
      (exponentFrameBase s + 0x2f8)
      (memLoad s.external (s.regValue .rsi + 0) 64) := by
    exact m8.trans (congrArg (memStore t7.external _) source8)
  refine ⟨t8, (((((((a1.trans a2).trans a3).trans a4).trans a5).trans a6).trans a7).trans a8), f8, ip8, ?_, ?_⟩
  · apply (((((((g1.trans g2).trans g3).trans g4).trans g5).trans g6).trans g7).trans g8).mono
    intro c hc
    simp only [inputCopyComponents, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hc ⊢
    rcases hc with (((((((rfl | rfl) | (rfl | rfl)) | (rfl | rfl)) |
      (rfl | rfl)) | (rfl | rfl)) | (rfl | rfl)) | (rfl | rfl)) | (rfl | rfl)
    all_goals first | exact Or.inl rfl | exact Or.inr rfl | simp
  · simp only [memory8, memory7, m6, m5, memory4, m3, memory2, m1,
      inputCopyMemory, List.foldl_cons, List.foldl_nil, BitVec.ofNat_eq_ofNat]

end P256.Proofs.Sec1.SquareRoot.ExponentInitialize
