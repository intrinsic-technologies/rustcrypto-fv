import K256.Proofs.Generate.Generator.Sample.Decide.Nonzero
import K256.Proofs.Generate.Generator.Sample.Value
import K256.Proofs.Generate.LIR.Fn105f30

namespace K256.Proofs.Generate.Generator.Sample

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR

private theorem jump {l r : Location Value Ram Label signature}
    (eq : program.runBlock (dialect Extracted.programImage) l = .jump r)
    (stack : List (StackFrame Value Label signature Reg.count)) :
    Run.Reaches ⟨l, stack⟩ ⟨r, stack⟩ := by
  apply Semantics.Reaches.single
  change program.step _ _ = _
  simp only [Program.step, eq, Transfer.next]

private abbrev order (s : RamState) (i : Nat) :=
  Sampling.orderFlag (word s i 0) (word s i 1) (word s i 2) (word s i 3)

private theorem rangeBranch {b : Registers} {mem : Ram} {s random fr i}
    (h : AfterDecode s random fr i b mem)
    (stack : List (StackFrame Value Label signature Reg.count)) :
    ∃ c : Registers, Run.Reaches ⟨⟨.l10605d, b, mem⟩, stack⟩
        ⟨⟨if order s i = 1 then .l105f70 else .l10606b, c, mem⟩, stack⟩ ∧
      AfterDecode s random fr i c mem := by
  have atoms := h.atoms
  simp only [Fn105f30.frameAt, Fn105f30.frameAtG0, Atom.All, Atom.Holds] at atoms
  obtain ⟨rsp, _, _, _, _, _, _, _, _, _, _, _, _, _, _, _, writable, room, _⟩ := atoms
  have sp : b[4].get 64 = fr.rsp - 392 := congrArg (Value.get 64) rsp
  have address : fr.rsp - 392 + 256 = fr.rsp - 136 := by bv_omega
  have ok : LoadOk mem (fr.rsp - 136) 1 := LoadOk.of_region writable.readable (by bv_omega) (by bv_omega)
  have flag := h.flag
  change memLoad mem (fr.rsp - 136) 8 = (order s i).setWidth 8 at flag
  have zf : (cmpSpec (memLoad mem (fr.rsp - 136) 8) 1).ZF = decide (order s i = 1) := by
    rw [flag]
    unfold order
    rw [Sampling.orderFlag_eq]
    split <;> rfl
  by_cases valid : order s i = 1
  all_goals
    first | rw [ite_eq_left valid] | rw [ite_eq_right valid]
    refine ⟨?_, jump ?_ stack, ?_⟩
    rotate_left
    · cfg_eval [sp, address, ok, zf, valid, decide_true, decide_false]
      rfl
    · exact ⟨⟨h.atoms, h.writes⟩, h.rdxWidth, h.r8Width, h.r9Width, h.cursorReg,
        h.remainingReg, h.nextLength, h.scratch, h.decoded, h.limbs, h.flag⟩


private theorem enoughRemaining {s : RamState} {random : ByteArray} {i : Nat}
    (call : ValidCall signingKeyGenerateFromRng s [random]) (bound : i < random.size / 32) :
    (cmpSpec (remaining random i) 32).CF = false := by
  have length : (s.regValue .rdx).toNat = random.size := call.lengthArgumentsMatchInputs.1
  have small := (s.regValue .rdx).isLt
  change decide ((BitVec.ofNat 64 (random.size - 32*i)).toNat < 32) = false
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (a := random.size - 32*i) (b := 2^64) (by omega),
    decide_eq_false_iff_not]
  omega

private theorem advanceCursor (s : RamState) (i : Nat) :
    cursor s i + 32 = cursor s (i+1) := by
  simp only [cursor, BitVec.add_assoc]
  congr 1
  change BitVec.ofNat 64 (32*(i+1)) + BitVec.ofNat 64 32 = _
  rw [← BitVec.ofNat_add]
  congr 1

private theorem retryRange {s : RamState} {random : ByteArray} {fr i b mem}
    (call : ValidCall signingKeyGenerateFromRng s [random]) (h : AfterDecode s random fr i b mem)
    (more : i+1 < random.size / 32) (stack : List (StackFrame Value Label signature Reg.count)) :
    ∃ c : Registers, Run.Reaches ⟨⟨.l10606b, b, mem⟩, stack⟩ ⟨⟨.l106020, c, mem⟩, stack⟩ ∧
      AtBlock s random fr (i+1) c mem := by
  have cf := enoughRemaining call more
  have bx : b[3].get 64 = remaining random (i+1) := congrArg (Value.get 64) h.nextLength
  have bp : b[5].get 64 = cursor s i := congrArg (Value.get 64) h.cursorReg
  refine ⟨?_, jump ?_ stack, ?_⟩
  rotate_left
  · cfg_eval [bx, bp, cf, advanceCursor]
    rfl
  · exact ⟨⟨h.atoms, h.writes⟩, h.rdxWidth, h.r8Width, h.r9Width, rfl,
      rfl, h.scratch, h.decoded⟩

private theorem decrement {random : ByteArray} {i : Nat} (bound : i < random.size / 32) :
    remaining random i - 32 = remaining random (i+1) := by
  change BitVec.ofNat 64 (random.size - 32*i) - BitVec.ofNat 64 32 = _
  rw [show random.size - 32*i = (random.size - 32*(i+1)) + 32 by omega, BitVec.ofNat_add]
  unfold remaining
  bv_omega

private theorem retryZero {s : RamState} {random : ByteArray} {fr : Activation} {i : Nat}
    {b : Registers} {mem : Ram} (call : ValidCall signingKeyGenerateFromRng s [random])
    (more : i+1 < random.size / 32) (h : Frame .l106009 fr b mem)
    (dx : b[2].width = 64) (r8 : b[8].width = 64) (r9 : b[9].width = 64)
    (cursorReg : b[5] = ⟨64, cursor s i⟩) (remainingReg : b[13] = ⟨64, remaining random (i+1)⟩)
    (scratch : b[12] = ⟨64, fr.rsp - 288⟩) (decoded : b[15] = ⟨64, fr.rsp - 168⟩)
    (stack : List (StackFrame Value Label signature Reg.count)) :
    ∃ c : Registers, Run.Reaches ⟨⟨.l106009, b, mem⟩, stack⟩ ⟨⟨.l106020, c, mem⟩, stack⟩ ∧
      AtBlock s random fr (i+1) c mem := by
  have cf := enoughRemaining call more
  have len : b[13].get 64 = remaining random (i+1) := congrArg (Value.get 64) remainingReg
  have bp : b[5].get 64 = cursor s i := congrArg (Value.get 64) cursorReg
  have test : ∃ a : Registers, program.runBlock (dialect Extracted.programImage) ⟨.l106009, b, mem⟩ =
      .jump ⟨.l10600f, a, mem⟩ ∧ Frame .l10600f fr a mem ∧ a[2] = b[2] ∧ a[8] = b[8] ∧
      a[9] = b[9] ∧ a[5] = b[5] ∧ a[13] = b[13] ∧ a[12] = b[12] ∧ a[15] = b[15] := by
    refine ⟨?_, ?_, ?_⟩
    rotate_left
    · cfg_eval [len, cf]
      rfl
    · exact ⟨⟨h.atoms, h.writes⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨a, test, frame, x2, x8, x9, x5, x13, x12, x15⟩ := test
  refine ⟨?_, (jump test stack).trans (jump ?_ stack), ?_⟩
  rotate_left
  · cfg_eval [x5, bp, advanceCursor]
    rfl
  · refine ⟨⟨frame.atoms, frame.writes⟩, congrArg Value.width x2 |>.trans dx,
      congrArg Value.width x8 |>.trans r8, congrArg Value.width x9 |>.trans r9, ?_,
      x13.trans remainingReg, x12.trans scratch, x15.trans decoded⟩
    change Value.mk 64 (a[5].get 64 + 32) = _
    rw [x5, bp, advanceCursor]

private theorem decideNonzero {s : RamState} {random : ByteArray} {fr : Activation} {i : Nat}
    {b : Registers} {mem : Ram} (call : ValidCall signingKeyGenerateFromRng s [random])
    (bound : i < random.size / 32) (h : AfterNonzero s random fr i b mem)
    (stack : List (StackFrame Value Label signature Reg.count)) :
    (∀ d, Sampling.decodeBlock random i = some d → (¬ ∀ j < 4, word s i j = 0) →
      ∃ c : Registers, Run.Reaches ⟨⟨.l106001, b, mem⟩, stack⟩ ⟨⟨.l10607d, c, mem⟩, stack⟩ ∧
        Accepted fr d c mem) ∧
    ((∀ j < 4, word s i j = 0) → i+1 < random.size / 32 →
      ∃ c : Registers, Run.Reaches ⟨⟨.l106001, b, mem⟩, stack⟩ ⟨⟨.l106020, c, mem⟩, stack⟩ ∧
        AtBlock s random fr (i+1) c mem) := by
  have len : b[13].get 64 = remaining random i := congrArg (Value.get 64) h.remainingReg
  have al : (b[0].get 64).setWidth 8 = b[0].get 8 := BitVec.setWidth_setWidth_of_le _ (by decide)
  constructor
  · intro d hd nonzero
    have one := h.flag.mpr nonzero
    have zf : (cmpSpec (b[0].get 8) 1).ZF = true := by rw [cmpSpec_ZF, one]; rfl
    refine ⟨?_, jump ?_ stack, ?_⟩
    rotate_left
    · cfg_eval [al, zf, len, decrement bound]
      rfl
    · refine ⟨⟨h.atoms, h.writes⟩, ?_, ?_⟩
      · intro ⟨r, hr⟩ idx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at idx
        rcases idx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
        all_goals first | rfl | exact h.rdxWidth | exact h.rbxWidth | exact h.r8Width | exact h.r9Width |
          exact congrArg Value.width h.cursorReg | exact congrArg Value.width h.scratch |
          exact congrArg Value.width h.decoded
      · intro j hj
        simpa only [Vector.getElem_ofFn, word_eq_limb call bound hd j hj] using h.limbs j hj
  · intro zero more
    have ne : b[0].get 8 ≠ 1 := fun eq => h.flag.mp eq zero
    have zf : (cmpSpec (b[0].get 8) 1).ZF = false := by
      rw [cmpSpec_ZF, beq_eq_false_iff_ne]
      exact ne
    have test : ∃ a : Registers, program.runBlock (dialect Extracted.programImage) ⟨.l106001, b, mem⟩ =
        .jump ⟨.l106009, a, mem⟩ ∧ Frame .l106009 fr a mem ∧ a[2] = b[2] ∧ a[8] = b[8] ∧
        a[9] = b[9] ∧ a[5] = b[5] ∧ a[13] = ⟨64, remaining random (i+1)⟩ ∧
        a[12] = b[12] ∧ a[15] = b[15] := by
      refine ⟨?_, ?_, ?_⟩
      rotate_left
      · cfg_eval [al, zf, len, decrement bound]
        rfl
      · exact ⟨⟨h.atoms, h.writes⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    obtain ⟨a, test, frame, x2, x8, x9, x5, len', x12, x15⟩ := test
    obtain ⟨c, steps, post⟩ := retryZero call more frame ((congrArg Value.width x2).trans h.rdxWidth)
      ((congrArg Value.width x8).trans h.r8Width) ((congrArg Value.width x9).trans h.r9Width)
      (x5.trans h.cursorReg) len' (x12.trans h.scratch) (x15.trans h.decoded) stack
    exact ⟨c, (jump test stack).trans steps, post⟩
theorem decideBlock {s : RamState} {random : ByteArray} {fr : Activation} {a : Registers}
    (call : ValidCall signingKeyGenerateFromRng s [random]) (entry : Entry s fr a) {i : Nat}
    {b : Registers} {mem : Ram} (bound : i < random.size / 32)
    (decoded : AfterDecode s random fr i b mem) (stack : List (StackFrame Value Label signature Reg.count)) :
    match Sampling.decodeBlock random i with
    | some d => ∃ c m, Run.Reaches ⟨⟨.l10605d, b, mem⟩, stack⟩ ⟨⟨.l10607d, c, m⟩, stack⟩ ∧
        Accepted fr d c m
    | none => i + 1 < random.size / 32 → ∃ c m,
        Run.Reaches ⟨⟨.l10605d, b, mem⟩, stack⟩ ⟨⟨.l106020, c, m⟩, stack⟩ ∧
        AtBlock s random fr (i+1) c m := by
  have input : ValidInput s (registerRegion s .rsi random.size) random := call.inputsInMemory.1
  have eq := Sampling.decodeBlock_eq input.2.2 bound
  change Sampling.decodeBlock random i =
    (if order s i = 1 ∧ ¬ (word s i 0 = 0 ∧ word s i 1 = 0 ∧ word s i 2 = 0 ∧ word s i 3 = 0)
     then some _ else none) at eq
  obtain ⟨c, step, mid⟩ := rangeBranch decoded stack
  by_cases range : order s i = 1
  · rw [ite_eq_left range] at step
    obtain ⟨e, n, test, flags⟩ := checkNonzero call entry mid stack
    obtain ⟨accept, retry⟩ := decideNonzero call bound flags stack
    by_cases zero : ∀ j < 4, word s i j = 0
    · rw [ite_eq_right (fun valid => valid.2 ((Sampling.words_all_zero_iff _).mp zero))] at eq
      rw [eq]
      intro more
      obtain ⟨f, last, post⟩ := retry zero more
      exact ⟨f, n, step.trans (test.trans last), post⟩
    · rw [ite_eq_left ⟨range, fun hz => zero ((Sampling.words_all_zero_iff _).mpr hz)⟩] at eq
      rw [eq]
      obtain ⟨f, last, post⟩ := accept _ eq zero
      exact ⟨f, n, step.trans (test.trans last), post⟩
  · rw [ite_eq_right range] at step
    rw [ite_eq_right (fun valid => range valid.1)] at eq
    rw [eq]
    intro more
    obtain ⟨f, last, post⟩ := retryRange call mid more stack
    exact ⟨f, mem, step.trans last, post⟩

end K256.Proofs.Generate.Generator.Sample
