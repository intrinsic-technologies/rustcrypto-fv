import K256.Proofs.Common.Tactic
import K256.Proofs.Verify.LIR.Defs17
import K256.Proofs.Verify.LIR.Generated.Values
import K256.Proofs.Common.Lift.Generated.Values.Load
import K256.Proofs.Common.Lift.Generated.Values.Store2
import K256.Proofs.Verify.Hash.Compression.Spills

namespace K256.Proofs.Verify.Hash.Compression
open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  K256.Proofs.Sec1.Affine.Uncompressed
open Values

def registersAgree {n : Nat} (a : CFG.Values Value n) (s : Compression.Values) :
    List (Fin n × BitVec 5) → Prop
  | [] => True
  | (i,r) :: rest => a[i.val].get 64 = s.regs r ∧ registersAgree a s rest

def GroupStep {n k : Nat} (block : Block Lift.Op Label signature Reg.count n)
    (tail : Block Lift.Op Label signature Reg.count k) (ops : List Values.Op)
    (before : List (Fin n × BitVec 5)) (after : List (Fin k × BitVec 5))
    (pointers : ValueContext → Compression.Values → Prop) : Prop :=
  ∀ (code : CodeMap) (_cover : ∀ x ∈ codeRange 0x121930 bytes_l121930, x ∈ code)
    (orig : CFG.Values Value Reg.count) (a : CFG.Values Value n) (m : Ram)
    (ctx : ValueContext) (s : Compression.Values),
    Writable code m ctx.stackPointer 336 → Readable m ctx.inputPointer 64 →
    (ctx.stackPointer.toNat + 336 ≤ ctx.inputPointer.toNat ∨
      ctx.inputPointer.toNat + 64 ≤ ctx.stackPointer.toNat) →
    (∀ off, off + 4 ≤ 64 → memLoad m (ctx.inputPointer + BitVec.ofNat 64 off) 32 = ctx.inputWords off) →
    StackMatches ctx.stackPointer s m →
    s.regs 4 = ctx.stackPointer → pointers ctx s → registersAgree a s before → preservedAt a orig →
    ∃ b m', block.eval (dialect code) a m = tail.eval (dialect code) b m' ∧
      m' = spillRun ctx ops s m ∧ registersAgree b (run ctx ops s) after ∧ preservedAt b orig

syntax "compression_group" "[" Lean.Parser.Tactic.simpLemma,* "]"
  ident ident ident
  "[" Lean.Parser.Tactic.simpLemma,* "]"
  "[" Lean.Parser.Tactic.simpLemma,* "]"
  "[" Lean.Parser.Tactic.simpLemma,* "]" : tactic

macro_rules
  | `(tactic| compression_group [$ds,*] $ar:ident $cv:ident $sv:ident
      [$ads,*] [$hyps,*] [$vals,*]) =>
    `(tactic| (
      refine ⟨?_, ?_, ?ev, ?mem, ?regs, ?keep⟩
      case ev =>
        arithmetic_prefix [BitVec.add_zero, $ads,*]
        repeat' (refine Eq.trans (ite_eq_left ?_) ?_; slot_guard using $cv)
        rfl
      case mem =>
        simp -failIfUnchanged only [$ds,*, List.take, List.drop, spillRun, Op.spill,
          Values.Op.eval, Source.read64, Source.read32, read32, read64, write32, write64, writeReg,
          Binary.apply, BitVec.reduceEq, ↓reduceIte,
          BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq, $hyps,*]
        all_goals segment_words [$hyps,*]
        all_goals simp -failIfUnchanged only [$vals,*, bswap32] <;> rfl
      case regs =>
        simp only [$ar:ident, registersAgree, arithmeticIndex, $ds,*, List.take, List.drop, run,
          Values.Op.eval, Source.read64, Source.read32, read32, read64, write32, write64, writeReg,
          Binary.apply, BitVec.reduceEq, ↓reduceIte,
          BitVec.setWidth_setWidth_of_le _ (by decide : 32 ≤ 64), BitVec.setWidth_eq, $hyps,*]
        repeat' apply And.intro
        all_goals first | exact True.intro |
          (simp -failIfUnchanged only [↓arithmeticRead, arithmeticIndex, cfg_eval]
           all_goals segment_words [$hyps,*]
           all_goals simp -failIfUnchanged only [$vals,*, bswap32] <;> rfl)
      case keep =>
        intro i hi ho hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with h | h | h | h <;> subst i <;> (try simp only [↓arithmeticRead]) <;>
          exact $sv _ (by decide) (by decide) (by decide)))

def firstGroup := Values.Program.part00.take 20

def initialRegisters : List (Fin 53 × BitVec 5) := [(0,0), (1,1), (2,2), (3,3), (4,4), (5,5), (6,6), (7,7), (8,8), (9,9), (10,10), (11,11), (12,12), (13,13), (14,14), (15,15)]

def firstRegisters : List (Fin 89 × BitVec 5) := [(81,0), (87,1), (2,2), (3,3), (4,4), (5,5), (72,6), (63,7), (8,8), (61,9), (10,10), (58,11), (12,12), (76,13), (56,14), (54,15)]

set_option maxHeartbeats 850000 in
set_option linter.unusedSimpArgs false in
theorem firstGroup_step : GroupStep b_l121930 b_l121930_1 firstGroup initialRegisters firstRegisters
    (fun c s => s.regs 6 = c.inputPointer) := by
  intro code cover orig a m ctx s stack src apart inputWords stackWords sp ip regs saved
  simp only [initialRegisters, registersAgree, arithmeticIndex] at regs
  obtain ⟨r0, r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12, r13, r14, r15, _⟩ := regs
  have input0 := inputWords 0 (by decide)
  have input4 := inputWords 4 (by decide)
  simp only [BitVec.ofNat_eq_ofNat, BitVec.add_zero] at input0 input4
  compression_group [firstGroup, Values.Program.part00] firstRegisters cover saved
    [show a[4].get 64 = ctx.stackPointer from r4.trans sp,
      show a[6].get 64 = ctx.inputPointer from r6.trans ip]
    [sp, ip]
    [← r0, ← r1, ← r2, ← r3, ← r4, ← r5, ← r6, ← r7, ← r8, ← r9, ← r10,
      ← r11, ← r12, ← r13, ← r14, ← r15, ← sp, ← ip, ← input0, ← input4]

end K256.Proofs.Verify.Hash.Compression
