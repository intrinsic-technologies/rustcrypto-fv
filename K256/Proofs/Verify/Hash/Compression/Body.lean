import K256.Proofs.Verify.Hash.Compression.BlockState
import K256.Proofs.Verify.Hash.Compression.InputWords
import K256.Proofs.Verify.Hash.Compression.Groups.Prefix
import K256.Proofs.Verify.Hash.Compression.Groups.BackEdge
import K256.Proofs.Verify.LIR.Program

namespace K256.Proofs.Verify.Hash.Compression

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

open Values K256.Proofs.Sec1.Affine.Uncompressed

private theorem addrOffset (p : BitVec 64) (n : Nat) (h : p.toNat + n < 2^64) :
    (p + BitVec.ofNat 64 n).toNat = p.toNat + n := by
  simp only [BitVec.toNat_add, BitVec.toNat_ofNat]
  rw [Nat.mod_eq_of_lt (a := n) (by omega), Nat.mod_eq_of_lt h]

private theorem slotOffsets : ∀ j : Fin 6, ((#v[48,8,40,32,24,16] : Vector (BitVec 64) 6)[j]).toNat ≤ 48 ∧
      8 ≤ ((#v[48,8,40,32,24,16] : Vector (BitVec 64) 6)[j]).toNat := by decide

variable {entry : CFG.Values Value Reg.count} {original : Ram} {sp dst src : BitVec 64}
    {initial : Array UInt32} {input : ByteArray}

attribute [local irreducible] prefixOperations b_l121930 b_l121930_166

theorem body (call : Call entry original sp dst src initial input)
    {index : Nat} {hash : Array UInt32} {args : CFG.Values Value Reg.count} {mem : Ram}
    (ready : LoopState entry original sp dst src (input.size / 64) index hash args mem)
    (more : index < input.size / 64) :
    ∃ args' mem', program.runBlock (dialect Extracted.programImage) ⟨.l121930, args, mem⟩ =
      .jump ⟨if index + 1 < input.size / 64 then .l121930 else .l1240c4, args', mem'⟩ ∧
      LoopState entry original sp dst src (input.size / 64) (index+1)
        (Reference.compress hash (blockBits input index)) args' mem' := by
  let stackBase := sp - 336
  let inputBase := src + BitVec.ofNat 64 (64*index)
  let ctx : ValueContext := ⟨stackBase, inputBase, fun off =>
    memLoad original (inputBase + BitVec.ofNat 64 off) 32⟩
  let s := blockValues args mem stackBase
  have sp0 : s.regs 4 = ctx.stackPointer := ready.rsp
  have ip0 : s.regs 6 = ctx.inputPointer := ready.rsi
  have matching : StackMatches ctx.stackPointer s mem := fun _ _ _ => rfl
  have stack := call.stackWritable.of_frame ready.writes
  have dep := call.depth
  have low := call.inputReadable.low
  have base : stackBase.toNat = sp.toNat - 336 :=
    BitVec.toNat_sub_of_le (BitVec.le_def.mpr dep)
  have inp : inputBase.toNat = src.toNat + 64*index := addrOffset _ _ (by omega)
  have srcOk : Readable mem inputBase 64 := (call.inputReadable.of_frame ready.writes).sub
      (by rw [inp]; omega) (by rw [inp]; omega)
  have apart : stackBase.toNat + 336 ≤ inputBase.toNat ∨ inputBase.toNat + 64 ≤ stackBase.toNat := by
    have sep := call.inputStack
    rw [inp, base]
    omega
  have inputWords (off : Nat) (bound : off + 4 ≤ 64) :
      memLoad mem (ctx.inputPointer + BitVec.ofNat 64 off) 32 = ctx.inputWords off := by
    apply ready.writes.memLoad_eq
    have addr := addrOffset inputBase off (by omega)
    change Outside _ (inputBase + BitVec.ofNat 64 off) 4
    refine ⟨by rw [addr]; omega, ?_⟩
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    change _ ≤ sp.toNat - 336 ∨ sp.toNat - 336 + 336 ≤ _
    rw [addr]
    omega
  have cover := fun x hx => Common.fnCode_subset_programImage x (code_l121930 x hx)
  have saved : preservedAt args entry := fun i _ hi h => ready.preserved ⟨i,hi⟩ h
  obtain ⟨b, m', ev, storeEq, regs, keep⟩ := prefixSteps _ cover entry args mem ctx s stack
    srcOk apart inputWords matching sp0 ip0 (blockRegisters args mem stackBase) saved
  subst m'
  have valid (op : Values.Op) (h : op ∈ prefixOperations) : op.validSpills :=
    operations_valid op (operations_split ▸ List.mem_append_left group166 h)
  have frame := spillRun_frame ctx prefixOperations s mem valid stack.readable.low
  have slots := spillRun_matches ctx prefixOperations s mem valid matching
  obtain ⟨sp1, ip1⟩ := prefixPointers ctx s sp0 ip0
  have lowStack := stack.readable.low
  have safe {p : BitVec 64} (bounds : (p.toNat ≥ stackBase.toNat + 192 ∧
      p.toNat + 8 ≤ stackBase.toNat + 208) ∨
      (stackBase.toNat + 288 ≤ p.toNat ∧ p.toNat + 8 ≤ stackBase.toNat + 336)) :
      Outside (spillRegions ctx.stackPointer) p 8 := by
    change stackBase.toNat + 336 ≤ 2^32 at lowStack
    refine ⟨by omega, ?_⟩
    intro reg hr
    simp only [spillRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> change _ ≤ _ ∨ _ ≤ _ <;> dsimp only [ctx] <;> omega
  have safeAt (off : Nat) (h₁ : 192 ≤ off) (h₂ : off + 8 ≤ 208) :
      Outside (spillRegions ctx.stackPointer) (stackBase + BitVec.ofNat 64 off) 8 := by
    apply safe
    left
    rw [addrOffset _ _ (by change stackBase.toNat + 336 ≤ 2^32 at lowStack; omega)]
    omega
  have limit := (frame.memLoad_eq (k := 64) (safeAt 200 (by decide) (by decide))).trans ready.limit
  obtain ⟨out, jump, rsp, rsi, outWords, outKeep⟩ := backEdge Extracted.programImage b entry _ ctx _ _
    (stack.readable.of_frame frame) slots limit sp1 ip1 regs keep
  have advance : ctx.inputPointer + 64 = src + BitVec.ofNat 64 (64*(index+1)) := by
    change src + BitVec.ofNat 64 (64*index) + 64 = _
    rw [Nat.mul_add, BitVec.ofNat_add, BitVec.add_assoc]
    rfl
  have branch : (ctx.inputPointer + 64 ≠ src + BitVec.ofNat 64 (64*(input.size/64))) ↔
      index+1 < input.size / 64 := by
    rw [advance]
    have modulus (j : Nat) (hj : j ≤ input.size / 64) : (BitVec.ofNat 64 (64*j)).toNat = 64*j :=
      Nat.mod_eq_of_lt (by omega)
    constructor
    · intro h
      have h' : index+1 ≠ input.size/64 := fun eq => h (by rw [eq])
      omega
    · intro h eq
      have vals := congrArg BitVec.toNat ((BitVec.add_right_inj src).mp eq)
      rw [modulus _ (by omega), modulus _ (by omega)] at vals
      omega
  have labels : (if ctx.inputPointer + 64 ≠ src + BitVec.ofNat 64 (64*(input.size/64))
        then Label.l121930 else Label.l1240c4) =
      (if index+1 < input.size / 64 then Label.l121930 else Label.l1240c4) := by
    by_cases h : index+1 < input.size / 64
    · rw [ite_eq_left h, ite_eq_left (branch.mpr h)]
    · rw [ite_eq_right h, ite_eq_right (fun hn => h (branch.mp hn))]
  refine ⟨out, _, ev.trans (jump.trans (congrArg (fun lbl : Label =>
    Transfer.jump (results := Reg.count) (signature := signature) ⟨lbl, out, spillRun ctx prefixOperations s mem⟩) labels)), rsp, rsi.trans advance,
    compress_size _ _, ?_, ready.writes.trans frame ?_, ?_, limit, ?_, ?_⟩
  · intro i
    have inputs (j : Nat) (hj : j < 16) := input_word call.inputBytes more j hj
    have result := Values.Correctness.hashState_correct hash (blockBits input index) ctx s
      inputs (blockHash ready.words)
    rw [← operations_split, run_append] at result
    exact (outWords i).trans (registersOfHash result i)
  · intro r hr
    refine ⟨_, List.mem_singleton_self _, ?_⟩
    simp only [spillRegions, List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl <;> dsimp only [ctx] <;> omega
  · exact (frame.memLoad_eq (safeAt 192 (by decide) (by decide))).trans ready.destination
  · intro i
    let off := (#v[48,8,40,32,24,16] : Vector (BitVec 64) 6)[i]
    have bounds : off.toNat ≤ 48 ∧ 8 ≤ off.toNat := slotOffsets i
    have addr : (sp-off).toNat = sp.toNat - off.toNat :=
      BitVec.toNat_sub_of_le (BitVec.le_def.mpr (by omega))
    apply (frame.memLoad_eq (safe (p := sp-off) (Or.inr (by rw [addr, base]; omega)))).trans
    exact ready.slots i
  · intro i hi
    exact outKeep i i.isLt i.isLt hi

end K256.Proofs.Verify.Hash.Compression
