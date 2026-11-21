import K256.Proofs.Sec1.Serialize.Assemble.Memory
import K256.Proofs.Sec1.Tactic.Lemma.Refine
import K256.Proofs.Sec1.Serialize.Coordinates.PackCall
import K256.Proofs.Common.Field.Repr
import K256.Proofs.Sec1.LIR.Fn1215e0
import K256.Proofs.Common.Lift.Generated.Values.Load

namespace K256.Proofs.Sec1.Serialize.Coordinates

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Sec1.LIR
open K256.Proofs.Common.Field

def Axis.normalizeSite : Axis → Label
  | .x => .l1215e0
  | .y => .l121643

def Axis.normalizeReturn : Axis → Word
  | .x => 0x121633
  | .y => 0x121682

def setupWrites (axis : Axis) (base : Word) : List MemoryRegion :=
  ⟨(base - 8).toNat, 8⟩ :: ⟨(base + 8).toNat, 40⟩ ::
    match axis with
    | .x => [⟨(base + 280).toNat, 32⟩]
    | .y => []

structure NormalizeSetup (axis : Axis) (code : CodeMap) (args : Values Value Reg.count)
    (mem : Ram) (base point dest flag : Word) (limbs : Limbs)
    (child : Values Value Reg.count) (written : Ram) : Prop where
  run : program.runBlock (dialect code) ⟨axis.normalizeSite, args, mem⟩ =
    .call ⟨.l114930, child, written⟩ (callFrame axis.packSite axis.normalizeReturn)
  rsp : child[4] = ⟨64, base - 8⟩
  src : child[6] = ⟨64, base + 8⟩
  dst : child[7] = ⟨64, base + 80⟩
  out : child[3] = ⟨64, dest⟩
  flag : child[5] = ⟨64, flag⟩
  point : child[14] = ⟨64, point⟩
  scratch : child[15] = ⟨64, base + 80⟩
  keeps : ∀ i : Fin Reg.count, i.val ∈ [10,11,12,13,22,39,50,51] → child[i] = args[i]
  frame : RamWriteFrame mem written (setupWrites axis base)
  slot : memLoad written (base - 8) 64 = axis.normalizeReturn
  words : WordsAt written (base + 8) 64 limbs

structure SerializerSaved (args : Values Value Reg.count) (written : Ram) (base : Word) : Prop where
  rbx : memLoad written (base + 280) 64 = args[3].get 64
  r14 : memLoad written (base + 288) 64 = args[14].get 64
  r15 : memLoad written (base + 296) 64 = args[15].get 64
  rbp : memLoad written (base + 304) 64 = args[5].get 64

open K256.Proofs.Sec1.Serialize.Assemble

private def copyLimbs (mem : Ram) (base ret : Word) (a : Limbs) : Ram :=
  let m4 := memStore mem (base + 40) a[4]
  let m3 := memStore m4 (base + 32) a[3]
  let m2 := memStore m3 (base + 24) a[2]
  let m1 := memStore m2 (base + 16) a[1]
  let m0 := memStore m1 (base + 8) a[0]
  memStore m0 (base - 8) ret

private def saveRegisters (mem : Ram) (base : Word) (args : Values Value Reg.count) : Ram :=
  let m5 := memStore mem (base + 304) (args[5].get 64)
  let m15 := memStore m5 (base + 296) (args[15].get 64)
  let m14 := memStore m15 (base + 288) (args[14].get 64)
  memStore m14 (base + 280) (args[3].get 64)

private theorem copiedSourceApart {code : CodeMap} {mem : Ram} {a b base point c d : Word}
    (stack : Writable code mem (base - 121) 433) (pointRead : Readable mem point 88)
    (apart : point.toNat + 88 ≤ (base - 8).toNat ∨ base.toNat + 312 ≤ point.toNat)
    (ha : a = base + c) (hb : b = point + d)
    (hstack : (c - (0 - 8)).toNat + 8 ≤ 320) (hpoint : d.toNat + 8 ≤ 88) :
    RangeApart a (64 / 8) b (64 / 8) := by
  have stackLow : (base - 8).toNat + 320 ≤ 2^32 :=
    (stack.readable.of_offsets (addr_sub base 8) (addr_sub base 121) (by decide)).low
  have baseNat : base.toNat = (base - 8).toNat + 8 :=
    toNat_of_offsets (n := 312) (addr_self base) (addr_sub base 8) stackLow (by decide)
  apply K256.Proofs.Refine.RangeApart.of_regions ha (addr_sub base 8) hb (addr_self point) stackLow pointRead.low
  · rcases apart with h | h
    · exact Or.inr h
    · exact Or.inl (by rw [baseNat] at h; omega)
  · exact ⟨hstack, by simpa only [show d - (0 : Word) = d from by bv_omega] using hpoint⟩

private theorem setupRegion {code : CodeMap} {mem : Ram} {a b base c d : Word} {len : Nat}
    (stack : Writable code mem (base - 121) 433)
    (ha : a = base + c) (hb : b = base + d)
    (h1 : (d - (0 - 121)).toNat + len ≤ 433)
    (h2 : (c - d).toNat + 8 ≤ len) : InRegion ⟨b.toNat, len⟩ a 8 := by
  have low := (stack.readable.of_offsets hb (addr_sub base 121) h1).low
  have addr := toNat_of_offsets ha hb low h2
  change b.toNat ≤ a.toNat ∧ a.toNat + 8 ≤ b.toNat + len ∧ a.toNat + 8 ≤ 2^64
  exact ⟨by omega, by omega, by omega⟩

private theorem copyLimbsFrame {code : CodeMap} {original mem : Ram} {base : Word} {a : Limbs}
    {regions : List MemoryRegion} (stack : Writable code original (base - 121) 433)
    (frame : RamWriteFrame original mem regions) (ret : Word)
    (slot : ⟨(base - 8).toNat, 8⟩ ∈ regions)
    (limbs : ⟨(base + 8).toNat, 40⟩ ∈ regions) :
    RamWriteFrame original (copyLimbs mem base ret a) regions := by
  unfold copyLimbs
  apply RamWriteFrame.memStore
  case hin =>
    exact ⟨_, slot, setupRegion stack (addr_sub base 8) (addr_sub base 8) (by decide) (by decide)⟩
  iterate 5
    apply RamWriteFrame.memStore
    case hin => exact ⟨_, limbs, setupRegion stack rfl rfl (by decide) (by decide)⟩
  exact frame

set_option hygiene false in
local macro "read_setup_word" : tactic =>
  `(tactic| simp
    (disch := (first
      | decide
      | exact RangeApart.of_offsets (addr_sub base 8) rfl (by decide)
      | exact RangeApart.of_offsets rfl (addr_sub base 8) (by decide)
      | exact RangeApart.of_offsets rfl rfl (by decide)))
    only [memLoad_memStore_same, memLoad_memStore_of_rangeApart, Lift.reduceAddOffset])

private theorem copyLimbsWords (mem : Ram) (base ret : Word) (a : Limbs) :
    WordsAt (copyLimbs mem base ret a) (base + 8) 64 a := by
  intro i hi
  have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
  rcases this with rfl | rfl | rfl | rfl | rfl <;>
    simp only [copyLimbs, wordAddr, Nat.reduceDiv, Nat.reduceMul, BitVec.add_zero] <;>
    read_setup_word

private theorem copyLimbsSlot (mem : Ram) (base ret : Word) (a : Limbs) :
    memLoad (copyLimbs mem base ret a) (base - 8) 64 = ret := by
  apply memLoad_memStore_same <;> decide

private theorem wordFromPoint {mem : Ram} {point : Word} {a : Limbs} {off : Nat}
    (words : WordsAt mem (point + BitVec.ofNat 64 off) 64 a) (i : Nat) (hi : i < 5) :
    memLoad mem (point + BitVec.ofNat 64 (off + 8 * i)) 64 = a[i] := by
  simpa only [wordAddr, Nat.reduceDiv, BitVec.ofNat_add, BitVec.add_assoc] using words i hi

private theorem savedRegisters {args : Values Value Reg.count} {mem : Ram} {base : Word}
    {a : Limbs} (ret : Word) :
    SerializerSaved args (copyLimbs (saveRegisters mem base args) base ret a) base := by
  constructor <;> simp only [copyLimbs, saveRegisters] <;> read_setup_word

private theorem saveRegistersFrame {code : CodeMap} {args : Values Value Reg.count} {mem : Ram}
    {base : Word} (stack : Writable code mem (base - 121) 433) :
    RamWriteFrame mem (saveRegisters mem base args) (setupWrites .x base) := by
  unfold saveRegisters
  iterate 4
    apply RamWriteFrame.memStore
    case hin =>
      exact ⟨_, List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self),
        setupRegion stack rfl rfl (by decide) (by decide)⟩
  exact RamWriteFrame.refl _ _

private theorem setupKeeps {args child : Values Value Reg.count}
    (h10 : child[10] = args[10]) (h11 : child[11] = args[11])
    (h12 : child[12] = args[12]) (h13 : child[13] = args[13]) (h22 : child[22] = args[22])
    (h39 : child[39] = args[39]) (h50 : child[50] = args[50]) (h51 : child[51] = args[51])
    (i : Fin Reg.count) (hi : i.val ∈ [10,11,12,13,22,39,50,51]) : child[i] = args[i] := by
  rcases i with ⟨i, _⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> assumption

private theorem subSetupRSP (base : Word) :
    (subSpec (base + 280) (280 : Word)).1 = base := by
  change base + 280 - 280 = base
  exact BitVec.add_sub_cancel _ _

private theorem setupLoadOk {mem : Ram} {point b d : Word}
    (pointRead : Readable mem point 88) (hb : b = point + d) (hd : d.toNat + 8 ≤ 88) :
    LoadOk mem b 8 :=
  LoadOk.of_offsets pointRead hb (addr_self point)
    (by simpa only [show d - (0 : Word) = d from by bv_omega] using hd)

private theorem setupStoreOk {code : CodeMap} {mem : Ram} {base block b c pc : Word}
    {len : Nat} {bytes : List UInt8} (stack : Writable code mem (base - 121) 433)
    (included : ∀ x ∈ codeRange block bytes, x ∈ code)
    (hb : b = base + c) (hc : (c - (0 - 121)).toNat + 8 ≤ 433)
    (hp : (pc - block).toNat + len ≤ bytes.length) : StoreOk code mem b 8 pc len :=
  storeOk_inBlock (stack.of_offsets hb (addr_sub base 121) hc) included hp

set_option hygiene false in
local macro "setup_access" : tactic =>
  `(tactic| (
    repeat first | apply loadOk_memStore | apply storeOk_memStore
    first
    | apply setupLoadOk pointRead rfl <;> decide
    | apply setupLoadOk pointRead (addr_self point) <;> decide
    | apply setupStoreOk stack included rfl <;> decide
    | apply setupStoreOk stack included (addr_sub base 8) <;> decide))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 2500000 in
theorem normalizeSetupX {code : CodeMap} {args : Values Value Reg.count} {mem : Ram}
    {base point dest : Word} {a : Limbs} (cover : ∀ x ∈ fnCode, x ∈ code)
    (rsp : args[4].get 64 = base + 312) (source : args[6].get 64 = point)
    (destReg : args[7].get 64 = dest) (flagReg : args[2].get 64 = 0)
    (stack : Writable code mem (base - 121) 433) (pointRead : Readable mem point 88)
    (pointApart : point.toNat + 88 ≤ (base - 8).toNat ∨ base.toNat + 312 ≤ point.toNat) (words : WordsAt mem point 64 a) :
    ∃ child written, NormalizeSetup .x code args mem base point dest 0 a child written ∧
      SerializerSaved args written base := by
  have included : ∀ x ∈ codeRange 0x1215e0 bytes_l1215e0, x ∈ code :=
    fun x hx => cover x (code_l1215e0 x hx)
  have h0 : memLoad mem point 64 = a[0] := by simpa only [wordAddr, Nat.mul_zero, BitVec.add_zero] using words 0 (by decide)
  have h1 : memLoad mem (point + 8) 64 = a[1] := words 1 (by decide)
  have h2 : memLoad mem (point + 16) 64 = a[2] := words 2 (by decide)
  have h3 : memLoad mem (point + 24) 64 = a[3] := words 3 (by decide)
  have h4 : memLoad mem (point + 32) 64 = a[4] := words 4 (by decide)
  refine ⟨?child, copyLimbs (saveRegisters mem base args) base 0x121633 a,
    ⟨?step, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, savedRegisters _⟩
  case step =>
    change program.runBlock _ ⟨.l1215e0, _, _⟩ = _
    cfg_eval [b_l1215e0_1, rsp, source, destReg, flagReg, subSetupRSP base]
    repeat
      refine (ite_eq_left ?_).trans ?_
      · setup_access
    simp (disch := first
        | exact copiedSourceApart stack pointRead pointApart rfl rfl (by decide) (by decide)
        | exact copiedSourceApart stack pointRead pointApart rfl (addr_self point) (by decide) (by decide))
      only [memLoad_memStore_of_rangeApart, h0, h1, h2, h3, h4]
    rfl
  all_goals
    first
    | rfl
    | exact setupKeeps rfl rfl rfl rfl rfl rfl rfl rfl
    | exact copyLimbsFrame stack (saveRegistersFrame stack) _ List.mem_cons_self
        (List.mem_cons_of_mem _ List.mem_cons_self)
    | exact copyLimbsSlot _ _ _ _
    | exact copyLimbsWords _ _ _ _

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1500000 in
theorem normalizeSetupY {code : CodeMap} {args : Values Value Reg.count} {mem : Ram}
    {base point dest flag : Word} {a : Limbs} (cover : ∀ x ∈ fnCode, x ∈ code)
    (rsp : args[4].get 64 = base) (source : args[14] = ⟨64, point⟩)
    (destReg : args[3] = ⟨64, dest⟩) (flagReg : args[5] = ⟨64, flag⟩)
    (stack : Writable code mem (base - 121) 433) (pointRead : Readable mem point 88)
    (pointApart : point.toNat + 88 ≤ (base - 8).toNat ∨ base.toNat + 312 ≤ point.toNat) (words : WordsAt mem (point + 40) 64 a) :
    ∃ child written, NormalizeSetup .y code args mem base point dest flag a child written := by
  have hsource := congrArg (Value.get 64) source
  change args[14].get 64 = point at hsource
  have included : ∀ x ∈ codeRange 0x121643 bytes_l121643, x ∈ code :=
    fun x hx => cover x (code_l121643 x hx)
  have h0 : memLoad mem (point + 40) 64 = a[0] := wordFromPoint words 0 (by decide)
  have h1 : memLoad mem (point + 48) 64 = a[1] := wordFromPoint words 1 (by decide)
  have h2 : memLoad mem (point + 56) 64 = a[2] := wordFromPoint words 2 (by decide)
  have h3 : memLoad mem (point + 64) 64 = a[3] := wordFromPoint words 3 (by decide)
  have h4 : memLoad mem (point + 72) 64 = a[4] := wordFromPoint words 4 (by decide)
  refine ⟨?child, copyLimbs mem base 0x121682 a, ?step, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  case step =>
    change program.runBlock _ ⟨.l121643, _, _⟩ = _
    cfg_eval [rsp, hsource]
    repeat
      refine (ite_eq_left ?_).trans ?_
      · setup_access
    simp (disch := exact copiedSourceApart stack pointRead pointApart rfl rfl (by decide) (by decide))
      only [memLoad_memStore_of_rangeApart, h0, h1, h2, h3, h4]
    rfl
  all_goals
    first
    | rfl
    | exact setupKeeps rfl rfl rfl rfl rfl rfl rfl rfl
    | exact source | exact destReg | exact flagReg
    | exact copyLimbsFrame stack (RamWriteFrame.refl _ _) _ List.mem_cons_self
        (List.mem_cons_of_mem _ List.mem_cons_self)
    | exact copyLimbsSlot _ _ _ _
    | exact copyLimbsWords _ _ _ _

end K256.Proofs.Sec1.Serialize.Coordinates
