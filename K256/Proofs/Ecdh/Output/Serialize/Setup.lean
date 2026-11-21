import K256.Proofs.Ecdh.Transfer
import K256.Proofs.Common.SignatureRun
import K256.Proofs.Ecdh.LIR.Generated.Values
import K256.Proofs.Common.Field.Repr
import K256.Proofs.Sec1.Serialize.Coordinates.NormalizeSetup

namespace K256.Proofs.Ecdh.Output

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine Ecdh.LIR Common.Field

def fieldReturn (l : Label) (ret : Word) : StackFrame Value Label signature Reg.count :=
  ⟨l, #v[], rfl, some ⟨64,ret⟩⟩

open Sec1.Serialize.Assemble

private def setupMemory (m : Ram) (base : Word) (a : Values Value Reg.count) (w : Limbs) : Ram :=
  let savedR14 := memStore m (base + 96) (a[14].get 64)
  let savedRbx := memStore savedR14 (base + 88) (a[3].get 64)
  let m4 := memStore savedRbx (base + 40) w[4]
  let m3 := memStore m4 (base + 32) w[3]
  let m2 := memStore m3 (base + 24) w[2]
  let m1 := memStore m2 (base + 16) w[1]
  let m0 := memStore m1 (base + 8) w[0]
  memStore m0 (base - 8) (0x120398 : Word)

set_option hygiene false in
local macro "read_setup_memory" : tactic =>
  `(tactic| simp
    (disch := first
      | decide
      | exact RangeApart.of_offsets (addr_sub base 8) rfl (by decide)
      | exact RangeApart.of_offsets rfl (addr_sub base 8) (by decide)
      | exact RangeApart.of_offsets rfl rfl (by decide))
    only [setupMemory, memLoad_memStore_same, memLoad_memStore_of_rangeApart, Lift.reduceAddOffset])

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem normalizeSetup {a : Values Value Reg.count} {m : Ram} {base dst src : Word} {w : Limbs}
    (rsp : a[4].get 64 = base + 104) (rsi : a[6].get 64 = src) (rdi : a[7].get 64 = dst)
    (win : Writable Extracted.programImage m (base - 121) 433)
    (read : Readable m src 40) (sep : base.toNat + 112 ≤ src.toNat)
    (input : WordsAt m src 64 w) :
    ∃ b n, program.runBlock (dialect Extracted.programImage) ⟨.l120350,a,m⟩ =
        .call ⟨.l114930,b,n⟩ (fieldReturn .l120398 0x120398) ∧
      b[4] = ⟨64,base - 8⟩ ∧ b[6] = ⟨64,base + 8⟩ ∧ b[7] = ⟨64,base + 48⟩ ∧
      b[3] = ⟨64,dst⟩ ∧ b[14] = ⟨64,base + 48⟩ ∧ b[22] = a[22] ∧
      RamWriteFrame m n [⟨(base - 8).toNat,112⟩] ∧
      memLoad n (base + 88) 64 = a[3].get 64 ∧ memLoad n (base - 8) 64 = 0x120398 ∧
      WordsAt n (base + 8) 64 w := by
  have included : ∀ x ∈ codeRange 0x120350 bytes_l120350, x ∈ Extracted.programImage :=
    fun x hx => Common.fnCode_subset_programImage x (code_l120350 x hx)
  have stack : Writable Extracted.programImage m (base - 8) 112 :=
    win.of_offsets (addr_sub base 8) (addr_sub base 121) (by decide)
  have baseNat : base.toNat = (base - 8).toNat + 8 :=
    toNat_of_offsets (n := 1) (addr_self base) (addr_sub base 8) stack.readable.low (by decide)
  have loadGuard {j d : Word} (addr : j = src + d) (fits : (d - 0).toNat + 8 ≤ 40) :
      LoadOk m j 8 := LoadOk.of_offsets read addr (addr_self src) fits
  have storeGuard {j d pc : Word} {len : Nat} (addr : j = base + d)
      (fits : (d - (0 - 8)).toNat + 8 ≤ 112)
      (instr : (pc - 0x120350).toNat + len ≤ bytes_l120350.length) :
      StoreOk Extracted.programImage m j 8 pc len :=
    storeOk_inBlock (stack.of_offsets addr (addr_sub base 8) fits) included instr
  have sourceApart {j k d e : Word} (store : j = base + d) (load : k = src + e)
      (within : (d - (0 - 8)).toNat + 8 ≤ 112) (fits : (e - 0).toNat + 8 ≤ 40) :
      RangeApart j (64 / 8) k (64 / 8) :=
    RangeApart.of_regions store (addr_sub base 8) load (addr_self src)
      stack.readable.low read.low (Or.inl (by omega)) ⟨within, fits⟩
  have stackRegion {j d : Word} (addr : j = base + d)
      (fits : (d - (0 - 8)).toNat + 8 ≤ 112) :
      InRegion ⟨(base - 8).toNat, 112⟩ j 8 := by
    have lo := stack.readable.low
    have offset := toNat_of_offsets addr (addr_sub base 8) lo fits
    change (base - 8).toNat ≤ j.toNat ∧ j.toNat + 8 ≤ (base - 8).toNat + 112 ∧
      j.toNat + 8 ≤ 2^64
    omega
  have h0 : memLoad m src 64 = w[0] := by
    simpa only [wordAddr, Nat.mul_zero, BitVec.add_zero] using input 0 (by decide)
  have h1 : memLoad m (src + 8) 64 = w[1] := input 1 (by decide)
  have h2 : memLoad m (src + 16) 64 = w[2] := input 2 (by decide)
  have h3 : memLoad m (src + 24) 64 = w[3] := input 3 (by decide)
  have h4 : memLoad m (src + 32) 64 = w[4] := input 4 (by decide)
  have subRsp : (subSpec (base + 88) (88 : Word)).1 = base :=
    BitVec.add_sub_cancel _ _
  refine ⟨?child, setupMemory m base a w, ?run, ?_, ?_, ?_, ?_, ?_, ?_,
    ?frame, ?saved, ?slot, ?words⟩
  case run =>
    cfg_eval [b_l120350, rsp, rsi, rdi, subRsp]
    repeat
      refine (ite_eq_left ?_).trans ?_
      · repeat first | apply loadOk_memStore | apply storeOk_memStore
        first
        | apply loadGuard rfl <;> decide
        | apply loadGuard (addr_self src) <;> decide
        | apply storeGuard rfl <;> decide
        | apply storeGuard (addr_sub base 8) <;> decide
    simp (disch := first
        | exact sourceApart rfl rfl (by decide) (by decide)
        | exact sourceApart rfl (addr_self src) (by decide) (by decide))
      only [memLoad_memStore_of_rangeApart, h0, h1, h2, h3, h4]
    rfl
  case frame =>
    unfold setupMemory
    apply RamWriteFrame.memStore
    case hin => exact ⟨_, List.mem_singleton_self _, stackRegion (addr_sub base 8) (by decide)⟩
    iterate 7
      apply RamWriteFrame.memStore
      case hin => exact ⟨_, List.mem_singleton_self _, stackRegion rfl (by decide)⟩
    exact RamWriteFrame.refl _ _
  case saved => read_setup_memory
  case slot => exact memLoad_memStore_same _ _ _ (by decide) (by decide)
  case words =>
    intro i hi
    have : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 := by omega
    rcases this with rfl | rfl | rfl | rfl | rfl <;>
      simp only [wordAddr, Nat.reduceDiv, Nat.reduceMul, BitVec.add_zero] <;>
      read_setup_memory
  all_goals rfl

end K256.Proofs.Ecdh.Output
