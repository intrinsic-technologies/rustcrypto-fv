import K256.Proofs.Generate.Generator.Multiply.Prepare.Accumulator.CallBlocks
import K256.Proofs.Generate.Generator.Multiply.Prepare.Copy

namespace K256.Proofs.Generate.Generator.Multiply.Prepare.Accumulator

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR

set_option maxRecDepth 2048 in
theorem copyTable {a : Registers} {m : Ram} {src dst rsp ret : BitVec 64}
    (rd : a[7].get 64 = dst) (rs : a[6].get 64 = src) (count : a[2].get 64 = 960)
    (stack : a[4].get 64 = rsp) (df : a[22].get 1 = 0)
    (align : dst.toNat % 8 = 0) (args : ParseSignature.ArgumentWidths a)
    (read : Readable m src 960) (write : Writable Extracted.programImage m dst 960)
    (apart : src.toNat + 960 ≤ dst.toNat ∨ dst.toNat + 960 ≤ src.toNat)
    (slot : LoadOk (memCopy m dst src 960) rsp 8)
    (tag : memLoad (memCopy m dst src 960) rsp 64 = ret) (small : ret.toNat < 2^32) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l12a820,a,m⟩,[]⟩ out ∧
      out.tag = some ⟨64,ret⟩ ∧ out.store = memCopy m dst src 960 ∧
      ParseSignature.ArgumentWidths out.values ∧ out.values[4] = ⟨64,rsp+8⟩ ∧
      ∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15,22,39,50,51] → out.values[i] = a[i] := by
  have mov : RepMovsOk Extracted.programImage m 0 src dst 120 8 0x12a843 3 :=
    copyGuard read (by slot_guard using code_l12a820) apart
  have low : (memLoad (memCopy m dst src 960) rsp 64).toNat < 2^32 := tag ▸ small
  have headBytes : (-(dst.setWidth 32) &&& 7) = 0 := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_and, BitVec.toNat_neg, BitVec.toNat_setWidth]
    change (((2^32 - dst.toNat % 2^32) % 2^32) &&& (2^3 - 1)) = 0
    rw [Nat.and_two_pow_sub_one_eq_mod]
    omega
  have empty (n : Ram) (t s : BitVec 64) : memCopy n t s 0 = n := rfl
  have w : (0 : BitVec 32).setWidth 64 = 0 := rfl
  have cf : (cmpSpec (960 : BitVec 64) 0).CF = false := by decide +kernel
  have mid : ((960 : BitVec 64) - 0) >>> 3 = 120 := by decide +kernel
  have tail : ((((960 : BitVec 64) - 0).setWidth 32) &&& 7).setWidth 64 = 0 := by decide +kernel
  refine ⟨?out, .done ?run, ?tag, ?mem, ?widths, ?rsp, ?keep⟩
  case run =>
    have block : program.runBlock (dialect Extracted.programImage) ⟨.l12a820,a,m⟩ = .returned ?out := by
      generate_block [rd,rs,count,stack,df]
      simp only [headBytes,w,cf,Bool.false_eq_true,ite_false,mid,tail,
        BitVec.reduceToNat,BitVec.add_zero,empty,Nat.reduceMul,mov,or_true,true_or,ite_true,slot,low,and_self]
      rfl
    rw [Program.step,block]
    rfl
  case tag => exact congrArg (fun v => some (⟨64,v⟩ : Value)) tag
  case mem => rfl
  case widths =>
    rintro ⟨i,h⟩ hi
    have w := args ⟨i,h⟩ hi
    simp only [Activation.argumentNumbers,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl <;> first | rfl | exact w
  case rsp => rfl
  case keep =>
    rintro ⟨i,h⟩ hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

end K256.Proofs.Generate.Generator.Multiply.Prepare.Accumulator
