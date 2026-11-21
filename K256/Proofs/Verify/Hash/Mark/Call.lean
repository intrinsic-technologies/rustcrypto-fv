import K256.Proofs.Verify.LIR.Program
import K256.Proofs.Verify.LIR.Generated.Values
import K256.Proofs.Verify.Hash.Mark.Copy
import K256.Proofs.Verify.Hash.Padding.Finalize

namespace K256.Proofs.Verify.Hash.Mark

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR

def resume : StackFrame Value Label signature Reg.count :=
  { target := .l1031c3, kept := #v[], arity := rfl, guard := some ⟨64, 0x1031c3⟩ }

set_option maxRecDepth 4096 in
theorem call {code : CodeMap} {args : Values Value Reg.count} {m : Ram} {sp : BitVec 64} (n : Nat)
    (rsp : args[4].get 64 = sp) (df : args[22].get 1 = 0)
    (copy : RepMovsOk code m 0 (sp + 248) (sp + 8) 13 8 0x103182 3)
    (len : LoadOk (copied m sp) (sp + 71) 1) (blocks : LoadOk (copied m sp) (sp + 104) 8)
    (tailSize : memLoad m (sp + 311) 8 = BitVec.ofNat 8 (n % 64))
    (count : memLoad m (sp + 344) 64 = BitVec.ofNat 64 (n / 64))
    (mark : StoreOk code (copied m sp) (sp + 8 + BitVec.ofNat 64 (n % 64)) 1 0x103197 6)
    (slot : StoreOk code (marked m sp (n % 64)) (sp - 8) 8 0x1031bd 6)
    (got : LoadOk (marked m sp (n % 64)) 0x203e10 8)
    (target : memLoad (marked m sp (n % 64)) 0x203e10 64 = 0x12a700) :
    ∃ a : Values Value Reg.count, program.runBlock (dialect code) ⟨.l103170, args, m⟩ =
        .call ⟨.l12a700, a, pushed m sp (n % 64)⟩ resume ∧
      a[2] = ⟨64, BitVec.ofNat 64 (63 - n % 64)⟩ ∧ a[3] = ⟨64, sp + 72⟩ ∧
      a[4] = ⟨64, sp - 8⟩ ∧ a[6] = ⟨64, 0⟩ ∧ a[7] = ⟨64, sp + 9 + BitVec.ofNat 64 (n % 64)⟩ ∧
      a[14] = ⟨64, BitVec.ofNat 64 (63 - n % 64)⟩ ∧
      a[15] = ⟨64, bswapSpec (BitVec.ofNat 64 (8*n))⟩ ∧
      (∀ r ∈ [5,9,10,11,12,13,22,39,50,51], ∀ hr : r < Reg.count, a[r] = args[r]) := by
  have hlen := (copied_load m sp 63 8 (by decide)).trans tailSize
  have hblocks := (copied_load m sp 96 64 (by decide)).trans count
  change memLoad (copied m sp) (sp + 71) 8 = _ at hlen
  change memLoad (copied m sp) (sp + 104) 64 = _ at hblocks
  have bound := Nat.mod_lt n (by decide : 0 < 64)
  have zext : (BitVec.ofNat 8 (n % 64)).setWidth 64 = BitVec.ofNat 64 (n % 64) := by
    apply BitVec.eq_of_toNat_eq
    simp only [BitVec.toNat_setWidth, BitVec.toNat_ofNat]
    omega
  have addr (k : BitVec 64) : sp + BitVec.ofNat 64 (n % 64) + k =
      sp + k + BitVec.ofNat 64 (n % 64) := by bv_omega
  refine ⟨?_, ?run, ?post⟩
  case run =>
    cfg_eval [rsp, df, copy, len, blocks, hlen, hblocks, zext, addr 8, mark, slot, got, target]
    rw [ite_eq_left (Or.inr trivial), ite_eq_left ⟨target, slot, got⟩]
    rfl
  case post =>
    refine ⟨?_, rfl, rfl, ?_, ?_, ?_, ?_, ?_⟩
    · exact congrArg (Value.mk 64) (remaining_xor _ bound)
    · rfl
    · exact congrArg (Value.mk 64) (addr 9)
    · exact congrArg (Value.mk 64) (remaining_xor _ bound)
    · exact congrArg (fun x => Value.mk 64 (bswapSpec x)) (length_word n)
    · intro r hr _
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

end K256.Proofs.Verify.Hash.Mark
