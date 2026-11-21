import K256.Proofs.Sec1.LIR.Program
import K256.Proofs.Common.Lift.Generated.Values.Register1
import K256.Proofs.Common.Lift.Generated.Values.Register2
import K256.Proofs.Common.Lift.Generated.Values.Register3
import K256.Proofs.Common.Lift.Generated.Values.Register4
import K256.Proofs.Common.Lift.Generated.Values.Load

import K256.Proofs.ParseSignature.Memory
import K256.Proofs.Common.Lift.Generated.Values.Store2

namespace K256.Proofs.Sec1.Serialize

open Prelude K256.Proofs.Refine X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift LIR

theorem choiceBlock {code : CodeMap} {args : Vector Value 53} {m : Ram} {sp : BitVec 64}
    (hcode : ∀ x ∈ codeRange 0x127d50 bytes_l127d50, x ∈ code)
    (rsp : Value.get 64 args[4] = sp) (stack : Writable code m (sp - 1) 1)
    (slot : Readable m sp 8) (low : (memLoad m sp 64).toNat < 2^32) :
    ∃ out : Output Value Ram Reg.count,
      program.runBlock (dialect code) ⟨.l127d50, args, m⟩ = .returned out ∧
      out.tag = some ⟨64, memLoad m sp 64⟩ ∧ out.values[4] = ⟨64, sp + 8⟩ ∧
      out.values[0] = ⟨64, ((Value.get 64 args[7]).setWidth 8).setWidth 64⟩ ∧
      RamWriteFrame m out.store [⟨(sp - 1).toNat, 1⟩] ∧
      ∀ i : Fin 53, i.val ∈ [1,2,3,5,6,7,8,9,10,11,12,13,14,15,22,39,50,51] →
        out.values[i] = args[i] := by
  let byte := (Value.get 64 args[7]).setWidth 8
  let written := memStore m (sp - 1) byte
  have hs : StoreOk code m (sp - 1) 1 0x127d54 4 :=
    ParseSignature.storeOk_of_codeRange (off := 4) stack hcode (by decide)
  have hb : LoadOk written (sp - 1) 1 :=
    let r := stack.readable.memStore (sp - 1) byte
    ⟨r.low, r.present⟩
  have hv : memLoad written (sp - 1) 8 = byte :=
    memLoad_memStore_same _ _ _ (by decide) (by decide)
  have hr : LoadOk written sp 8 :=
    let r := slot.memStore (sp - 1) byte
    ⟨r.low, r.present⟩
  have hret : memLoad written sp 64 = memLoad m sp 64 := by
    exact memLoad_memStore_of_rangeApart _ _ _ _ _ (RangeApart.of_offsets
      (addr_sub sp 1) (addr_self sp) (by decide))
  have hf : RamWriteFrame m written [⟨(sp - 1).toNat, 1⟩] := by
    apply (RamWriteFrame.refl _ _).memStore
    exact ⟨_, List.mem_cons_self .., Nat.le_refl _, Nat.le_refl _,
      by have := stack.readable.low; change (sp - 1).toNat + 1 ≤ 2^64; omega⟩
  dsimp only [written, byte] at hb hv hr hret hf
  refine ⟨?out, ?step, ?post⟩
  case step =>
    cfg_eval
    simp only [rsp, hs, hb, hv, hr, hret, low, and_self, ite_true]
    rfl
  case post =>
    refine ⟨rfl, rfl, rfl, hf, ?_⟩
    intro ⟨i, _⟩ hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

end K256.Proofs.Sec1.Serialize
