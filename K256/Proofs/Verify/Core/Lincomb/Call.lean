import K256.Proofs.Verify.Core.Memory
import K256.Proofs.Verify.LIR.Generated.Values

namespace K256.Proofs.Verify.Core.Lincomb

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC

abbrev resume : StackFrame Value Label signature Reg.count :=
  ⟨.l10526c, #v[], rfl, some ⟨64, 0x10526c⟩⟩

abbrev push (m : Ram) (fr : Activation) :=
  memStore m (localSp fr - 8) (0x10526c : BitVec 64)

structure Arguments (fr : Activation) (b c : Registers) : Prop where
  sp : c[4] = ⟨64, localSp fr - 8⟩
  dst : c[7] = ⟨64, localSp fr + 8⟩
  u : c[6] = ⟨64, localSp fr + 384⟩
  v : c[2] = ⟨64, localSp fr + 416⟩
  peer : c[1] = ⟨64, fr.rsi⟩
  result : c[13] = ⟨64, localSp fr + 8⟩
  keep : ∀ i : Fin Reg.count, i.val ∈ [3,5,9,10,11,12,14,15,22,39,50,51] → c[i] = b[i]

theorem call {fr : Activation} {a b : Registers} {p : Curve.Point} {digest : ByteArray}
    {r s u v : Nat} {m : Ram} (e : Entry fr a p digest r s) (h : Products fr b m u v r) :
    ∃ c, program.runBlock (dialect Extracted.programImage) ⟨.l105256, b, m⟩ =
      .call ⟨.l10fb20, c, push m fr⟩ resume ∧ Arguments fr b c := by
  have stack := e.stack.of_frame h.frame
  have slot : Writable Extracted.programImage m (localSp fr - 8) 8 :=
    stack.of_offsets (x := fr.rsp) (c := -496) (d := -12456) (by unfold localSp; bv_omega)
      (by rw [e.stackBase]; bv_omega) (by decide)
  have guard : StoreOk Extracted.programImage m (localSp fr - 8) 8 0x105267 5 :=
    ParseSignature.storeOk_of_codeRange (off := 17) slot
      (fun x hx => Common.fnCode_subset_programImage x (code_l105256 x hx)) (by decide)
  have sp : b[4].get 64 = localSp fr := congrArg (Value.get 64) h.sp
  have uPtr : b[12].get 64 = localSp fr + 384 := congrArg (Value.get 64) h.uPtr
  have vPtr : b[15].get 64 = localSp fr + 416 := congrArg (Value.get 64) h.vPtr
  have key : b[14].get 64 = fr.rsi := congrArg (Value.get 64) h.key
  refine ⟨?_, ?run, ?post⟩
  case run =>
    cfg_eval [sp, uPtr, vPtr, key, guard]
    rfl
  case post =>
    refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
    intro ⟨i, hi⟩ live
    simp only [List.mem_cons, List.not_mem_nil, or_false] at live
    rcases live with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

end K256.Proofs.Verify.Core.Lincomb
