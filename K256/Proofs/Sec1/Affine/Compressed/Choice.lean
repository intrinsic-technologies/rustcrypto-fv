import K256.Proofs.Sec1.Serialize.Choice
import K256.Proofs.Sec1.Serialize.Coordinates.PackCall
import K256.Proofs.Sec1.LIR.Generated.Values
import K256.Proofs.Common.Lift.Generated.Values.Load

namespace K256.Proofs.Sec1.Affine.Compressed

open Prelude X86 X86.Machine X86.UserProcess X86Proofs
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Sec1.LIR
open K256.Proofs.Sec1.Serialize.Coordinates

inductive ChoiceSite where
  | canonical | xorParity | equalParity

namespace ChoiceSite

def site : ChoiceSite → Label
  | .canonical => .l120653
  | .xorParity => .l120dff
  | .equalParity => .l120e0b

def resume : ChoiceSite → Label
  | .canonical => .l12065f
  | .xorParity => .l120e0b
  | .equalParity => .l120e17

def ret : ChoiceSite → BitVec 64
  | .canonical => 0x12065f
  | .xorParity => 0x120e0b
  | .equalParity => 0x120e17

def result (site : ChoiceSite) (x want : BitVec 8) : BitVec 8 :=
  match site with
  | .xorParity => x ^^^ want
  | _ => ~~~x &&& 1

theorem pass (k : ChoiceSite) (code : CodeMap) (args : Values Value Reg.count) (mem : Ram)
    (sp : BitVec 64) (cover : ∀ x ∈ fnCode, x ∈ code)
    (rsp : args[4].get 64 = sp) (stack : Writable code mem (sp - 9) 9)
    (readParity : k = .xorParity → LoadOk mem (sp + 108) 1) :
    ∃ (regs : Values Value Reg.count) (m : Ram), (program.sem (dialect code)).Reaches ⟨⟨k.site, args, mem⟩, []⟩
        ⟨⟨k.resume, regs, m⟩, []⟩ ∧
      regs[0] = ⟨64, (k.result ((args[0].get 64).setWidth 8) (memLoad mem (sp+108) 8)).setWidth 64⟩ ∧
      regs[4] = ⟨64, sp⟩ ∧ RamWriteFrame mem m [⟨(sp-9).toNat, 9⟩] ∧
      (∀ i : Fin 53, i.val ∈ [3,5,12,13,14,15,22,39,50,51] → regs[i] = args[i]) := by
  let w := memStore mem (sp - 8) k.ret
  have slot : Writable code mem (sp - 8) 8 :=
    stack.of_offsets (addr_sub sp 8) (addr_sub sp 9) (by decide)
  have call : ∃ next, program.runBlock (dialect code) ⟨k.site, args, mem⟩ =
      .call ⟨.l127d50, next, w⟩ (callFrame k.resume k.ret) ∧
      next[4].get 64 = sp - 8 ∧ (next[7].get 64).setWidth 8 =
        k.result ((args[0].get 64).setWidth 8) (memLoad mem (sp+108) 8) ∧
      ∀ i : Fin 53, i.val ∈ [3,5,12,13,14,15,22,39,50,51] → next[i] = args[i] := by
    dsimp only [w]
    cases k
    case' canonical =>
      have hs : StoreOk code mem (sp - 8) 8 0x12065a 5 :=
        ParseSignature.storeOk_of_codeRange (off := 7) slot (fun e he => cover e (code_l120653 e he)) (by decide)
      refine ⟨?_, ?ev, ?post⟩
      case ev =>
        change program.runBlock _ ⟨.l120653, _, _⟩ = _
        cfg_eval [rsp, hs]
        rfl
    case' xorParity =>
      have hs : StoreOk code mem (sp - 8) 8 0x120e06 5 :=
        ParseSignature.storeOk_of_codeRange (off := 7) slot (fun e he => cover e (code_l120dff e he)) (by decide)
      have hp := readParity rfl
      refine ⟨?_, ?ev, ?post⟩
      case ev =>
        change program.runBlock _ ⟨.l120dff, _, _⟩ = _
        cfg_eval [rsp, hs, hp]
        rfl
    case' equalParity =>
      have hs : StoreOk code mem (sp - 8) 8 0x120e12 5 :=
        ParseSignature.storeOk_of_codeRange (off := 7) slot (fun e he => cover e (code_l120e0b e he)) (by decide)
      refine ⟨?_, ?ev, ?post⟩
      case ev =>
        change program.runBlock _ ⟨.l120e0b, _, _⟩ = _
        cfg_eval [rsp, hs]
        rfl
    all_goals
      refine ⟨rfl, ?value, ?kept⟩
      case value =>
        change ((BitVec.setWidth 8 (mergeGPR 8 _ _)).setWidth 64).setWidth 8 = _
        simp [result, setWidth_mergeGPR8]
      case kept =>
        intro ⟨i, hi⟩ h
        simp only [List.mem_cons, List.not_mem_nil, or_false] at h
        rcases h with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl
  obtain ⟨next, hcall, hs, hv, hk⟩ := call
  have t : memLoad w (sp - 8) 64 = k.ret := memLoad_memStore_same _ _ _ (by decide) (by decide)
  have scratch : Writable code w (sp - 8 - 1) 1 := by
    have eq : sp - 8 - 1 = sp - 9 := by bv_omega
    rw [eq]
    exact (stack.memStore _ k.ret).sub (Nat.le_refl _) (by omega)
  have hr := slot.readable.memStore (sp - 8) k.ret
  obtain ⟨o, he, htag, hsp, hax, hf, keep⟩ := Serialize.choiceBlock
    (fun e h => cover e (code_l127d50 e h)) hs scratch hr (by rw [t]; cases k <;> decide)
  have run : program.Exec (dialect code) ⟨⟨.l127d50, next, w⟩, []⟩ o :=
    .done (by simp only [Program.step, he, Transfer.next])
  have addr : (sp - 8).toNat = (sp - 9).toNat + 1 := by
    have h := toNat_of_offsets (addr_sub sp 8) (addr_sub sp 9) stack.readable.low (n := 8) (by decide)
    rwa [show (((0 - 8) - (0 - 9) : BitVec 64).toNat) = 1 by decide +kernel] at h
  have wp : RamWriteFrame mem w [⟨(sp - 9).toNat, 9⟩] := by
    apply (RamWriteFrame.refl _ _).memStore
    have low := stack.readable.low
    refine ⟨_, List.mem_cons_self, ?_⟩
    change (sp-9).toNat ≤ (sp-8).toNat ∧ (sp-8).toNat + 8 ≤ (sp-9).toNat + 9 ∧ _
    omega
  have frm := wp.trans hf (by
    intro r h
    rcases List.mem_singleton.mp h with rfl
    refine ⟨_, List.mem_cons_self, ?_, ?_⟩
    · change (sp - 9).toNat ≤ (sp - 8 - 1).toNat
      rw [show sp - 8 - 1 = sp - 9 by bv_omega]
      exact Nat.le_refl _
    · change (sp - 8 - 1).toNat + 1 ≤ (sp - 9).toNat + 9
      rw [show sp - 8 - 1 = sp - 9 by bv_omega]
      omega)
  refine ⟨o.values, o.store, reaches_call hcall run (htag.trans (congrArg (fun x => some (Value.mk 64 x)) t)), ?_,
    ?_, frm, ?_⟩
  · rwa [hv] at hax
  · rwa [BitVec.sub_add_cancel] at hsp
  · intro i hi
    apply Eq.trans (keep i ?_) (hk i hi)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
    rcases hi with h|h|h|h|h|h|h|h|h|h <;> simp [h]

end ChoiceSite
end K256.Proofs.Sec1.Affine.Compressed
