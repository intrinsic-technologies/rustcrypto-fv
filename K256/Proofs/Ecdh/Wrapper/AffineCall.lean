import K256.Proofs.Ecdh.LIR.EcdhDiffieHellman
import K256.Proofs.Common.Refine.Lemma.Store

namespace K256.Proofs.Ecdh.Wrapper

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine Ecdh.LIR

def callFrame (target : Label) (rip : BitVec 64) : StackFrame Value Label signature Reg.count :=
  { target, kept := #v[], arity := rfl, guard := some ⟨64, rip⟩ }

def affineArgs (a : Vector Value Reg.count) (sp : BitVec 64) : Vector Value Reg.count :=
  (((a.set 4 ⟨64, sp - 8⟩).set 6 ⟨64, sp + 0x158⟩).set 7 ⟨64, sp + 0x1058⟩).set 14
    ⟨64, sp + 0x1058⟩

theorem affineCallBlock {code : CodeMap} {a : Vector Value Reg.count} {mem : Ram} {sp : BitVec 64}
    (rsp : a[4].get 64 = sp) (r12 : a[12].get 64 = sp + 0x158)
    (store : StoreOk code mem (sp - 8) 8 0x101b08 5) :
    program.runBlock (dialect code) ⟨.l101afa, a, mem⟩ = .call
      ⟨.l10fe50, affineArgs a sp, memStore mem (sp - 8) (0x101b0d : BitVec 64)⟩
      (callFrame .l101b0d 0x101b0d) := by
  cfg_eval
  simp only [rsp, r12, store, ↓reduceIte]
  congr 2
  apply (show ∀ {u v : Vector Value 53}, (∀ i : Fin 53, u[i.val] = v[i.val]) → u = v from
    fun he => Vector.ext fun i hi => he ⟨i, hi⟩)
  intro j
  finite_cases j <;> simp only [affineArgs, Vector.getElem_set] <;> rfl

end K256.Proofs.Ecdh.Wrapper
