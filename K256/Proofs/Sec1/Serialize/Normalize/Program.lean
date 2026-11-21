import K256.Proofs.Sec1.Serialize.Normalize.Words
import K256.Proofs.Common.CFG.IR

namespace K256.Proofs.Sec1.Serialize.Normalize

open K256.Proofs.Common.Field K256.Proofs.CFG

abbrev Store := Limbs × Limbs

inductive Op : Nat → Type where
  | first : Op 0
  | carry (i : Fin 5) : Op 1
  | top : Op 1
  | flag : Op 5
  | lowByte : Op 1
  | normalize : Op 6

def eval : {n : Nat} → Op n → Values Word n → Store → Option (Word × Store)
  | _, .first, _, s => some (first s.1, s)
  | _, .carry i, v, s => some (carry v[0] s.1[i], s)
  | _, .top, v, s => some (top v[0] s.1[4], s)
  | _, .flag, v, s => some (flagOf v[0] v[1] v[2] v[3] v[4], s)
  | _, .lowByte, v, s => some ((v[0].setWidth 8).setWidth 64, s)
  | _, .normalize, v, s => some (0, (s.1, normOf v[0] v[1] v[2] v[3] v[4] v[5]))

def dialect : Dialect Op Word Store where
  eval := eval
  truth := (· != 0)

inductive Label where
  | entry | resume | choice

def signature : Label → Nat
  | .entry => 1
  | .resume => 7
  | .choice => 1

def program : Program Op Label signature 1 where
  blocks
    | .entry => .letOp .first #v[] (.letOp (.carry 1) #v[%1] (.letOp (.carry 2) #v[%2]
        (.letOp (.carry 3) #v[%3] (.letOp .top #v[%4] (.letOp .flag #v[%1, %2, %3, %4, %5]
        (.terminate (.call ⟨.choice, #v[%6]⟩
          { target := .resume, kept := #v[%0, %1, %2, %3, %4, %5] })))))))
    | .resume => .letOp .normalize #v[%0, %2, %3, %4, %5, %6] (.terminate (.ret #v[%1]))
    | .choice => .letOp .lowByte #v[%0] (.terminate (.ret #v[%1]))

theorem exec (dst : Word) (s : Store) :
    program.Exec dialect ⟨⟨.entry, #v[dst], s⟩, []⟩ ⟨#v[dst], none, (s.1, normalize s.1)⟩ := by
  let t0 := first s.1
  let t1 := carry t0 s.1[1]
  let t2 := carry t1 s.1[2]
  let t3 := carry t2 s.1[3]
  let t4 := top t3 s.1[4]
  let f := flagOf t0 t1 t2 t3 t4
  have hf : (f.setWidth 8).setWidth 64 = f := by
    dsimp only [f, flagOf]
    simp only [BitVec.setWidth_setWidth_of_le _ (show 8 ≤ 64 by decide), BitVec.setWidth_eq]
  have step3 (r : Word) :
      program.step dialect ⟨⟨.resume, #v[r, dst, t0, t1, t2, t3, t4], s⟩, []⟩ =
        .done ⟨#v[dst], none, (s.1, normOf r t0 t1 t2 t3 t4)⟩ := rfl
  have step2 :
      program.step dialect ⟨⟨.choice, #v[f], s⟩,
        [⟨.resume, #v[dst,t0,t1,t2,t3,t4], rfl, none⟩]⟩ =
        .next ⟨⟨.resume, #v[(f.setWidth 8).setWidth 64, dst,t0,t1,t2,t3,t4], s⟩, []⟩ := rfl
  rw [hf] at step2
  exact .next rfl (.next step2 (.done (step3 f)))

end K256.Proofs.Sec1.Serialize.Normalize
