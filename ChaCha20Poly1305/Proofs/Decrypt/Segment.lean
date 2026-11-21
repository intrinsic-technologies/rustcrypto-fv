import ChaCha20Poly1305.Proofs.Decrypt.Compose
import ChaCha20Poly1305.Proofs.Decrypt.Empty

namespace ChaCha20Poly1305.Proofs.Decrypt
open X86 X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine

theorem jumpTrans {l : Lifted} {code : CodeMap} {a b c}
    (x : JumpRun l code a b) (y : JumpRun l code b c) : JumpRun l code a c := by
  induction x with
  | refl => exact y
  | jump h _ ih => exact .jump h (ih y)

theorem aheadBind {l : Lifted} {code : CodeMap} {a : l.Location} {p q : l.Location → Prop}
    (h : Ahead l code p a) (k : ∀ b, p b → Ahead l code q b) : Ahead l code q a := by
  obtain ⟨b,x,hb⟩ := h
  obtain ⟨c,y,hc⟩ := k b hb
  exact ⟨c,jumpTrans x y,hc⟩

abbrev unitLoc {L : Type} (l : L) : Location Unit Unit L (fun _ => 0) := ⟨l,#v[],()⟩

theorem segment {L C : Type} {p : Program (fun _ => _root_.Empty) L (fun _ => 0) 0}
    (lay : Layout p Empty.semantics Lifted.lifted C) {i j : L}
    (hs : lay.BlockSimulation Lifted.fnCode i)
    (edge : p.runBlock Empty.semantics (unitLoc i) = .jump (unitLoc j)) {c a}
    (rel : lay.Rel Lifted.fnCode c (unitLoc i) a) :
    Ahead Lifted.lifted Lifted.fnCode (lay.Rel Lifted.fnCode c (unitLoc j)) a := by
  have h := hs c #v[] () a rel
  change lay.MatchedBy _ _ _ (p.runBlock _ (unitLoc i)) at h
  rw [edge] at h
  exact h

end ChaCha20Poly1305.Proofs.Decrypt
