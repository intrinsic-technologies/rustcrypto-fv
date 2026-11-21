import ChaCha20Poly1305.Proofs.Decrypt.TailKernel
import ChaCha20Poly1305.Proofs.Decrypt.RoundFrame

namespace ChaCha20Poly1305.Proofs.Decrypt.Stream.Tail
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program
open ChaChaRound hiding Label program

set_option maxHeartbeats 600000
set_option maxRecDepth 5000

private theorem safe {fr : Activation} (x : Input) (hb : fr.rsp.toNat + 176 ≤ 2^32) :
    ∀ a ∈ keep x fr, pass (TailRounds.layout.regions fr) a := by
  intro a ha
  simp only [keep,common,List.cons_append, List.nil_append,List.mem_cons,List.not_mem_nil,or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | trivial | (simp [pass,TailRounds.layout,Outside]; bv_omega)

private theorem contained (fr : Activation) (x : Input) :
    RegionsWithin (TailRounds.layout.regions fr) ((layout x).regions fr) := by
  intro r hr
  simp only [TailRounds.layout,List.mem_cons,List.not_mem_nil,or_false] at hr
  rcases hr with rfl | rfl | rfl | rfl | rfl
  all_goals exact ⟨_,.head _,by dsimp; omega,by dsimp; omega⟩

theorem roundStep (x : Input) : (layout x).BlockSimulation fnCode .round := by
  intro fr args st a h
  obtain ⟨hl,⟨p,hargs,hst,hat⟩,hf⟩ := h
  change args = #v[] at hargs
  subst args; cases st
  change Atom.All _ _ _ (roundAtoms fr x.w 10 ++ keep x fr) at hat
  have hk := (Atom.all_append _ _).1 hat |>.2
  have hcom := (Atom.all_append _ _).1 hk |>.1
  have hb : fr.rsp.toNat + 176 ≤ 2^32 := hcom.1.readable.low
  have aux := runFramed TailRounds.layout TailRounds.blocks (fun _ _ => rfl)
    (fun _ _ _ _ => rfl) (fun _ _ => rfl) (fun _ p => p)
    (fun _ _ => rfl) (w := x.w) (fr := fr) (a := a)
    (safe x hb) (contained fr x) hl hat hf (by
      intro l p q he
      exact congrArg (fun v => v[0]) he)
  obtain ⟨b,run,lbl,ha,frame⟩ := aux
  exact ⟨b,run,lbl,⟨(),rfl,rfl,ha⟩,frame⟩

end ChaCha20Poly1305.Proofs.Decrypt.Stream.Tail
