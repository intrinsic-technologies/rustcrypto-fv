import ChaCha20Poly1305.Proofs.Decrypt.ChaChaRound

namespace ChaCha20Poly1305.Proofs.Decrypt.ChaChaRound
open X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine ChaCha20Poly1305.Proofs.CFG Standards.RFC.ChaCha20Poly1305

private theorem transJump {l : Lifted} {code : CodeMap} {a b c}
    (x : JumpRun l code a b) (y : JumpRun l code b c) : JumpRun l code a c := by
  induction x with
  | refl => exact y
  | jump h _ ih => exact .jump h (ih y)

private theorem bindAhead {l : Lifted} {code : CodeMap} {a : l.Location} {p q : l.Location → Prop}
    (h : Ahead l code p a) (k : ∀ b, p b → Ahead l code q b) : Ahead l code q a := by
  obtain ⟨b,x,hb⟩ := h
  obtain ⟨c,y,hc⟩ := k b hb
  exact ⟨c,transJump x y,hc⟩

variable {lifted : Lifted} {Ctx : Type} (lay : Layout program dialect lifted Ctx) {code : CodeMap}
    (hs : ∀ l, l ≠ .finish → lay.BlockSimulation code l)

def loc (l : Label) (p : Data) : Location Data Unit Label (fun _ => 1) := ⟨l, #v[p], ()⟩

include hs
private theorem one {x y : Label} (hn : x ≠ .finish) {p q : Data}
    (he : program.runBlock dialect (loc x p) = .jump (loc y q)) {c a}
    (hr : lay.Rel code c (loc x p) a) : Ahead lifted code (lay.Rel code c (loc y q)) a := by
  have hb := hs x hn c #v[p] () a hr
  change lay.MatchedBy code c a (program.runBlock dialect (loc x p)) at hb
  rw [he] at hb
  exact hb

private theorem quarter0 {p : Data} {c a} (hr : lay.Rel code c (loc .q0 p) a) :
    Ahead lifted code (lay.Rel code c (loc .q1 (advance .q0 p))) a :=
  one lay hs (x := .q0) (y := .q1) (p := p) (q := advance .q0 p) (by decide) rfl hr

private theorem quarter1 {p : Data} {c a} (hr : lay.Rel code c (loc .q1 p) a) :
    Ahead lifted code (lay.Rel code c (loc .q2 (advance .q1 p))) a :=
  one lay hs (x := .q1) (y := .q2) (p := p) (q := advance .q1 p) (by decide) rfl hr

private theorem quarter2 {p : Data} {c a} (hr : lay.Rel code c (loc .q2 p) a) :
    Ahead lifted code (lay.Rel code c (loc .q3 (advance .q2 p))) a :=
  one lay hs (x := .q2) (y := .q3) (p := p) (q := advance .q2 p) (by decide) rfl hr

private theorem quarter3 {p : Data} {c a} (hr : lay.Rel code c (loc .q3 p) a) :
    Ahead lifted code (lay.Rel code c (loc .q4 (advance .q3 p))) a :=
  one lay hs (x := .q3) (y := .q4) (p := p) (q := advance .q3 p) (by decide) rfl hr

private theorem quarter4 {p : Data} {c a} (hr : lay.Rel code c (loc .q4 p) a) :
    Ahead lifted code (lay.Rel code c (loc .q5 (advance .q4 p))) a :=
  one lay hs (x := .q4) (y := .q5) (p := p) (q := advance .q4 p) (by decide) rfl hr

private theorem quarter5 {p : Data} {c a} (hr : lay.Rel code c (loc .q5 p) a) :
    Ahead lifted code (lay.Rel code c (loc .q6 (advance .q5 p))) a :=
  one lay hs (x := .q5) (y := .q6) (p := p) (q := advance .q5 p) (by decide) rfl hr

private theorem quarter6 {p : Data} {c a} (hr : lay.Rel code c (loc .q6 p) a) :
    Ahead lifted code (lay.Rel code c (loc .q7 (advance .q6 p))) a :=
  one lay hs (x := .q6) (y := .q7) (p := p) (q := advance .q6 p) (by decide) rfl hr

private theorem quarter7 {p : Data} {c a} (hr : lay.Rel code c (loc .q7 p) a) :
    Ahead lifted code (lay.Rel code c (loc .count (advance .q7 p))) a :=
  one lay hs (x := .q7) (y := .count) (p := p) (q := advance .q7 p) (by decide) rfl hr

theorem inner {p : Data} {c a} (hr : lay.Rel code c (loc .q0 p) a) :
    Ahead lifted code (lay.Rel code c (loc .count ⟨innerBlock p.words,p.count⟩)) a := by
  apply bindAhead (quarter0 lay hs hr)
  intro a hr
  apply bindAhead (quarter1 lay hs hr)
  intro a hr
  apply bindAhead (quarter2 lay hs hr)
  intro a hr
  apply bindAhead (quarter3 lay hs hr)
  intro a hr
  apply bindAhead (quarter4 lay hs hr)
  intro a hr
  apply bindAhead (quarter5 lay hs hr)
  intro a hr
  apply bindAhead (quarter6 lay hs hr)
  intro a hr
  apply bindAhead (quarter7 lay hs hr)
  intro a hr
  simp only [advance, innerBlock] at hr ⊢
  exact ⟨a,.refl a,hr⟩

omit hs
private theorem dec (p : Data) :
    program.runBlock dialect (loc .count p) =
      .jump (loc (if p.count - 1 = 0 then .finish else .q0) ⟨p.words,p.count - 1⟩) := by
  unfold loc
  cfg_eval [program, dialect, advance]
  by_cases h : p.count - 1 = 0 <;> simp_all [dialect,Dialect.ofPure]

def rounds : Nat → Vector UInt32 16 → Vector UInt32 16
  | 0, w => w
  | i+1, w => rounds i (innerBlock w)

include hs
theorem loop {n : Nat} (hn : n < 2^64) (hp : n > 0) {w} {c a}
    (hr : lay.Rel code c (loc .q0 ⟨w,BitVec.ofNat 64 n⟩) a) :
    Ahead lifted code (lay.Rel code c (loc .finish ⟨rounds n w,0⟩)) a := by
  induction n generalizing w a with
  | zero => omega
  | succ n ih =>
    apply bindAhead (inner lay hs hr)
    intro b hb
    have he : BitVec.ofNat 64 (n+1) - 1 = BitVec.ofNat 64 n := by rw [BitVec.ofNat_add]; exact BitVec.add_sub_cancel _ (1 : BitVec 64)
    have step := dec (⟨innerBlock w,BitVec.ofNat 64 (n+1)⟩ : Data)
    dsimp only at step
    rw [he] at step
    cases n with
    | zero =>
      simp only [ite_true, BitVec.ofNat_eq_ofNat] at step
      exact one lay hs (by decide) step hb
    | succ n =>
      have nz : BitVec.ofNat 64 (n+1) ≠ 0 := by
        have he : (BitVec.ofNat 64 (n+1)).toNat = n+1 := Nat.mod_eq_of_lt (by omega)
        intro h
        rw [h] at he
        simp at he
      simp only [nz, ite_false] at step
      exact bindAhead (one lay hs (by decide) step hb) fun _ h => ih (by omega) (by omega) h

end ChaCha20Poly1305.Proofs.Decrypt.ChaChaRound
