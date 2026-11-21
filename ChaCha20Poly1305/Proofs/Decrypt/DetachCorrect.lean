import ChaCha20Poly1305.Proofs.Decrypt.DetachMessage

namespace ChaCha20Poly1305.Proofs.Decrypt.Detached
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program
open Hash Poly1305 Standards.RFC.ChaCha20Poly1305
set_option allowUnsafeReducibility true in
attribute [local reducible] ChaCha20Poly1305.Proofs.Decrypt.Lifted.lifted
set_option maxHeartbeats 750000
set_option maxRecDepth 8000
set_option linter.constructorNameAsVariable false

attribute [local irreducible] Packet.good chacha20Encrypt poly1305Mac poly1305KeyGen memLoad memStore

private theorem restoreSaved {fr : Activation} {p : Packet} {m m' rs rs'}
    (h : Atom.All fnCode rs m (preserved fr)) (ext : Atom.All fnCode rs m (extraIn p fr))
    (f : RamWriteFrame m m' (dirty p fr)) (sp : 864≤fr.rsp.toNat) : Atom.All fnCode rs' m' (preserved fr) := by
  have read : Readable m fr.rsp 8 := by unpack_atoms h []; assumption
  have lo := read.low
  have dat := ext
  unpack_atoms dat []
  apply ChaChaRound.keepFrame _ f h
  intro t ht
  simp only [preserved,List.mem_cons,List.not_mem_nil,or_false] at ht
  rcases ht with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  all_goals cases eq : p.good <;> simp [ChaChaRound.pass,Outside,dirty,innerZone,detachedFn,eq] <;> bv_omega

private theorem snapshotRegion (fr : Activation) (m : Ram) (lo : 864≤fr.rsp.toNat) :
    (atEntry fr m).region=⟨fr.rsp.toNat-864,864⟩ := by
  simp [atEntry,Activation.region]; bv_omega

theorem detachedCorrect (p : Packet) : (detachedFn p).Correct := by
  intro orig a lbl atoms prior
  let fr := atEntry orig a.store
  obtain ⟨abi,pre⟩ := (Atom.all_append _ _).1 atoms
  obtain ⟨pre0,ext0⟩ := (Atom.all_append _ _).1 pre
  have floor : 864≤orig.rsp.toNat := by unpack_atoms abi []; omega
  have bound : orig.low.toNat+864≤orig.rsp.toNat := by unpack_atoms abi []; assumption
  have low : orig.rsp.toNat+16≤2^32 := by
    have h := ext0; unpack_atoms h []; have l := abi; unpack_atoms l []; bv_omega
  have fg : fr.region=⟨orig.rsp.toNat-864,864⟩ := snapshotRegion orig a.store floor
  have start : (preLayout p.x).Rel fnCode (fr,()) (unitLoc .entry) a := by
    refine ⟨lbl,⟨(),rfl,rfl,(Atom.all_append _ _).2 ⟨?_,pre0⟩⟩,.refl _ _⟩
    unpack_atoms abi []
    join_atoms [fr,atEntry]
    all_goals first | assumption | bv_omega
  obtain ⟨b,j,bl,⟨_,_,_,bb⟩,bf⟩ := beginKey p.x start
  obtain ⟨abiB,rest⟩ := (Atom.all_append _ _).1 bb
  have sw : RamWriteFrame a.store b.store [⟨orig.rsp.toNat-864,864⟩] := by
    change RamWriteFrame a.store b.store [fr.region] at bf
    rwa [fg] at bf
  have ext : Atom.All fnCode b.arguments b.store (extraIn p fr) := keepExt (fr:=orig) ext0 sw
    (fun z hz => ⟨z,hz,Nat.le_refl _,Nat.le_refl _⟩) floor low
  have snap : Atom.All fnCode b.arguments b.store (preserved fr) := by unpack_atoms abiB []; join_atoms [] <;> assumption
  have reg : Atom.All fnCode b.arguments b.store (live (physical fr)) := by unpack_atoms abiB []; join_atoms [] <;> assumption
  have got : Atom.All fnCode b.arguments b.store (gotInfo fr) := by unpack_atoms abiB []; join_atoms [] <;> assumption
  have stack : Writable fnCode b.store (fr.rsp-864) 864 := by unpack_atoms snap []; assumption
  have align : fr.rsp.toNat%16=8 := by unpack_atoms snap []; assumption
  have code : fr.rsp.toNat≤0x1001f0 ∨ 0x102e00+864≤fr.rsp.toNat := by unpack_atoms ext []; assumption
  apply Forward.ofAhead (show Ahead lifted fnCode (fun d => d=b) a from ⟨b,j,rfl⟩) _
  intro b1 eq1
  subst b1
  apply prep p fr b bl reg ((Atom.all_append _ _).1 rest).2 stack floor align code ext _
  intro c pr
  have ec := keepExt (fr:=fr) (rs':=c.arguments) ext pr.frame (innerOuter fr floor) floor low
  have gc := keepGot (rs':=c.arguments) got pr.frame (innerOuter fr floor) floor
  apply checkPrepared p fr b.store c pr ec (stack.of_frame pr.frame) floor align gc _
  intro d q
  have ed := keepExt (fr:=fr) (rs':=d.arguments) ext q.frame (innerOuter fr floor) floor low
  apply message p fr b.store d q ed (stack.of_frame q.frame) floor align _
  intro t end_
  let v : BitVec 8 := if p.good then 0 else 1
  let ef := {fr with original:=t.store}
  have restore := restoreSaved (rs':=t.arguments) snap ext end_.frame floor
  have entry : Atom.All fnCode t.arguments t.store ((returnFn v).abi ef ++ (returnFn v).pre ef) :=
    retAtoms (fr:=fr) v end_.regs restore
  obtain ⟨o,run,ret,out,frame⟩ := returnCorrect v ef t end_.label entry (.refl _ _)
  refine ⟨o,run,ret,?_,?_⟩
  · obtain ⟨regs,al,_⟩ := (Atom.all_append _ _).1 out
    apply (Atom.all_append _ _).2
    refine ⟨regs,?_⟩
    cases hg : p.good
    · change Atom.All _ _ _ ([.low 0 8 (if p.good then 0 else 1)] ++ (if p.good then _ else []))
      simp only [hg,Bool.false_eq_true,ite_false,List.append_nil]
      exact ⟨by simpa only [v,hg,Bool.false_eq_true,ite_false] using al,trivial⟩
    · have ptr := ext
      unpack_atoms ptr []
      have keep : memLoad o.store p.buf (8*p.n.toNat)=memLoad t.store p.buf (8*p.n.toNat) := by
        apply frame.memLoad_eq
        change Outside [fr.region] p.buf (8*p.n.toNat/8)
        rw [fg]
        simp [Outside]; change 864≤fr.rsp.toNat at floor; dsimp [fr,atEntry] at *; omega
      change Atom.All _ _ _ (detachedFn p |>.post orig)
      simp only [detachedFn,hg,ite_true,List.cons_append,List.nil_append]
      exact ⟨by simpa only [v,hg,ite_true] using al,keep.trans (end_.data hg),trivial⟩
  · have within : ∀ z ∈ [fr.region], ∃ z' ∈ orig.region :: (detachedFn p).writes orig,
        z'.start≤z.start ∧ z.start+z.size≤z'.start+z'.size := by
      intro z hz
      simp only [List.mem_singleton] at hz
      subst z
      refine ⟨_,.head _,?_⟩
      rw [fg]; simp [Activation.region]; omega
    have incl : RegionsWithin (dirty p fr) (orig.region :: (detachedFn p).writes orig) := by
      intro z hz
      obtain hz|hz := List.mem_append.mp hz
      · simp only [innerZone,List.mem_singleton] at hz; subst z
        refine ⟨_,.head _,?_⟩
        dsimp [fr,atEntry,Activation.region]; omega
      · exact ⟨z,.tail _ hz,Nat.le_refl _,Nat.le_refl _⟩
    exact ((prior.trans (show RamWriteFrame a.store b.store [fr.region] from fg ▸ sw) within).trans end_.frame incl).trans frame within

end ChaCha20Poly1305.Proofs.Decrypt.Detached
