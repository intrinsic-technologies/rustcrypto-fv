import AesGcm.Proofs.Copied.X86Proofs.Lift.Rules

namespace X86Proofs.Lift

open X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG

structure FixedRel [Bindings] (code : CodeMap) (P : Lifted) (s₀ : RamState) (st : P.State)
    (s : RamState) : Prop where
  rel : Rel code P st s
  fixed : fixedPart s = fixedPart s₀

structure FixedRetRel [Bindings] (code : CodeMap) (P : Lifted) (s₀ : RamState)
    (o : Output Value Ram Reg.count) (t : RamState) : Prop where
  rel : RetRel code P o t
  fixed : fixedPart t = fixedPart s₀

structure LiftedBlock [Bindings] (code : CodeMap) (P : Lifted) (label : P.Label) : Prop where
  addr : CodeAt code (P.address label)
  sim : ∀ boundary : ReturnBoundary, ReturnOutside boundary code →
    (∀ l, P.address l ≠ boundary.rip) → ∀ s₀ : RamState,
      Program.BlockSimulation (machineAnyReturn boundary) P.program (dialect code)
        (FixedRel code P s₀) (FixedRetRel code P s₀) label

theorem Lifted.simulationFixed [Bindings] {code : CodeMap} {P : Lifted}
    (blocks : ∀ l, LiftedBlock code P l) {boundary : ReturnBoundary}
    (hout : ReturnOutside boundary code) (s₀ : RamState) :
    Simulation (machineAnyReturn boundary) (P.program.sem (dialect code)) (FixedRel code P s₀)
      (FixedRetRel code P s₀) :=
  Simulation.of_blocks fun l => (blocks l).sim boundary hout (fun l' =>
    ReturnOutside.ne hout (blocks l').addr) s₀

theorem Lifted.simulation [Bindings] {code : CodeMap} {P : Lifted}
    (blocks : ∀ l, LiftedBlock code P l) {boundary : ReturnBoundary}
    (hout : ReturnOutside boundary code) :
    Simulation (machineAnyReturn boundary) (P.program.sem (dialect code)) (Rel code P)
      (RetRel code P) where
  step := fun {_ _ a} h hs =>
    let ⟨b, hab, hb⟩ := (Lifted.simulationFixed blocks hout a).step ⟨h, rfl⟩ hs
    ⟨b, hab, hb.rel⟩
  ret := fun {_ _ a} h hr =>
    let ⟨o', he, hp⟩ := (Lifted.simulationFixed blocks hout a).ret ⟨h, rfl⟩ hr
    ⟨o', he, hp.rel⟩

theorem codeRange_sub_section {sections : Prelude.ImageSections} {s : Prelude.ImageSection}
    (hs : s ∈ sections) (off len : Nat) {bytes : List UInt8} {p : BitVec 64}
    (h : chunkedRead s.bytes off len = bytes) (hc : len ≤ s.bytes.chunkSize)
    (hle : off + len ≤ s.bytes.size) (hp : s.address + BitVec.ofNat 64 off = p) :
    ∀ x ∈ codeRange p bytes, x ∈ sections.toCodeMap := by
  subst h hp
  rw [← chunked_toListFrom_eq_read _ hc hle, ← chunked_toList_slice _ _ _ hle]
  exact fun x hx => List.mem_flatMap.2 ⟨s, hs, codeRange_slice_subset _ _ off len x hx⟩

theorem codeRange_sub_section_append {sections : Prelude.ImageSections} {s : Prelude.ImageSection}
    (hs : s ∈ sections) (off len : Nat) {bytes rest : List UInt8} {p q : BitVec 64}
    (h : chunkedRead s.bytes off len = bytes) (hc : len ≤ s.bytes.chunkSize)
    (hle : off + len ≤ s.bytes.size) (hp : s.address + BitVec.ofNat 64 off = p)
    (hq : p + BitVec.ofNat 64 len = q) (hrest : ∀ x ∈ codeRange q rest, x ∈ sections.toCodeMap) :
    ∀ x ∈ codeRange p (bytes ++ rest), x ∈ sections.toCodeMap := by
  have hlen : bytes.length = len := by
    rw [← h, ← chunked_toListFrom_eq_read _ hc hle, chunked_toListFrom_length]
  intro x hx
  rw [codeRange_append, hlen, hq] at hx
  exact (List.mem_append.1 hx).elim (codeRange_sub_section hs off len h hc hle hp x) (hrest x)

def sectionCode (s : Prelude.ImageSection) (pieces : List (Nat × Nat)) : CodeMap :=
  pieces.flatMap fun q => codeRange (s.address + BitVec.ofNat 64 q.1) (chunkedRead s.bytes q.1 q.2)

theorem sectionCode_sub {sections : Prelude.ImageSections} {s : Prelude.ImageSection}
    (hs : s ∈ sections) {pieces : List (Nat × Nat)}
    (h : ∀ q ∈ pieces, q.2 ≤ s.bytes.chunkSize ∧ q.1 + q.2 ≤ s.bytes.size) :
    ∀ x ∈ sectionCode s pieces, x ∈ sections.toCodeMap := by
  intro x hx
  obtain ⟨q, hq, hx⟩ := List.mem_flatMap.1 hx
  exact codeRange_sub_section hs q.1 q.2 rfl (h q hq).1 (h q hq).2 rfl x hx

def Lifted.locationOf (P : Lifted) (l : P.Label) (s : RamState) : P.Location :=
  ⟨l, Vector.ofFn fun i => (Reg.ofIndex i).read s, s.external⟩

section

variable [Bindings] {code : CodeMap} {P : Lifted}

theorem Rel.locationOf {l : P.Label} {s : RamState} (h : EntryReady code s)
    (hrip : s.RIP = P.address l) : Rel code P ⟨P.locationOf l s, []⟩ s :=
  ⟨hrip, fun _ _ _ => Vector.getElem_ofFn _, rfl, nofun, h.ready, h.sse, h.code⟩

theorem Rest.liftedBlock {label : P.Label} {k : Nat} {bytes : List UInt8}
    (rest : Rest code P (codeRange (P.address label) bytes) (entryMap (P.live label)) k
      (P.address label) bytes (P.program.blocks label))
    (hne : bytes ≠ []) (inCode : ∀ x ∈ codeRange (P.address label) bytes, x ∈ code) :
    LiftedBlock code P label := by
  refine ⟨(codeAt_codeRange (List.length_pos_iff.mpr hne)).mono inCode,
    fun boundary hout hoff s₀ arguments store stack s rel => ?_⟩
  obtain ⟨⟨hrip, hregs, hstore, hframes, hready, hsse, hcode⟩, hfixed⟩ := rel
  have hout' : ReturnOutside boundary (codeRange (P.address label) bytes) :=
    ReturnOutside.mono hout inCode
  have start : Start code (codeRange (P.address label) bytes) (entryMap (P.live label))
      (P.address label) bytes arguments store s := by
    refine ⟨hrip, ?_, hstore, hready, hsse, hcode, fun _ h => h, inCode⟩
    intro i j hj
    obtain ⟨rfl, hi, hlive⟩ := mem_entryMap hj
    exact ⟨hi, hregs j hi hlive⟩
  change (((P.program.blocks label).eval (dialect code) arguments store).next (dialect code)
    stack).MatchedBy _ _ _ s
  cases htr : (P.program.blocks label).eval (dialect code) arguments store with
  | stuck => trivial
  | jump next =>
    obtain ⟨u, fin⟩ := rest.run arguments store s start (by rw [htr]; nofun)
    rw [htr] at fin
    obtain ⟨hrip', hargs', hstore'⟩ := fin.reached
    obtain ⟨m, hrun, -⟩ := fin.run
    exact ⟨u, .single ⟨m, hrun.advances_to_label hout' (hrip' ▸ hoff _)⟩,
      ⟨⟨hrip', hargs', hstore', hframes, fin.ready, fin.sse, fin.codeIn⟩, fin.fixed.trans hfixed⟩⟩
  | call next fr =>
    obtain ⟨u, fin⟩ := rest.run arguments store s start (by rw [htr]; nofun)
    rw [htr] at fin
    obtain ⟨hrip', hargs', hstore', hfr⟩ := fin.reached
    obtain ⟨m, hrun, -⟩ := fin.run
    refine ⟨u, .single ⟨m, hrun.advances_to_label hout' (hrip' ▸ hoff _)⟩,
      ⟨⟨hrip', hargs', hstore', ?_, fin.ready, fin.sse, fin.codeIn⟩, fin.fixed.trans hfixed⟩⟩
    intro fr' hfr'
    rcases List.mem_cons.mp hfr' with rfl | hfr'
    · exact hfr
    · exact hframes fr' hfr'
  | returned o =>
    obtain ⟨u, fin⟩ := rest.run arguments store s start (by rw [htr]; nofun)
    rw [htr] at fin
    obtain ⟨htag, hvals, hstore'⟩ := fin.reached
    obtain ⟨m, hrun, -⟩ := fin.run
    cases stack with
    | nil =>
      refine ⟨u, .ret ⟨m, ?_⟩, ⟨⟨htag, hvals, hstore', fin.ready, fin.sse, fin.codeIn⟩,
        fin.fixed.trans hfixed⟩⟩
      by_cases hat : AtBoundary boundary u
      · have hm : m ≠ 0 := by
          rintro rfl
          rw [← hrun.eq_of_zero] at hat
          exact hoff label (hrip.symm.trans hat.1)
        exact .inr (hrun.returns hout' hm hat)
      · refine .inl ⟨hrun.advances hout' fun _ => ?_, hat⟩
        by_cases h : u.RIP = boundary.rip
        · exact .inr fun h' => hat ⟨h, h'⟩
        · exact .inl h
    | cons fr rest' =>
      simp only [Transfer.next]
      split
      · rename_i hacc
        obtain ⟨hsize, hguard, hret⟩ := hframes fr List.mem_cons_self
        have hrip' : u.RIP = P.address fr.target := by
          simp only [StackFrame.Accepts, hguard, htag, dialect, decide_eq_true_eq] at hacc
          exact (eq_of_heq (Value.mk.inj hacc).2).symm
        refine ⟨u, .single ⟨m, hrun.advances_to_label hout' (hrip' ▸ hoff _)⟩,
          ⟨⟨hrip', ?_, hstore', fun fr' hfr' => hframes fr' (List.mem_cons_of_mem _ hfr'),
            fin.ready, fin.sse, fin.codeIn⟩, fin.fixed.trans hfixed⟩⟩
        intro i hi hlive
        show ((o.values ++ fr.kept).cast fr.arity)[i] = _
        rw [Vector.getElem_cast, Vector.getElem_append_left hi]
        exact hvals i hi (hret i hi hlive)
      · trivial

end

end X86Proofs.Lift
