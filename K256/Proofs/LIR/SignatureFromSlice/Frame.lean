import K256.Proofs.LIR.Program
import K256.Proofs.Common.Refine.Contract
import K256.Proofs.Common.Refine.Lemma.SysVEntry

namespace K256.Proofs.LIR

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift

namespace SignatureFromSlice

def frameInfo : Refine.FrameInfo where
  entry := 0x102450
  frameBytes := 0x58
  stackBytes := some 0x290
  slots := [(3, 0x8)]
  preserved := [3, 5, 12, 13, 14, 15]
  fpPreserved := [39, 50, 51]
  clobbers := [0, 1, 2, 6, 7, 8, 9, 10, 11]
  callSlots := [(0x203dd0, 0x12a820), (0x203de0, 0x129770), (0x203e20, 0x100a20)]

def labelFrameG0 : Label.G0 → Option Refine.LabelFrame
  | .l102450 => some ⟨0x0, [(1, 1), (2, 2), (3, 3), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9),
      (12, 12), (13, 13), (14, 14), (15, 15), (39, 39), (50, 50),
      (51, 51)], [], [(0x203dd0, 0x12a820), (0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l10245b => some ⟨0x58, [(1, 1), (2, 2), (3, 3), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9),
      (12, 12), (13, 13), (14, 14), (15, 15), (39, 39), (50, 50),
      (51, 51)], [(0x8, 3)], [(0x203dd0, 0x12a820), (0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l102468 => some ⟨0x58, [(3, 7), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (39, 39),
      (50, 50), (51, 51)], [(0x8, 3)], []⟩
  | .l10246f => some ⟨0x58, [(3, 7), (5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (39, 39),
      (50, 50), (51, 51)], [(0x8, 3)], []⟩
  | .l1024d0 => some ⟨0x58, [(5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (39, 39), (50, 50),
      (51, 51)], [(0x8, 3)], []⟩
  | .l1024d6 => some ⟨0x58, [(1, 1), (2, 2), (3, 3), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9),
      (12, 12), (13, 13), (14, 14), (15, 15), (39, 39), (50, 50), (51, 51)], [(0x8, 3)], []⟩
  | .l1024df => some ⟨0x58, [(5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (39, 39), (50, 50),
      (51, 51)], [(0x8, 3)], []⟩
  | .l1024ee => some ⟨0x58, [(5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (39, 39), (50, 50),
      (51, 51)], [(0x8, 3)], []⟩
  | .l1024fb => some ⟨0x58, [(5, 5), (12, 12), (13, 13), (14, 14), (15, 15), (39, 39), (50, 50),
      (51, 51)], [(0x8, 3)], []⟩
  | _ => none

@[refine_layout] def frameAtG0 : Label.G0 → Refine.Activation → List Refine.Atom
  | .l102450 => fun fr =>
      [.gpr 4 fr.rsp, .reg 22 ⟨1, 0⟩, .gpr 1 fr.rcx, .gpr 2 fr.rdx, .gpr 3 fr.rbx, .gpr 5 fr.rbp,
       .gpr 6 fr.rsi, .gpr 7 fr.rdi, .gpr 8 fr.r8, .gpr 9 fr.r9, .gpr 12 fr.r12, .gpr 13 fr.r13,
       .gpr 14 fr.r14, .gpr 15 fr.r15, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x290) 0x290,
       .fact (fr.low.toNat + 0x290 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x203dd0 8, .mem 0x203dd0 64 0x12a820, .readable 0x203de0 8,
       .mem 0x203de0 64 0x129770, .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x2040b8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203dd0)]
  | .l10245b => fun fr =>
      [.gpr 4 (fr.rsp - 0x58), .reg 22 ⟨1, 0⟩, .gpr 1 fr.rcx, .gpr 2 fr.rdx, .gpr 3 fr.rbx,
       .gpr 5 fr.rbp, .gpr 6 fr.rsi, .gpr 7 fr.rdi, .gpr 8 fr.r8, .gpr 9 fr.r9, .gpr 12 fr.r12,
       .gpr 13 fr.r13, .gpr 14 fr.r14, .gpr 15 fr.r15, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x8) 64 fr.rbx, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x290) 0x290, .fact (fr.low.toNat + 0x290 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203dd0 8, .mem 0x203dd0 64 0x12a820,
       .readable 0x203de0 8, .mem 0x203de0 64 0x129770, .readable 0x203e20 8,
       .mem 0x203e20 64 0x100a20, .fact (0x2040b8 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203dd0)]
  | .l102468 => fun fr =>
      [.gpr 4 (fr.rsp - 0x58), .reg 22 ⟨1, 0⟩, .gpr 3 fr.rdi, .gpr 5 fr.rbp, .gpr 12 fr.r12,
       .gpr 13 fr.r13, .gpr 14 fr.r14, .gpr 15 fr.r15, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x8) 64 fr.rbx, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x290) 0x290, .fact (fr.low.toNat + 0x290 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8)]
  | .l10246f => fun fr =>
      [.gpr 4 (fr.rsp - 0x58), .reg 22 ⟨1, 0⟩, .gpr 3 fr.rdi, .gpr 5 fr.rbp, .gpr 12 fr.r12,
       .gpr 13 fr.r13, .gpr 14 fr.r14, .gpr 15 fr.r15, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x8) 64 fr.rbx, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x290) 0x290, .fact (fr.low.toNat + 0x290 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8)]
  | .l1024d0 => fun fr =>
      [.gpr 4 (fr.rsp - 0x58), .reg 22 ⟨1, 0⟩, .gpr 5 fr.rbp, .gpr 12 fr.r12, .gpr 13 fr.r13,
       .gpr 14 fr.r14, .gpr 15 fr.r15, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x8) 64 fr.rbx, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x290) 0x290, .fact (fr.low.toNat + 0x290 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8)]
  | .l1024d6 => fun fr =>
      [.gpr 4 (fr.rsp - 0x58), .reg 22 ⟨1, 0⟩, .gpr 1 fr.rcx, .gpr 2 fr.rdx, .gpr 3 fr.rbx,
       .gpr 5 fr.rbp, .gpr 6 fr.rsi, .gpr 7 fr.rdi, .gpr 8 fr.r8, .gpr 9 fr.r9, .gpr 12 fr.r12,
       .gpr 13 fr.r13, .gpr 14 fr.r14, .gpr 15 fr.r15, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x8) 64 fr.rbx, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x290) 0x290, .fact (fr.low.toNat + 0x290 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8)]
  | .l1024df => fun fr =>
      [.gpr 4 (fr.rsp - 0x58), .reg 22 ⟨1, 0⟩, .gpr 5 fr.rbp, .gpr 12 fr.r12, .gpr 13 fr.r13,
       .gpr 14 fr.r14, .gpr 15 fr.r15, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x8) 64 fr.rbx, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x290) 0x290, .fact (fr.low.toNat + 0x290 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8)]
  | .l1024ee => fun fr =>
      [.gpr 4 (fr.rsp - 0x58), .reg 22 ⟨1, 0⟩, .gpr 5 fr.rbp, .gpr 12 fr.r12, .gpr 13 fr.r13,
       .gpr 14 fr.r14, .gpr 15 fr.r15, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x8) 64 fr.rbx, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x290) 0x290, .fact (fr.low.toNat + 0x290 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8)]
  | .l1024fb => fun fr =>
      [.gpr 4 (fr.rsp - 0x58), .reg 22 ⟨1, 0⟩, .gpr 5 fr.rbp, .gpr 12 fr.r12, .gpr 13 fr.r13,
       .gpr 14 fr.r14, .gpr 15 fr.r15, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x8) 64 fr.rbx, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x290) 0x290, .fact (fr.low.toNat + 0x290 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8)]
  | _ => fun _ => []

def labelFrame : Label → Option Refine.LabelFrame
  | .g0 l => labelFrameG0 l

@[refine_layout] def frameAt : Label → Refine.Activation → List Refine.Atom
  | .g0 l => frameAtG0 l

@[refine_layout] def doneAt (fr : Refine.Activation) : List Refine.Atom :=
  [.gpr 4 (fr.rsp + 8), .reg 22 ⟨1, 0⟩, .gpr 3 fr.rbx, .gpr 5 fr.rbp, .gpr 12 fr.r12,
   .gpr 13 fr.r13, .gpr 14 fr.r14, .gpr 15 fr.r15, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
   .reg 51 ⟨16, fr.fcw⟩]

theorem frameAt_canonical (l : Label) (fr : Refine.Activation) :
    frameAt l fr = frameInfo.atomsAt (labelFrame l) fr := by
  cases l <;> rename_i l <;> first | rfl | (cases l <;> rfl)

theorem doneAt_canonical (fr : Refine.Activation) : doneAt fr = frameInfo.doneAtoms fr := rfl

abbrev Pre (code : CodeMap) (fr : Refine.Activation) (s : RamState) : Prop :=
  frameInfo.Pre code fr s

abbrev Post (fr : Refine.Activation) (footprint : List Prelude.MemoryRegion)
    (t : RamState) : Prop :=
  frameInfo.Post fr footprint t

def closureCode : CodeMap := sectionCode textSection [(0xa20, 0x2), (0x2450, 0xad), (0x3ac0, 0x235),
    (0x7730, 0x1b9), (0x27d50, 0x11), (0x27d70, 0x79), (0x27df0, 0xa4), (0x27f50, 0x6a),
    (0x295f2, 0x3d), (0x29770, 0x2c), (0x2a820, 0x2f)]

theorem closure_code : ∀ x ∈ closureCode, x ∈ fnCode :=
  sectionCode_sub (.head _) (by decide)

theorem callSlots_loaded {sections : Prelude.ImageSections}
    (hs : rodataSection ∈ sections) {mem : Ram}
    (h : ∀ x ∈ sections.toCodeMap, mem[x.1]? = some x.2) :
    ∀ c ∈ frameInfo.callSlots, Refine.Readable mem c.1 8 ∧ memLoad mem c.1 64 = c.2 :=
  Refine.FrameInfo.callSlots_of_section hs (by decide +kernel) h

theorem callSlots_span {sections : Prelude.ImageSections}
    (hs : rodataSection ∈ sections) :
    ∀ a : BitVec 64, Refine.FrameInfo.slotsLow frameInfo.callSlots ≤ a.toNat →
      a.toNat < Refine.FrameInfo.slotsHigh frameInfo.callSlots →
        ∃ b, (a, b) ∈ sections.toCodeMap :=
  Refine.FrameInfo.callSlotSpan_of_section hs (by decide +kernel)

section Contract

variable {UOp : Nat → Type} {ULabel UValue UStore : Type} {usig : ULabel → Nat} {results : Nat}
  {P : Program UOp ULabel usig results} {D : Dialect UOp UValue UStore} {Ctx : Type}

theorem routine [inst : Bindings] {atoms : Label → Refine.Activation → List Refine.Atom}
    {retAtoms : Refine.Activation → List Refine.Atom} (core : Refine.LayoutCore P D lifted Ctx)
    {code : CodeMap} (liftedBlocks : ∀ l, LiftedBlock code lifted l)
    (blocks : ∀ label, (Refine.Layout.withFrame atoms retAtoms core).BlockSimulation code label)
    {initial : RamState} {fr : Refine.Activation} {c : Ctx} {n : Nat}
    {regions : Vector Prelude.MemoryRegion n} (hready : EntryReady code initial)
    (hpre : Pre code fr initial)
    (hregions : ∀ x, (∀ r ∈ regions, ¬ r.Contains x) →
      ∀ r ∈ fr.region :: core.footprint c fr, ¬ r.Contains x)
    {lab : ULabel} {p : core.Params lab} {o : Output UValue UStore results}
    (hexec : P.Exec D ⟨⟨lab, core.args lab p, core.store lab p⟩, []⟩ o)
    (hcore : Refine.Atom.All code (lifted.locationOf .l102450 initial).arguments initial.external
      (core.atoms lab c fr p))
    (hstart : core.start lab = .l102450 := by rfl)
    (hentry : ∀ fr, atoms .l102450 fr = frameInfo.entryAtoms fr := by intro _; rfl)
    (hdone : ∀ fr, retAtoms fr = frameInfo.doneAtoms fr := by intro _; rfl) :
    RoutineResult inst initial regions fun t =>
      Prelude.Execution.CallingConvention.SysVCalleeReturn initial t fr.ret ∧
        Post fr (core.footprint c fr) t ∧ ∃ r, o = core.output r ∧ ∃ lo,
          RetRel code lifted lo t ∧
            Refine.Atom.All code lo.values lo.store (core.done c fr r) :=
  Refine.Layout.withFrame_routine core hready hpre liftedBlocks blocks hregions hexec hcore hstart hentry
    hdone rfl rfl (by decide) (by decide)

theorem call {atoms : Label → Refine.Activation → List Refine.Atom}
    {retAtoms : Refine.Activation → List Refine.Atom} {core : Refine.LayoutCore P D lifted Ctx}
    {code : CodeMap}
    (blocks : ∀ label, (Refine.Layout.withFrame atoms retAtoms core).BlockSimulation code label)
    {u : Location UValue UStore ULabel usig} {o : Output UValue UStore results}
    (hexec : P.Exec D ⟨u, []⟩ o) (fr : Refine.Activation) (c : Ctx) {l : lifted.Location}
    (hrel : (Refine.Layout.withFrame atoms retAtoms core).Rel code (fr, c) u l)
    (hdone : ∀ fr, retAtoms fr = frameInfo.doneAtoms fr := by intro _; rfl) :
    ∃ lo, lifted.program.Exec (dialect code) ⟨l, []⟩ lo ∧
      (Refine.Layout.withFrame atoms retAtoms core).RetRel code (fr, c) o lo ∧
        Refine.Atom.All code lo.values lo.store (frameInfo.doneAtoms fr) :=
  Refine.Layout.withFrame_call blocks hexec fr c hrel hdone

end Contract

end SignatureFromSlice

end K256.Proofs.LIR
