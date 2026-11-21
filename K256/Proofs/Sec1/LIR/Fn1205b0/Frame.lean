import K256.Proofs.Sec1.LIR.Program
import K256.Proofs.Common.Refine.Contract

namespace K256.Proofs.Sec1.LIR

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift

namespace Fn1205b0

def frameInfo : Refine.FrameInfo where
  entry := 0x1205b0
  frameBytes := 0x1e8
  stackBytes := some 0x418
  slots := [(3, 0x30), (5, 0x8), (12, 0x28), (13, 0x20), (14, 0x18), (15, 0x10)]
  preserved := [3, 5, 12, 13, 14, 15]
  fpPreserved := [39, 50, 51]
  clobbers := [0, 1, 2, 6, 7, 8, 9, 10, 11]
  callSlots := []

def labelFrameG2 : Label.G2 → Option Refine.LabelFrame
  | .l1205b0 => some ⟨0x0, [(1, 1), (2, 2), (3, 3), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9),
      (12, 12), (13, 13), (14, 14), (15, 15), (39, 39), (50, 50), (51, 51)], [], []⟩
  | .l120653 => some ⟨0x1e8, [(39, 39), (50, 50), (51, 51)], [(0x160, 7), (0x30, 3), (0x28, 12),
      (0x20, 13), (0x18, 14), (0x10, 15), (0x8, 5)], []⟩
  | .l12065f => some ⟨0x1e8, [(39, 39), (50, 50), (51, 51)], [(0x160, 7), (0x30, 3), (0x28, 12),
      (0x20, 13), (0x18, 14), (0x10, 15), (0x8, 5)], []⟩
  | .l120d03 => some ⟨0x1e8, [(39, 39), (50, 50), (51, 51)], [(0x160, 7), (0x30, 3), (0x28, 12),
      (0x20, 13), (0x18, 14), (0x10, 15), (0x8, 5)], []⟩
  | .l120d83 => some ⟨0x1e8, [(39, 39), (50, 50), (51, 51)], [(0x160, 7), (0x30, 3), (0x28, 12),
      (0x20, 13), (0x18, 14), (0x10, 15), (0x8, 5)], []⟩
  | .l120dff => some ⟨0x1e8, [(39, 39), (50, 50), (51, 51)], [(0x160, 7), (0x30, 3), (0x28, 12),
      (0x20, 13), (0x18, 14), (0x10, 15), (0x8, 5)], []⟩
  | .l120e0b => some ⟨0x1e8, [(39, 39), (50, 50), (51, 51)], [(0x160, 7), (0x30, 3), (0x28, 12),
      (0x20, 13), (0x18, 14), (0x10, 15), (0x8, 5)], []⟩
  | .l120e17 => some ⟨0x1e8, [(39, 39), (50, 50), (51, 51)], [(0x160, 7), (0x30, 3), (0x28, 12),
      (0x20, 13), (0x18, 14), (0x10, 15), (0x8, 5)], []⟩
  | .l120e9b => some ⟨0x1e8, [(39, 39), (50, 50), (51, 51)], [(0x160, 7), (0x30, 3), (0x28, 12),
      (0x20, 13), (0x18, 14), (0x10, 15), (0x8, 5)], []⟩
  | .l120f13 => some ⟨0x1e8, [(3, 7), (39, 39), (50, 50), (51, 51)], [(0x160, 7), (0x30, 3),
      (0x28, 12), (0x20, 13), (0x18, 14), (0x10, 15), (0x8, 5)], []⟩
  | _ => none

@[refine_layout] def frameAtG2 : Label.G2 → Refine.Activation → List Refine.Atom
  | .l1205b0 => fun fr =>
      [.gpr 4 fr.rsp, .reg 22 ⟨1, 0⟩, .gpr 1 fr.rcx, .gpr 2 fr.rdx, .gpr 3 fr.rbx, .gpr 5 fr.rbp,
       .gpr 6 fr.rsi, .gpr 7 fr.rdi, .gpr 8 fr.r8, .gpr 9 fr.r9, .gpr 12 fr.r12, .gpr 13 fr.r13,
       .gpr 14 fr.r14, .gpr 15 fr.r15, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x418) 0x418,
       .fact (fr.low.toNat + 0x418 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l120653 => fun fr =>
      [.gpr 4 (fr.rsp - 0x1e8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x160) 64 fr.rdi, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x418) 0x418,
       .fact (fr.low.toNat + 0x418 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l12065f => fun fr =>
      [.gpr 4 (fr.rsp - 0x1e8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x160) 64 fr.rdi, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x418) 0x418,
       .fact (fr.low.toNat + 0x418 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l120d03 => fun fr =>
      [.gpr 4 (fr.rsp - 0x1e8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x160) 64 fr.rdi, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x418) 0x418,
       .fact (fr.low.toNat + 0x418 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l120d83 => fun fr =>
      [.gpr 4 (fr.rsp - 0x1e8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x160) 64 fr.rdi, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x418) 0x418,
       .fact (fr.low.toNat + 0x418 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l120dff => fun fr =>
      [.gpr 4 (fr.rsp - 0x1e8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x160) 64 fr.rdi, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x418) 0x418,
       .fact (fr.low.toNat + 0x418 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l120e0b => fun fr =>
      [.gpr 4 (fr.rsp - 0x1e8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x160) 64 fr.rdi, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x418) 0x418,
       .fact (fr.low.toNat + 0x418 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l120e17 => fun fr =>
      [.gpr 4 (fr.rsp - 0x1e8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x160) 64 fr.rdi, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x418) 0x418,
       .fact (fr.low.toNat + 0x418 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l120e9b => fun fr =>
      [.gpr 4 (fr.rsp - 0x1e8), .reg 22 ⟨1, 0⟩, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x160) 64 fr.rdi, .mem (fr.rsp - 0x30) 64 fr.rbx,
       .mem (fr.rsp - 0x28) 64 fr.r12, .mem (fr.rsp - 0x20) 64 fr.r13,
       .mem (fr.rsp - 0x18) 64 fr.r14, .mem (fr.rsp - 0x10) 64 fr.r15,
       .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x418) 0x418,
       .fact (fr.low.toNat + 0x418 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8)]
  | .l120f13 => fun fr =>
      [.gpr 4 (fr.rsp - 0x1e8), .reg 22 ⟨1, 0⟩, .gpr 3 fr.rdi, .reg 39 ⟨32, fr.mxcsr⟩,
       .reg 50 ⟨16, fr.ftw⟩, .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x160) 64 fr.rdi,
       .mem (fr.rsp - 0x30) 64 fr.rbx, .mem (fr.rsp - 0x28) 64 fr.r12,
       .mem (fr.rsp - 0x20) 64 fr.r13, .mem (fr.rsp - 0x18) 64 fr.r14,
       .mem (fr.rsp - 0x10) 64 fr.r15, .mem (fr.rsp - 0x8) 64 fr.rbp, .readable fr.rsp 8,
       .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x418) 0x418, .fact (fr.low.toNat + 0x418 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8)]
  | _ => fun _ => []

def labelFrame : Label → Option Refine.LabelFrame
  | .g2 l => labelFrameG2 l
  | _ => none

@[refine_layout] def frameAt : Label → Refine.Activation → List Refine.Atom
  | .g2 l => frameAtG2 l
  | _ => fun _ => []

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

def closureCode : CodeMap := sectionCode textSection [(0x145f0, 0x2d4), (0x14930, 0x18a),
    (0x15950, 0x1000), (0x16950, 0x1000), (0x17950, 0x1000), (0x18950, 0x1000), (0x19950, 0xc17),
    (0x205b0, 0x97b), (0x27d50, 0x11)]

theorem closure_code : ∀ x ∈ closureCode, x ∈ fnCode :=
  sectionCode_sub (.head _) (by decide)

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
    (hcore : Refine.Atom.All code (lifted.locationOf .l1205b0 initial).arguments initial.external
      (core.atoms lab c fr p))
    (hstart : core.start lab = .l1205b0 := by rfl)
    (hentry : ∀ fr, atoms .l1205b0 fr = frameInfo.entryAtoms fr := by intro _; rfl)
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

end Fn1205b0

end K256.Proofs.Sec1.LIR
