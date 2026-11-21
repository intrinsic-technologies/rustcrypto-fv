import K256.Proofs.Verify.LIR.Program
import K256.Proofs.Common.Refine.Contract
import K256.Proofs.Common.Refine.Lemma.SysVEntry

namespace K256.Proofs.Verify.LIR

open X86 X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Sec1.LIR K256.Proofs.Generate.LIR K256.Proofs.Ecdh.LIR

namespace Fn103ac0

def frameInfo : Refine.FrameInfo where
  entry := 0x103ac0
  frameBytes := 0xb8
  stackBytes := some 0x230
  slots := [(3, 0x10), (14, 0x8)]
  preserved := [3, 5, 12, 13, 14, 15]
  fpPreserved := [39, 50, 51]
  clobbers := [0, 1, 2, 6, 7, 8, 9, 10, 11]
  callSlots := [(0x203dd0, 0x12a820), (0x203de0, 0x129770), (0x203e20, 0x100a20)]

def labelFrameG4 : Label.G4 → Option Refine.LabelFrame
  | .l103ac0 => some ⟨0x0, [(1, 1), (2, 2), (3, 3), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9),
      (12, 12), (13, 13), (14, 14), (15, 15), (39, 39), (50, 50),
      (51, 51)], [], [(0x203dd0, 0x12a820), (0x203de0, 0x129770), (0x203e20, 0x100a20)]⟩
  | .l103b07 => some ⟨0xb8, [(3, 7), (5, 5), (12, 12), (13, 13), (14, 6), (15, 15), (39, 39),
      (50, 50), (51, 51)], [(0x10, 3), (0x8, 14)], [(0x203dd0, 0x12a820), (0x203de0, 0x129770),
      (0x203e20, 0x100a20)]⟩
  | .l103b12 => some ⟨0xb8, [(3, 7), (5, 5), (12, 12), (13, 13), (14, 6), (15, 15), (39, 39),
      (50, 50), (51, 51)], [(0x10, 3), (0x8, 14)], [(0x203dd0, 0x12a820), (0x203de0, 0x129770),
      (0x203e20, 0x100a20)]⟩
  | .l103b75 => some ⟨0xb8, [(3, 7), (5, 5), (12, 12), (13, 13), (14, 6), (15, 15), (39, 39),
      (50, 50), (51, 51)], [(0x10, 3), (0x8, 14)], []⟩
  | .l103b80 => some ⟨0xb8, [(3, 7), (5, 5), (12, 12), (13, 13), (14, 6), (15, 15), (39, 39),
      (50, 50), (51, 51)], [(0x10, 3), (0x8, 14)], []⟩
  | .l103bf1 => some ⟨0xb8, [(3, 7), (5, 5), (12, 12), (13, 13), (14, 6), (15, 15), (39, 39),
      (50, 50), (51, 51)], [(0x10, 3), (0x8, 14)], []⟩
  | .l103bfb => some ⟨0xb8, [(3, 7), (5, 5), (12, 12), (13, 13), (14, 6), (15, 15), (39, 39),
      (50, 50), (51, 51)], [(0x10, 3), (0x8, 14)], []⟩
  | .l103bff => some ⟨0xb8, [(3, 7), (5, 5), (12, 12), (13, 13), (14, 6), (15, 15), (39, 39),
      (50, 50), (51, 51)], [(0x10, 3), (0x8, 14)], []⟩
  | .l103c3f => some ⟨0xb8, [(3, 7), (5, 5), (12, 12), (13, 13), (14, 6), (15, 15), (39, 39),
      (50, 50), (51, 51)], [(0x10, 3), (0x8, 14)], []⟩
  | .l103c49 => some ⟨0xb8, [(3, 7), (5, 5), (12, 12), (13, 13), (14, 6), (15, 15), (39, 39),
      (50, 50), (51, 51)], [(0x10, 3), (0x8, 14)], []⟩
  | .l103c4d => some ⟨0xb8, [(3, 7), (5, 5), (12, 12), (13, 13), (14, 6), (15, 15), (39, 39),
      (50, 50), (51, 51)], [(0x10, 3), (0x8, 14)], []⟩
  | .l103c5c => some ⟨0xb8, [(3, 7), (5, 5), (12, 12), (13, 13), (14, 6), (15, 15), (39, 39),
      (50, 50), (51, 51)], [(0x10, 3), (0x8, 14)], []⟩
  | .l103c6a => some ⟨0xb8, [(3, 7), (5, 5), (12, 12), (13, 13), (14, 6), (15, 15), (39, 39),
      (50, 50), (51, 51)], [(0x10, 3), (0x8, 14)], []⟩
  | _ => none

@[refine_layout] def frameAtG4 : Label.G4 → Refine.Activation → List Refine.Atom
  | .l103ac0 => fun fr =>
      [.gpr 4 fr.rsp, .reg 22 ⟨1, 0⟩, .gpr 1 fr.rcx, .gpr 2 fr.rdx, .gpr 3 fr.rbx, .gpr 5 fr.rbp,
       .gpr 6 fr.rsi, .gpr 7 fr.rdi, .gpr 8 fr.r8, .gpr 9 fr.r9, .gpr 12 fr.r12, .gpr 13 fr.r13,
       .gpr 14 fr.r14, .gpr 15 fr.r15, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .readable fr.rsp 8, .mem fr.rsp 64 fr.ret,
       .fact (fr.ret.toNat < 2 ^ (32 : Nat)), .writable (fr.rsp - 0x230) 0x230,
       .fact (fr.low.toNat + 0x230 ≤ fr.rsp.toNat), .fact (fr.rsp.toNat % 16 = 8),
       .readable 0x203dd0 8, .mem 0x203dd0 64 0x12a820, .readable 0x203de0 8,
       .mem 0x203de0 64 0x129770, .readable 0x203e20 8, .mem 0x203e20 64 0x100a20,
       .fact (0x204058 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203dd0)]
  | .l103b07 => fun fr =>
      [.gpr 4 (fr.rsp - 0xb8), .reg 22 ⟨1, 0⟩, .gpr 3 fr.rdi, .gpr 5 fr.rbp, .gpr 12 fr.r12,
       .gpr 13 fr.r13, .gpr 14 fr.rsi, .gpr 15 fr.r15, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x10) 64 fr.rbx, .mem (fr.rsp - 0x8) 64 fr.r14,
       .readable fr.rsp 8, .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x230) 0x230, .fact (fr.low.toNat + 0x230 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203dd0 8, .mem 0x203dd0 64 0x12a820,
       .readable 0x203de0 8, .mem 0x203de0 64 0x129770, .readable 0x203e20 8,
       .mem 0x203e20 64 0x100a20, .fact (0x204058 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203dd0)]
  | .l103b12 => fun fr =>
      [.gpr 4 (fr.rsp - 0xb8), .reg 22 ⟨1, 0⟩, .gpr 3 fr.rdi, .gpr 5 fr.rbp, .gpr 12 fr.r12,
       .gpr 13 fr.r13, .gpr 14 fr.rsi, .gpr 15 fr.r15, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x10) 64 fr.rbx, .mem (fr.rsp - 0x8) 64 fr.r14,
       .readable fr.rsp 8, .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x230) 0x230, .fact (fr.low.toNat + 0x230 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8), .readable 0x203dd0 8, .mem 0x203dd0 64 0x12a820,
       .readable 0x203de0 8, .mem 0x203de0 64 0x129770, .readable 0x203e20 8,
       .mem 0x203e20 64 0x100a20, .fact (0x204058 ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x203dd0)]
  | .l103b75 => fun fr =>
      [.gpr 4 (fr.rsp - 0xb8), .reg 22 ⟨1, 0⟩, .gpr 3 fr.rdi, .gpr 5 fr.rbp, .gpr 12 fr.r12,
       .gpr 13 fr.r13, .gpr 14 fr.rsi, .gpr 15 fr.r15, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x10) 64 fr.rbx, .mem (fr.rsp - 0x8) 64 fr.r14,
       .readable fr.rsp 8, .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x230) 0x230, .fact (fr.low.toNat + 0x230 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8)]
  | .l103b80 => fun fr =>
      [.gpr 4 (fr.rsp - 0xb8), .reg 22 ⟨1, 0⟩, .gpr 3 fr.rdi, .gpr 5 fr.rbp, .gpr 12 fr.r12,
       .gpr 13 fr.r13, .gpr 14 fr.rsi, .gpr 15 fr.r15, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x10) 64 fr.rbx, .mem (fr.rsp - 0x8) 64 fr.r14,
       .readable fr.rsp 8, .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x230) 0x230, .fact (fr.low.toNat + 0x230 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8)]
  | .l103bf1 => fun fr =>
      [.gpr 4 (fr.rsp - 0xb8), .reg 22 ⟨1, 0⟩, .gpr 3 fr.rdi, .gpr 5 fr.rbp, .gpr 12 fr.r12,
       .gpr 13 fr.r13, .gpr 14 fr.rsi, .gpr 15 fr.r15, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x10) 64 fr.rbx, .mem (fr.rsp - 0x8) 64 fr.r14,
       .readable fr.rsp 8, .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x230) 0x230, .fact (fr.low.toNat + 0x230 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8)]
  | .l103bfb => fun fr =>
      [.gpr 4 (fr.rsp - 0xb8), .reg 22 ⟨1, 0⟩, .gpr 3 fr.rdi, .gpr 5 fr.rbp, .gpr 12 fr.r12,
       .gpr 13 fr.r13, .gpr 14 fr.rsi, .gpr 15 fr.r15, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x10) 64 fr.rbx, .mem (fr.rsp - 0x8) 64 fr.r14,
       .readable fr.rsp 8, .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x230) 0x230, .fact (fr.low.toNat + 0x230 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8)]
  | .l103bff => fun fr =>
      [.gpr 4 (fr.rsp - 0xb8), .reg 22 ⟨1, 0⟩, .gpr 3 fr.rdi, .gpr 5 fr.rbp, .gpr 12 fr.r12,
       .gpr 13 fr.r13, .gpr 14 fr.rsi, .gpr 15 fr.r15, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x10) 64 fr.rbx, .mem (fr.rsp - 0x8) 64 fr.r14,
       .readable fr.rsp 8, .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x230) 0x230, .fact (fr.low.toNat + 0x230 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8)]
  | .l103c3f => fun fr =>
      [.gpr 4 (fr.rsp - 0xb8), .reg 22 ⟨1, 0⟩, .gpr 3 fr.rdi, .gpr 5 fr.rbp, .gpr 12 fr.r12,
       .gpr 13 fr.r13, .gpr 14 fr.rsi, .gpr 15 fr.r15, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x10) 64 fr.rbx, .mem (fr.rsp - 0x8) 64 fr.r14,
       .readable fr.rsp 8, .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x230) 0x230, .fact (fr.low.toNat + 0x230 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8)]
  | .l103c49 => fun fr =>
      [.gpr 4 (fr.rsp - 0xb8), .reg 22 ⟨1, 0⟩, .gpr 3 fr.rdi, .gpr 5 fr.rbp, .gpr 12 fr.r12,
       .gpr 13 fr.r13, .gpr 14 fr.rsi, .gpr 15 fr.r15, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x10) 64 fr.rbx, .mem (fr.rsp - 0x8) 64 fr.r14,
       .readable fr.rsp 8, .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x230) 0x230, .fact (fr.low.toNat + 0x230 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8)]
  | .l103c4d => fun fr =>
      [.gpr 4 (fr.rsp - 0xb8), .reg 22 ⟨1, 0⟩, .gpr 3 fr.rdi, .gpr 5 fr.rbp, .gpr 12 fr.r12,
       .gpr 13 fr.r13, .gpr 14 fr.rsi, .gpr 15 fr.r15, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x10) 64 fr.rbx, .mem (fr.rsp - 0x8) 64 fr.r14,
       .readable fr.rsp 8, .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x230) 0x230, .fact (fr.low.toNat + 0x230 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8)]
  | .l103c5c => fun fr =>
      [.gpr 4 (fr.rsp - 0xb8), .reg 22 ⟨1, 0⟩, .gpr 3 fr.rdi, .gpr 5 fr.rbp, .gpr 12 fr.r12,
       .gpr 13 fr.r13, .gpr 14 fr.rsi, .gpr 15 fr.r15, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x10) 64 fr.rbx, .mem (fr.rsp - 0x8) 64 fr.r14,
       .readable fr.rsp 8, .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x230) 0x230, .fact (fr.low.toNat + 0x230 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8)]
  | .l103c6a => fun fr =>
      [.gpr 4 (fr.rsp - 0xb8), .reg 22 ⟨1, 0⟩, .gpr 3 fr.rdi, .gpr 5 fr.rbp, .gpr 12 fr.r12,
       .gpr 13 fr.r13, .gpr 14 fr.rsi, .gpr 15 fr.r15, .reg 39 ⟨32, fr.mxcsr⟩, .reg 50 ⟨16, fr.ftw⟩,
       .reg 51 ⟨16, fr.fcw⟩, .mem (fr.rsp - 0x10) 64 fr.rbx, .mem (fr.rsp - 0x8) 64 fr.r14,
       .readable fr.rsp 8, .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ (32 : Nat)),
       .writable (fr.rsp - 0x230) 0x230, .fact (fr.low.toNat + 0x230 ≤ fr.rsp.toNat),
       .fact (fr.rsp.toNat % 16 = 8)]
  | _ => fun _ => []

def labelFrame : Label → Option Refine.LabelFrame
  | .g4 l => labelFrameG4 l
  | _ => none

@[refine_layout] def frameAt : Label → Refine.Activation → List Refine.Atom
  | .g4 l => frameAtG4 l
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

def closureCode : CodeMap := sectionCode textSection [(0xa20, 0x2), (0x3ac0, 0x235),
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
    (hcore : Refine.Atom.All code (lifted.locationOf .l103ac0 initial).arguments initial.external
      (core.atoms lab c fr p))
    (hstart : core.start lab = .l103ac0 := by rfl)
    (hentry : ∀ fr, atoms .l103ac0 fr = frameInfo.entryAtoms fr := by intro _; rfl)
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

end Fn103ac0

end K256.Proofs.Verify.LIR
