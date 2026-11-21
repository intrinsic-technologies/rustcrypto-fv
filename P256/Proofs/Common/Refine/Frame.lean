import P256.Proofs.Common.Refine.Layout
import Prelude.Execution.CallingConvention

namespace P256.Proofs.Refine

open X86 X86.Machine X86.UserProcess X86Proofs P256.Proofs.CFG P256.Proofs.Lift Prelude
open Prelude.Execution.CallingConvention (mxcsrControlBits)

structure FrameInfo where
  entry : BitVec 64
  frameBytes : Nat
  stackBytes : Option Nat
  slots : List (Fin Reg.count × Nat)
  preserved : List (Fin Reg.count)
  fpPreserved : List (Fin Reg.count)
  clobbers : List (Fin Reg.count)
  callSlots : List (BitVec 64 × BitVec 64)

structure Activation where
  original : Ram
  rsp : BitVec 64
  ret : BitVec 64
  low : BitVec 64
  rbx : BitVec 64
  rbp : BitVec 64
  r12 : BitVec 64
  r13 : BitVec 64
  r14 : BitVec 64
  r15 : BitVec 64
  rdi : BitVec 64
  rsi : BitVec 64
  rdx : BitVec 64
  rcx : BitVec 64
  r8 : BitVec 64
  r9 : BitVec 64
  mxcsr : BitVec 32
  ftw : BitVec 16
  fcw : BitVec 16
  fs : X86.Helpers.Segment

namespace Activation

def entryReg (fr : Activation) : Nat → BitVec 64
  | 1 => fr.rcx
  | 2 => fr.rdx
  | 3 => fr.rbx
  | 4 => fr.rsp
  | 5 => fr.rbp
  | 6 => fr.rsi
  | 7 => fr.rdi
  | 8 => fr.r8
  | 9 => fr.r9
  | 12 => fr.r12
  | 13 => fr.r13
  | 14 => fr.r14
  | 15 => fr.r15
  | _ => 0

def entryValue (fr : Activation) : Nat → Value
  | 39 => ⟨32, fr.mxcsr⟩
  | 50 => ⟨16, fr.ftw⟩
  | 51 => ⟨16, fr.fcw⟩
  | r => ⟨64, fr.entryReg r⟩

def region (fr : Activation) : MemoryRegion :=
  ⟨fr.low.toNat, fr.rsp.toNat - fr.low.toNat⟩

def below (fr : Activation) (d : Nat) : BitVec 64 :=
  if d = 0 then fr.rsp else fr.rsp - BitVec.ofNat 64 d

def entryNumbers : List Nat := [1, 2, 3, 4, 5, 6, 7, 8, 9, 12, 13, 14, 15]

def calleeSavedNumbers : List Nat := [3, 5, 12, 13, 14, 15]

def argumentNumbers : List Nat := [7, 6, 2, 1, 8, 9]

theorem calleeSavedNumbers_sub : ∀ r ∈ calleeSavedNumbers, r ∈ entryNumbers := by decide

end Activation

attribute [refine_layout] Activation.region

structure LabelFrame where
  depth : Nat
  regs : List (Fin Reg.count × Nat)
  slots : List (Nat × Nat)
  callSlots : List (BitVec 64 × BitVec 64)

namespace FrameInfo

def window (m : FrameInfo) : Nat := m.stackBytes.getD m.frameBytes

def slotsLow (cs : List (BitVec 64 × BitVec 64)) : Nat :=
  (cs.map fun c => c.1.toNat).foldr min (2 ^ 64)

def slotsHigh (cs : List (BitVec 64 × BitVec 64)) : Nat :=
  (cs.map fun c => c.1.toNat + 8).foldr max 0

def callSlotAtoms (m : FrameInfo) (cs : List (BitVec 64 × BitVec 64)) (fr : Activation) :
    List Atom :=
  match cs with
  | [] => []
  | _ :: _ => cs.flatMap (fun c => [.readable c.1 8, .mem c.1 64 c.2]) ++
      [.fact (slotsHigh cs + m.window ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ slotsLow cs)]

def stackAtoms (m : FrameInfo) (fr : Activation) : List Atom :=
  [.readable fr.rsp 8, .mem fr.rsp 64 fr.ret, .fact (fr.ret.toNat < 2 ^ 32)] ++
  (if m.window = 0 then [.fact (fr.low.toNat ≤ fr.rsp.toNat)] else
    [.writable (fr.rsp - BitVec.ofNat 64 m.window) m.window,
      .fact (fr.low.toNat + m.window ≤ fr.rsp.toNat)]) ++
  [.fact (fr.rsp.toNat % 16 = 8)]

def frameAtoms (m : FrameInfo) (lf : LabelFrame) (fr : Activation) : List Atom :=
  .gpr 4 (fr.below lf.depth) :: .reg 22 ⟨1, 0⟩ ::
    (lf.regs.map fun x => .reg x.1 (fr.entryValue x.2)) ++
    (lf.slots.map fun x => .mem (fr.rsp - BitVec.ofNat 64 x.1) 64 (fr.entryReg x.2)) ++
    m.stackAtoms fr ++ m.callSlotAtoms lf.callSlots fr

def atomsAt (m : FrameInfo) : Option LabelFrame → Activation → List Atom
  | some lf, fr => m.frameAtoms lf fr
  | none, _ => []

def entryRegs : List (Fin Reg.count × Nat) :=
  [(1, 1), (2, 2), (3, 3), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (12, 12), (13, 13), (14, 14),
    (15, 15), (39, 39), (50, 50), (51, 51)]

def entryFrame (m : FrameInfo) : LabelFrame := ⟨0, entryRegs, [], m.callSlots⟩

def entryAtoms (m : FrameInfo) (fr : Activation) : List Atom := m.frameAtoms m.entryFrame fr

def doneAtoms (m : FrameInfo) (fr : Activation) : List Atom :=
  .gpr 4 (fr.rsp + 8) :: .reg 22 ⟨1, 0⟩ :: (m.preserved.map fun r => .gpr r (fr.entryReg r)) ++
    m.fpPreserved.map fun r => .reg r (fr.entryValue r)

end FrameInfo

structure LayoutCore {UOp : Nat → Type} {ULabel UValue UStore : Type} {usig : ULabel → Nat}
    {results : Nat} (P : Program UOp ULabel usig results) (D : Dialect UOp UValue UStore)
    (lifted : Lifted) (Ctx : Type) where

  start : ULabel → lifted.Label

  Params : ULabel → Type

  args : (l : ULabel) → Params l → Values UValue (usig l)

  store : (l : ULabel) → Params l → UStore

  atoms : (l : ULabel) → Ctx → Activation → Params l → List Atom

  Result : Type

  output : Result → Output UValue UStore results

  done : Ctx → Activation → Result → List Atom

  footprint : Ctx → Activation → List MemoryRegion

variable {UOp : Nat → Type} {ULabel UValue UStore : Type} {usig : ULabel → Nat} {results : Nat}
  {P : Program UOp ULabel usig results} {D : Dialect UOp UValue UStore} {lifted : Lifted}
  {Ctx : Type}

def Layout.withFrame (frameAt : lifted.Label → Activation → List Atom)
    (doneAt : Activation → List Atom) (core : LayoutCore P D lifted Ctx) :
    Layout P D lifted (Activation × Ctx) where
  start := core.start
  Params := core.Params
  args := core.args
  store := core.store
  atoms l c p := frameAt (core.start l) c.1 ++ core.atoms l c.2 c.1 p
  Result := core.Result
  output := core.output
  done c r := doneAt c.1 ++ core.done c.2 c.1 r
  retAddr c := c.1.ret
  original c := c.1.original
  regions c := c.1.region :: core.footprint c.2 c.1

structure FrameInfo.Pre (m : FrameInfo) (code : CodeMap) (fr : Activation) (s : RamState) :
    Prop where
  rip : s.RIP = m.entry
  original : s.external = fr.original
  regs : ∀ r ∈ Activation.entryNumbers, (Reg.ofIndex r).read s = ⟨64, fr.entryReg r⟩
  ret : memLoad fr.original fr.rsp 64 = fr.ret
  retLow : fr.ret.toNat < 2 ^ 32
  retOutside : ∀ x ∈ code, x.1 ≠ fr.ret
  slot : Readable fr.original fr.rsp 8
  window : 0 < m.window →
    Writable code fr.original (fr.rsp - BitVec.ofNat 64 m.window) m.window
  room : fr.low.toNat + m.window ≤ fr.rsp.toNat
  align : fr.rsp.toNat % 16 = 8
  callSlots : ∀ c ∈ m.callSlots, Readable fr.original c.1 8 ∧ memLoad fr.original c.1 64 = c.2
  callSlotsApart : m.callSlots ≠ [] → FrameInfo.slotsHigh m.callSlots + m.window ≤
    fr.rsp.toNat ∨ fr.rsp.toNat ≤ FrameInfo.slotsLow m.callSlots
  df : RFLAGS.DirectionFlagClear s.RFLAGS
  mxcsr : (Reg.ofIndex 39).read s = ⟨32, fr.mxcsr⟩
  ftw : (Reg.ofIndex 50).read s = ⟨16, fr.ftw⟩
  fcw : (Reg.ofIndex 51).read s = ⟨16, fr.fcw⟩
  fs : s.FS = fr.fs

structure FrameInfo.Post (m : FrameInfo) (fr : Activation) (footprint : List MemoryRegion)
    (t : RamState) : Prop where
  rip : t.RIP = fr.ret
  rsp : (Reg.ofIndex 4).read t = ⟨64, fr.rsp + 8⟩
  preserved : ∀ r ∈ m.preserved, (Reg.ofIndex r).read t = ⟨64, fr.entryReg r⟩
  df : RFLAGS.DirectionFlagClear t.RFLAGS
  mxcsrControl : mxcsrControlBits (((Reg.ofIndex 39).read t).get 32) = mxcsrControlBits fr.mxcsr
  ftw : (Reg.ofIndex 50).read t = ⟨16, fr.ftw⟩
  fcw : (Reg.ofIndex 51).read t = ⟨16, fr.fcw⟩
  fs : t.FS = fr.fs
  frame : RamWriteFrame fr.original t.external (fr.region :: footprint)

end P256.Proofs.Refine
