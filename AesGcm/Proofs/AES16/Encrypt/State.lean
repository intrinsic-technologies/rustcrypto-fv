import AesGcm.Proofs.Machine.Runtime.Guards
import AesGcm.Proofs.AES16.Encrypt.Algebra
import AesGcm.Proofs.Machine.Runtime.Call
import AesGcm.Proofs.Machine.LIR.Fn105100.Frame
import AesGcm.Proofs.Machine.LIR.Fn106960.Frame

namespace AesGcm.Proofs.Machine.AES16.Encrypt

open Standards.NIST.AES Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime Fixslice16

def entryLabel (use256 : Bool) : LIR.Label := if use256 then .l106960 else .l105100

def frameInfo (use256 : Bool) : FrameInfo :=
  if use256 then LIR.Fn106960.frameInfo else LIR.Fn105100.frameInfo

def frameAt (use256 : Bool) (label : LIR.Label) (fr : Activation) : List Atom :=
  if use256 then LIR.Fn106960.frameAt label fr else LIR.Fn105100.frameAt label fr

def buffer (use256 : Bool) (fr : Activation) : BitVec 64 :=
  fr.rsp - (if use256 then 112 else 104)

def Pre (code : CodeMap) (use256 : Bool) (key : Vector UInt8 (variant use256).keyBytes)
    (input : Standards.NIST.AES.Block) (fr : Activation) (mem : Ram) : Prop :=
  ScheduleIn (variant use256) key fr.rsi mem ∧
    Readable mem fr.rsi (16 * ((variant use256).Nr + 1)) ∧
    Readable mem fr.rdx 16 ∧ Fixslice.memoryBlock mem fr.rdx = Fixslice16.fromStandard input ∧
    Writable code mem fr.rdi 16 ∧
    (callStack fr).Disjoint (span fr.rdi 16) ∧
    (callStack fr).Disjoint (span fr.rdx 16) ∧
    (callStack fr).Disjoint (span fr.rsi (16 * ((variant use256).Nr + 1)))

structure WorkingState (code : CodeMap) (use256 : Bool)
    (key : Vector UInt8 (variant use256).keyBytes) (fr : Activation)
    (loc : LIR.lifted.Location) : Prop where
  frame : Atom.All code loc.arguments loc.store (frameAt use256 loc.label fr)
  typed : GPRsTyped loc.arguments
  schedule : ScheduleIn (variant use256) key fr.rsi loc.store
  readable : Readable loc.store fr.rsi (16 * ((variant use256).Nr + 1))
  writable : Writable code loc.store
    (fr.rsp - BitVec.ofNat 64 (frameInfo use256).window) (frameInfo use256).window
  written : RamWriteFrame fr.original loc.store [fr.region]

def delayedPlanes (planes keys : Planes16) : Planes16 :=
  fun p ↦ if p.val = 7 then planes p ^^^ keys p else planes p

structure LoopState (use256 : Bool) (key : Vector UInt8 (variant use256).keyBytes)
    (input : Standards.NIST.AES.Block) (fr : Activation) (j : Nat)
    (hj : 4 * j < (variant use256).Nr + 1) (loc : LIR.lifted.Location) : Prop where
  label : loc.label = (if use256 then .l1069f0 else .l105180)
  index : loc.arguments[12]'(by change 12 < 53; decide) =
    ⟨64, BitVec.ofNat 64 (32 * j + (if use256 then 7 else 0))⟩
  words : WordsAt loc.store (buffer use256 fr) 16
    (Vector.ofFn (delayedPlanes (roundState (variant use256) key input (4 * j))
      (expectedKey (variant use256) key ⟨4 * j, hj⟩)))
  tail : ((loc.arguments[0]'(by change 0 < 53; decide)).get 64).setWidth 16 =
    delayedPlanes (roundState (variant use256) key input (4 * j))
      (expectedKey (variant use256) key ⟨4 * j, hj⟩) 7

def planeReg (p : Fin 8) : Fin Reg.count :=
  (#v[10, 9, 8, 7, 6, 2, 1, 0] : Vector (Fin Reg.count) 8)[p]

structure FinalState (use256 : Bool) (key : Vector UInt8 (variant use256).keyBytes)
    (input : Standards.NIST.AES.Block) (fr : Activation) (loc : LIR.lifted.Location) : Prop where
  label : loc.label = (if use256 then .l106ebc else .l105636)
  words : WordsAt loc.store (buffer use256 fr) 16
    (Vector.ofFn (roundState (variant use256) key input ((variant use256).Nr - 1)))
  regs : ∀ p : Fin 8,
    ((loc.arguments[(planeReg p).val]'(by change (planeReg p).val < 53; exact (planeReg p).isLt)).get 64).setWidth 16 =
      roundState (variant use256) key input ((variant use256).Nr - 1) p

def Result (code : CodeMap) (use256 : Bool) (key : Vector UInt8 (variant use256).keyBytes)
    (input : Standards.NIST.AES.Block) (fr : Activation)
    (output : Output Value Ram Reg.count) : Prop :=
  output.tag = some ⟨64, fr.ret⟩ ∧
    Atom.All code output.values output.store ((frameInfo use256).doneAtoms fr) ∧
    GPRsTyped output.values ∧
    RamWriteFrame fr.original output.store [fr.region, span fr.rdi 16] ∧
    Fixslice.memoryBlock output.store fr.rdi =
      Fixslice16.fromStandard (cipher (variant use256) key input)


theorem key_outside {v : Variant} {fr : Activation} {mem : Ram}
    (hlow : fr.low.toNat ≤ fr.rsp.toNat)
    (hread : Readable mem fr.rsi (16 * (v.Nr + 1)))
    (hsep : (callStack fr).Disjoint (span fr.rsi (16 * (v.Nr + 1)))) :
    Outside [fr.region] fr.rsi (16 * (v.Nr + 1)) := by
  have hn : 0 < 16 * (v.Nr + 1) := by omega
  have hbound := disjoint_bounds fr.low.toNat (fr.rsp.toNat + 8 - fr.low.toNat)
    fr.rsi.toNat (16 * (v.Nr + 1)) (by omega) hn hsep
  refine ⟨Nat.le_trans hread.low (by decide), ?_⟩
  intro r hr
  have he : r = fr.region := List.mem_singleton.mp hr
  subst r
  simp only [Activation.region]
  omega

theorem WorkingState.advance {code : CodeMap} {use256 : Bool}
    {key : Vector UInt8 (variant use256).keyBytes} {fr : Activation}
    {before after : LIR.lifted.Location} (h : WorkingState code use256 key fr before)
    (hframe : Atom.All code after.arguments after.store (frameAt use256 after.label fr))
    (htyped : GPRsTyped after.arguments)
    (hstep : RamWriteFrame before.store after.store [fr.region])
    (houtside : Outside [fr.region] fr.rsi (16 * ((variant use256).Nr + 1))) :
    WorkingState code use256 key fr after where
  frame := hframe
  typed := htyped
  schedule := scheduleIn_of_frame h.schedule hstep houtside
  readable := h.readable.of_frame hstep
  writable := h.writable.of_frame hstep
  written := h.written.trans hstep (by
    intro r hr
    exact ⟨r, hr, Nat.le_refl _, Nat.le_refl _⟩)

end AesGcm.Proofs.Machine.AES16.Encrypt
