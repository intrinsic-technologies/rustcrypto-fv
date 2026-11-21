import K256.Proofs.Sec1.Affine.Frame
import K256.Proofs.Sec1.Affine.Finish

namespace K256.Proofs.Sec1.Affine

open Prelude X86 X86.Machine X86.UserProcess X86Proofs K256.Spec.Program
open K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Sec1.LIR

theorem savedWithin {s : RamState} {bytes : ByteArray} (call : ValidCall publicKeyFromSec1Bytes s [bytes]) :
    RegionsWithin [⟨((activation s).rsp - 40).toNat, 40⟩] (Parser.affineWrites (s.regValue .rsp - 600)) := by
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  refine ⟨_, List.mem_cons_self, ?_, ?_⟩
  all_goals
    change _ ≤ _
    dsimp only [activation, Parser.affineWrites]
    rw [show s.regValue .rsp - 600 - 8 - 40 = s.regValue .rsp - 648 by bv_omega,
      show s.regValue .rsp - 600 - 1200 = s.regValue .rsp - 1800 by bv_omega,
      rootStackOffset call 648 (by decide), rootStackOffset call 1800 (by decide)]
  · exact Nat.sub_le_sub_left (by decide) _
  · have room : 1928 ≤ (s.regValue .rsp).toNat := call.stackAvailable.2.2.1
    change (s.regValue .rsp).toNat - 648 + 40 ≤ (s.regValue .rsp).toNat - 1800 + 1192
    omega

theorem EntryAt.savedFrame {s : RamState} {bytes : ByteArray} {args : Values Value Reg.count} {m : Ram}
    (call : ValidCall publicKeyFromSec1Bytes s [bytes]) (e : EntryAt s bytes args m)
    (writes : RamWriteFrame m (saveRegisters args m) [⟨((activation s).rsp - 40).toNat,40⟩]) :
    RamWriteFrame s.external (saveRegisters args m) [Stack.region s publicKeyFromSec1Bytes.minStackBytes] := by
  apply (e.stackFrame call).trans writes
  intro r hr
  obtain rfl := List.mem_singleton.mp hr
  have full := Parser.stackRange (off := 648) (n := 40) call (by decide) (by decide)
  obtain ⟨r, hr, within⟩ := full
  refine ⟨r, hr, ?_, ?_⟩
  all_goals
    dsimp only [activation]
    rw [show s.regValue .rsp - 600 - 8 - 40 = s.regValue .rsp - 648 by bv_omega]
  · exact within.1
  · exact within.2.1

theorem EntryAt.returnedRegisters {s : RamState} {bytes : ByteArray} {args : Values Value Reg.count} {m : Ram}
    {out : Output Value Ram Reg.count} (call : ValidCall publicKeyFromSec1Bytes s [bytes])
    (e : EntryAt s bytes args m) (done_ : Atom.All Extracted.programImage out.values out.store
      (Fn121480.doneAt (activation s))) : out.values[4] = ⟨64,s.regValue .rsp - 600⟩ ∧
    ∀ i : Fin Reg.count, i.val ∈ [3,5,12,13,14,15,22,39,50,51] → out.values[i] = args[i] := by
  simp only [Fn121480.doneAt, Atom.All, Atom.Holds] at done_
  obtain ⟨sp,df,bx,bp,r12,r13,r14,r15,mx,ft,fc,_⟩ := done_
  obtain ⟨initialDF, kept⟩ := e.registers call
  refine ⟨sp.trans (congrArg (Value.mk 64) (by dsimp only [activation]; bv_omega)), ?_⟩
  rintro ⟨i,hi⟩ h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact df.trans initialDF.symm
    | exact bx.trans (kept 3 (by decide)).symm
    | exact bp.trans (kept 5 (by decide)).symm
    | exact r12.trans (kept 12 (by decide)).symm
    | exact r13.trans (kept 13 (by decide)).symm
    | exact r14.trans (kept 14 (by decide)).symm
    | exact r15.trans (kept 15 (by decide)).symm
    | exact mx.trans (kept 39 (by decide)).symm
    | exact ft.trans (kept 50 (by decide)).symm
    | exact fc.trans (kept 51 (by decide)).symm

theorem decodeIdentityCall {s : RamState} {bytes : ByteArray} {args : Values Value Reg.count} {m : Ram}
    (call : ValidCall publicKeyFromSec1Bytes s [bytes]) (e : EntryAt s bytes args m)
    (zero : bytes.data[0]?.getD 0 = 0) :
    ∃ out, program.Exec (dialect Extracted.programImage) ⟨⟨.l121480,args,m⟩,[]⟩ out ∧
      ReturnAt (s.regValue .rsp-600) bytes args m out := by
  let fr := activation s
  obtain ⟨next, entry, _, cx, _, atoms, saved, _⟩ := e.start call
  rw [zero] at entry cx
  change program.runBlock _ _ = .jump ⟨.l1214d0,next,saveRegisters args m⟩ at entry
  have image := (Parser.inputs_of_stackFrame call (e.savedFrame call saved)).2
  have w := activationOutputWritable call (e.savedFrame call saved)
  have geometry := activationOutputAbove call
  obtain ⟨out, run, tag, done_, _, written, _, flag⟩ := finishIdentity Common.fnCode_subset_programImage
    fr next _ atoms (by rw [cx]; rfl) image w (identityWords_apart w) (.inr geometry)
  obtain ⟨sp, kept⟩ := e.returnedRegisters call done_
  have saved' := (RamWriteFrame.refl m (Parser.affineWrites (s.regValue .rsp-600))).trans saved (savedWithin call)
  have all := saved'.trans written (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    exact ⟨_, List.mem_cons_of_mem _ (List.mem_singleton_self _), Nat.le_refl _, Nat.le_refl _⟩)
  refine ⟨out, Program.Exec.of_sem ((Parser.reaches_jump entry).exec run.sem), tag, sp, kept, all, ?_⟩
  rw [ite_eq_left zero]
  change memLoad out.store (s.regValue .rsp-600+160+88) 8 = 1 at flag
  rwa [BitVec.add_assoc] at flag

end K256.Proofs.Sec1.Affine
