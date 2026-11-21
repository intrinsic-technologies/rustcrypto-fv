import AesGcm.Proofs.Machine.LIR.Aes128gcmEncryptInPlace.Frame
import AesGcm.Proofs.Machine.LIR.Fn102520.Frame
import AesGcm.Proofs.Machine.Runtime.StackGeometry

namespace AesGcm.Proofs.Machine.Entry.InPlaceEncrypt

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

theorem core_return_frame {code : CodeMap} {fr child : Activation} {p : BitVec 64} {n : Nat}
    {args : Values Value Reg.count} {before : Ram} {out : Output Value Ram Reg.count}
    (working : Atom.All code args before (LIR.Aes128gcmEncryptInPlace.frameAt .l1013c8 fr))
    (outer : RamWriteFrame fr.original before [fr.region])
    (setup : RamWriteFrame before child.original [span (fr.rsp - 480) 64])
    (sp : child.rsp = fr.rsp - 480) (low : child.low = fr.rsp - 2848)
    (result : child.rdi = fr.rsp - 457)
    (rbx : child.rbx = fr.r9) (rbp : child.rbp = args[5].get 64)
    (r12 : child.r12 = fr.rdx) (r13 : child.r13 = fr.rsi) (r14 : child.r14 = fr.r8)
    (r15 : child.r15 = fr.rcx)
    (mx : child.mxcsr = fr.mxcsr) (ft : child.ftw = fr.ftw) (fc : child.fcw = fr.fcw)
    (sep : (callStack fr).Disjoint (span p n)) (hp : p = fr.r8 ∨ n = 0)
    (done : Atom.All code out.values out.store (LIR.Fn102520.frameInfo.doneAtoms child))
    (writes : RamWriteFrame child.original out.store [child.region, span child.rdi 17, span p n]) :
    Atom.All code out.values out.store (LIR.Aes128gcmEncryptInPlace.frameAt .l101409 fr) ∧
    out.values[5].get 64 = args[5].get 64 ∧
    RamWriteFrame fr.original out.store [fr.region, span fr.r8 n] := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, saved3, saved12, saved13, saved14,
    saved15, saved5, retRead, savedRet, retLow, stack, room, align, _⟩ := working
  change Readable before fr.rsp 8 at retRead
  change Writable code before (fr.rsp - 2848) 2848 at stack
  change fr.low.toNat + 2848 ≤ fr.rsp.toNat at room
  have addr (offset : Nat) (h : offset ≤ 2848) :
      (fr.rsp - BitVec.ofNat 64 offset).toNat = fr.rsp.toNat - offset :=
    stack_sub_toNat fr room h
  have setupNat : (fr.rsp - (480 : BitVec 64)).toNat = fr.rsp.toNat - 480 :=
    addr 480 (by decide)
  have lowNat : (fr.rsp - (2848 : BitVec 64)).toNat = fr.rsp.toNat - 2848 :=
    addr 2848 (by decide)
  have resultNat : child.rdi.toNat = fr.rsp.toNat - 457 := by
    rw [result]
    exact addr 457 (by decide)
  let scratch := span (fr.rsp - 2848) 2432
  have throughSetup : RamWriteFrame before child.original [scratch, span p n] := by
    apply (RamWriteFrame.refl _ _).trans setup
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    refine ⟨scratch, List.mem_cons_self .., ?_, ?_⟩ <;>
      simp only [scratch, span, setupNat, lowNat] <;> omega
  have through : RamWriteFrame before out.store [scratch, span p n] := by
    apply throughSetup.trans writes
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl
    · refine ⟨scratch, List.mem_cons_self .., ?_, ?_⟩ <;>
        simp only [scratch, span, Activation.region, low, sp, setupNat, lowNat] <;> omega
    · refine ⟨scratch, List.mem_cons_self .., ?_, ?_⟩ <;>
        simp only [scratch, span, lowNat, resultNat] <;> omega
    · exact ⟨span p n, List.mem_cons_of_mem _ (List.mem_singleton_self _),
        Nat.le_refl _, Nat.le_refl _⟩
  have saved (offset : Nat) (h : offset ≤ 48) :
      memLoad out.store (fr.rsp - BitVec.ofNat 64 offset) 64 =
        memLoad before (fr.rsp - BitVec.ofNat 64 offset) 64 := by
    apply memLoad_congr
    intro i hi
    change i < 8 at hi
    let x := fr.rsp - BitVec.ofNat 64 offset + BitVec.ofNat 64 i
    have retBound := retRead.low
    have xNat : x.toNat = fr.rsp.toNat - offset + i := by
      dsimp only [x]
      rw [BitVec.toNat_add, addr offset (by omega), BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt (a := i) (by omega), Nat.mod_eq_of_lt (by omega)]
    have xStack : (callStack fr).Contains x.toNat := by
      simp only [MemoryRegion.Contains, callStack, xNat]
      omega
    have outside : Outside [scratch, span p n] x 1 := by
      refine ⟨by omega, ?_⟩
      intro r hr
      rcases List.mem_cons.mp hr with rfl | hr
      · right
        simp only [scratch, span, lowNat, xNat]
        omega
      · obtain rfl := List.mem_singleton.mp hr
        have hsep := sep x.toNat xStack
        simp only [MemoryRegion.Contains, span] at hsep ⊢
        omega
    simp only [memByte, PhysicalMemory.read]
    rw [through.outside x outside]
  have finalFrame : RamWriteFrame fr.original out.store [fr.region, span fr.r8 n] := by
    refine ⟨?_, fun x hx => through.present x (outer.present x hx)⟩
    intro x hx
    have outsideStack := hx.2 fr.region (List.mem_cons_self ..)
    rw [← outer.outside x ⟨hx.1, fun r hr => by
      obtain rfl := List.mem_singleton.mp hr
      exact outsideStack⟩]
    apply through.outside x
    refine ⟨hx.1, ?_⟩
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · simp only [Activation.region] at outsideStack
      simp only [scratch, span, lowNat]
      omega
    · obtain rfl := List.mem_singleton.mp hr
      rcases hp with rfl | empty
      · exact hx.2 (span fr.r8 n) (List.mem_cons_of_mem _ (List.mem_singleton_self _))
      · simp only [span, empty, Nat.add_zero]
        omega
  rw [← LIR.Fn102520.doneAt_canonical] at done
  obtain ⟨doneSP, doneDF, done3, done5, done12, done13, done14, done15, doneMX, doneFT, doneFC, _⟩ :=
    done
  change out.values[4] = ⟨64, child.rsp + 8⟩ at doneSP
  change out.values[5] = ⟨64, child.rbp⟩ at done5
  have rsp : child.rsp + 8 = fr.rsp - 472 := by rw [sp]; bv_omega
  refine ⟨⟨rsp ▸ doneSP, doneDF, rbx ▸ done3, r12 ▸ done12, r13 ▸ done13, r14 ▸ done14,
    r15 ▸ done15, mx ▸ doneMX, ft ▸ doneFT, fc ▸ doneFC, ?_, ?_, ?_, ?_, ?_, ?_,
    retRead.of_frame through, ?_, retLow, stack.of_frame through, room, align, trivial⟩,
    ?_, finalFrame⟩
  · exact (saved 48 (by decide)).trans saved3
  · exact (saved 40 (by decide)).trans saved12
  · exact (saved 32 (by decide)).trans saved13
  · exact (saved 24 (by decide)).trans saved14
  · exact (saved 16 (by decide)).trans saved15
  · exact (saved 8 (by decide)).trans saved5
  · have savedAtRet : memLoad out.store fr.rsp 64 = memLoad before fr.rsp 64 := by
      simpa only [BitVec.sub_zero] using saved 0 (by decide)
    exact savedAtRet.trans savedRet
  · rw [done5, rbp]
    exact BitVec.setWidth_eq _

end AesGcm.Proofs.Machine.Entry.InPlaceEncrypt
