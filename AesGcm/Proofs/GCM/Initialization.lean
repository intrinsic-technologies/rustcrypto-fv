import AesGcm.Proofs.GCM.Prefix
import AesGcm.Proofs.GCM.HashInitialization
import AesGcm.Proofs.GCM.Finish
import AesGcm.Proofs.Machine.GcmContext
import AesGcm.Proofs.Machine.GHASHUpdate.Initialize
import AesGcm.Proofs.Machine.Runtime.Memcpy
import AesGcm.Proofs.Machine.LIR.Fn102040.Frame
import AesGcm.Proofs.Machine.LIR.Fn102180.Frame

namespace AesGcm.Proofs.Machine.GCM

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

theorem initialize_callContract (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (key : Vector UInt8 (AES16.variant use256).keyBytes) :
    CallContract LIR.lifted code (if use256 then .l102180 else .l102040)
      (if use256 then LIR.Fn102180.frameInfo else LIR.Fn102040.frameInfo)
      (fun fr ↦ [span fr.rdi (GcmContext.size (AES16.variant use256))])
      (fun fr mem ↦ AES16.ScheduleIn (AES16.variant use256) key fr.rsi mem ∧
        Readable mem fr.rsi (16 * ((AES16.variant use256).Nr + 1)) ∧
        Writable code mem fr.rdi (GcmContext.size (AES16.variant use256)) ∧
        (callStack fr).Disjoint (span fr.rsi (16 * ((AES16.variant use256).Nr + 1))) ∧
        (callStack fr).Disjoint (span fr.rdi (GcmContext.size (AES16.variant use256))) ∧
        (span fr.rdi (GcmContext.size (AES16.variant use256))).Disjoint
          (span fr.rsi (16 * ((AES16.variant use256).Nr + 1))) ∧
        (span fr.rdi 32).Disjoint (span 0x201208 8))
      (fun fr mem ↦ GcmContext.ContextIn (AES16.variant use256) key fr.rdi mem) := by
  intro fr loc hlabel hstore hentry hTypes hpre
  rw [hstore] at hpre
  rcases hpre with ⟨hschedule, hr, hw, hsrcsep, hdstsep, hdatasep, hslotsep⟩
  let v := AES16.variant use256
  let n := 16 * (v.Nr + 1)
  let full := [fr.region, span fr.rdi (GcmContext.size v)]
  have npos : 0 < n := by cases use256 <;> decide
  have size32 : 32 ≤ GcmContext.size v := by dsimp only [GcmContext.size]; omega
  have hlow : fr.low.toNat ≤ fr.rsp.toNat := by
    cases use256
    all_goals
      have hh := hentry.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
      change fr.low.toNat + _ ≤ fr.rsp.toNat at hh
      omega
  have srcBounds := disjoint_bounds fr.low.toNat (fr.rsp.toNat + 8 - fr.low.toNat)
    fr.rsi.toNat n (by omega) npos hsrcsep
  have dataBounds := disjoint_bounds fr.rdi.toNat (GcmContext.size v) fr.rsi.toNat n
    (by omega) npos hdatasep
  have sourceOutside : Outside full fr.rsi n := by
    refine ⟨by have hh := hr.low; change fr.rsi.toNat + n ≤ 2^32 at hh; omega, ?_⟩
    intro r hr'
    simp only [full, List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · simp only [Activation.region]
      omega
    · simp only [span]
      omega
  have dest32sep : (callStack fr).Disjoint (span fr.rdi 32) := by
    intro x hx hd
    apply hdstsep x hx
    change 32 ≤ GcmContext.size (AES16.variant use256) at size32
    simp only [MemoryRegion.Contains, span] at hd ⊢
    omega
  have slotBounds := disjoint_bounds fr.rdi.toNat 32 0x201208 8
    (by decide) (by decide) hslotsep
  obtain ⟨first, hprefix, hfirstLabel, hfirstWorking, hfirstTypes, hprefixFrame, hblock⟩ :=
    GCM.prefix use256 code hcode key fr loc hlabel hstore hentry hTypes hschedule hr hsrcsep
  have firstFrame : RamWriteFrame fr.original first.store full := by
    apply (RamWriteFrame.refl fr.original full).trans hprefixFrame
    intro r hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    subst r
    exact ⟨fr.region, by simp [full], Nat.le_refl _, Nat.le_refl _⟩
  have firstWritable : Writable code first.store fr.rdi 32 := by
    apply (hw.of_frame firstFrame).of_offsets (addr_self _) (addr_self _)
    simpa only [BitVec.sub_self, BitVec.toNat_zero, Nat.zero_add] using size32
  obtain ⟨second, hhash, hsecondLabel, hsecondWorking, hsecondTypes, hhashFrame, hhashPost⟩ :=
    initializeHash use256 code hcode (Standards.NIST.AES.cipher v key (Vector.replicate 16 0))
      fr first hfirstLabel hfirstWorking hfirstTypes firstWritable dest32sep slotBounds hblock
  have secondFrame : RamWriteFrame fr.original second.store full := by
    apply firstFrame.trans hhashFrame
    intro r hr'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr'
    rcases hr' with rfl | rfl
    · exact ⟨fr.region, by simp [full], Nat.le_refl _, Nat.le_refl _⟩
    · exact ⟨span fr.rdi (GcmContext.size v), by simp [full], Nat.le_refl _, by simp only [span]; omega⟩
  have secondSchedule : AES16.ScheduleIn v key fr.rsi second.store :=
    AES16.scheduleIn_of_frame hschedule secondFrame sourceOutside
  obtain ⟨output, hfinish, htag, hdone, houtTypes, houtFrame, houtPost⟩ :=
    finish use256 code hcode key fr second hsecondLabel hsecondWorking hsecondTypes secondFrame
      secondSchedule (hr.of_frame secondFrame) (hw.of_frame secondFrame)
      hsrcsep hdstsep hdatasep hhashPost
  exact ⟨output, Program.Exec.of_sem ((hprefix.trans hhash).exec hfinish.sem),
    htag, hdone, houtTypes, houtFrame, houtPost⟩

end AesGcm.Proofs.Machine.GCM
