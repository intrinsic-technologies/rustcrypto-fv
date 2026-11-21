import Base16ct.Proofs.Base16ctUpperDecodeCorrect.Control.Checks
import Base16ct.Proofs.Base16ctUpperDecodeCorrect.Control.Entry.Initialize

namespace Base16ct.Proofs.Base16ctUpperDecodeCorrect
variable {alphabet : RFC4648.Alphabet} {lengthWritten : Prop}
open Base16ct.Spec Base16ct.Spec.Program Base16ct.Spec.Program.Extracted
open Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem decode_entry_nonempty [Bindings]
    {initial : RamState} {input : List UInt8} {capacity : Nat} {boundary : ReturnBoundary}
    (hv : ValidCall (decodeRoutine alphabet) initial input capacity lengthWritten)
    (he : EntryReady programImage initial)
    (heven : input.length % 2 = 0) (hcapacity : input.length / 2 ≤ capacity)
    (hne : input ≠ []) (hret : ¬ InProgram boundary.rip) :
    ∃ s, Advances boundary 14 initial s ∧ EntryReady programImage s ∧
      DecodeMachineLoopInvariant [alphabet] (decodeAddress alphabet) 228 initial input [] input
        #v[outputRegion initial (input.length / 2), Stack.region initial (decodeRoutine alphabet).minStackBytes]
        (decodeCallEffects initial (input.length / 2)) s := by
  obtain ⟨u, hau, heu, hpu, hfu, _⟩ := decode_check_parity he hv.entry hret
  have hlen0 : (AddrMode.reg64 6 initial).toNat = input.length := inputLength hv
  have hpu' : u.RIP = (decodeAddress alphabet) + 15#64 := by simpa only [hlen0, heven, ite_true] using hpu
  have hlen1 : (AddrMode.reg64 6 u).toNat = input.length := by
    exact (congrArg BitVec.toNat (hfu.read (r := 6) (n := 64) (by simp))).trans hlen0
  have hcap1 : (AddrMode.reg64 8 u).toNat = capacity := by
    exact (congrArg BitVec.toNat (hfu.read (r := 8) (n := 64) (by simp))).trans (outputCapacity hv)
  obtain ⟨v, hav, hev, hpv, hfv, haxv⟩ := decode_check_capacity heu hpu' hlen1 hcap1 hret
  have hpv' : v.RIP = (decodeAddress alphabet) + 30#64 := by simpa only [ite_eq_left hcapacity] using hpv
  have hlen2 : (AddrMode.reg64 6 v).toNat = input.length := by
    exact (congrArg BitVec.toNat (hfv.read (r := 6) (n := 64) (by simp))).trans hlen1
  obtain ⟨w, haw, hew, hpw, hfw⟩ := decode_check_empty hev hpv' hlen2 hret
  have hlength : input.length ≠ 0 := by cases input <;> simp_all
  have hpw' : w.RIP = (decodeAddress alphabet) + 39#64 := by simpa only [ite_eq_right hlength] using hpw
  have haxw : AddrMode.reg64 9 w = BitVec.ofNat 64 (input.length / 2) :=
    (hfw.read (by simp)).trans haxv
  have hframe : AgreesExcept [.reg 0, .reg 9, .flags, .rip] initial w :=
    (hfu.trans (hfv.trans hfw)).mono (by simp_all)
  obtain ⟨s, has, hes, hs⟩ := decode_initialize_loop hv hew hpw' hframe haxw hne hret
  exact ⟨s, hau.trans (hav.trans (haw.trans has)), hes, hs⟩

theorem decode_entry_invalid [Bindings]
    {initial : RamState} {input : List UInt8} {capacity : Nat} {boundary : ReturnBoundary}
    (hv : ValidCall (decodeRoutine alphabet) initial input capacity lengthWritten)
    (he : EntryReady programImage initial)
    (hinvalid : input.length % 2 ≠ 0 ∨ capacity < input.length / 2)
    (hret : ¬ InProgram boundary.rip) :
    ∃ fuel s, Advances boundary fuel initial s ∧ EntryReady programImage s ∧
      s.RIP = (decodeAddress alphabet) + 240#64 ∧
      AgreesExcept [.reg 0, .reg 9, .flags, .rip] initial s ∧
      AddrMode.reg64 0 s = 1#64 := by
  obtain ⟨u, hau, heu, hpu, hfu, hx⟩ := decode_check_parity he hv.entry hret
  have hlen0 : (AddrMode.reg64 6 initial).toNat = input.length := inputLength hv
  by_cases heven : input.length % 2 = 0
  · have hpu' : u.RIP = (decodeAddress alphabet) + 15#64 := by simpa only [hlen0, heven, ite_true] using hpu
    have hlen1 : (AddrMode.reg64 6 u).toNat = input.length := by
      exact (congrArg BitVec.toNat (hfu.read (r := 6) (n := 64) (by simp))).trans hlen0
    have hcap1 : (AddrMode.reg64 8 u).toNat = capacity := by
      exact (congrArg BitVec.toNat (hfu.read (r := 8) (n := 64) (by simp))).trans (outputCapacity hv)
    obtain ⟨v, hav, hev, hpv, hfv, _⟩ := decode_check_capacity heu hpu' hlen1 hcap1 hret
    have hsmall : ¬ input.length / 2 ≤ capacity := by omega
    have hpv' : v.RIP = (decodeAddress alphabet) + 240#64 := by simpa only [ite_eq_right hsmall] using hpv
    refine ⟨7, v, hau.trans hav, hev, hpv', ?_, ?_⟩
    · exact (hfu.trans hfv).mono (by simp_all)
    · exact (hfv.read (by simp)).trans hx
  · have hpu' : u.RIP = (decodeAddress alphabet) + 240#64 := by simpa only [hlen0, ite_eq_right heven] using hpu
    exact ⟨3, u, hau, heu, hpu', hfu.mono (by simp), hx⟩

theorem decode_entry_empty [Bindings]
    {initial : RamState} {capacity : Nat} {boundary : ReturnBoundary}
    (hv : ValidCall (decodeRoutine alphabet) initial [] capacity lengthWritten)
    (he : EntryReady programImage initial) (hret : ¬ InProgram boundary.rip) :
    ∃ s, Advances boundary 9 initial s ∧ EntryReady programImage s ∧
      s.RIP = (decodeAddress alphabet) + 241#64 ∧
      AgreesExcept [.reg 0, .reg 9, .flags, .rip] initial s ∧ AddrMode.reg64 9 s = 0#64 := by
  obtain ⟨u, hau, heu, hpu, hfu, _⟩ := decode_check_parity he hv.entry hret
  have hlen0 : (AddrMode.reg64 6 initial).toNat = 0 := inputLength hv
  have hpu' : u.RIP = (decodeAddress alphabet) + 15#64 := by simpa only [hlen0, Nat.zero_mod, ite_true] using hpu
  have hlen1 : (AddrMode.reg64 6 u).toNat = 0 := by
    exact (congrArg BitVec.toNat (hfu.read (r := 6) (n := 64) (by simp))).trans hlen0
  have hcap1 : (AddrMode.reg64 8 u).toNat = capacity := by
    exact (congrArg BitVec.toNat (hfu.read (r := 8) (n := 64) (by simp))).trans (outputCapacity hv)
  obtain ⟨v, hav, hev, hpv, hfv, h9⟩ := decode_check_capacity heu hpu' hlen1 hcap1 hret
  have hpv' : v.RIP = (decodeAddress alphabet) + 30#64 := by simpa using hpv
  have hlen2 : (AddrMode.reg64 6 v).toNat = 0 := by
    exact (congrArg BitVec.toNat (hfv.read (r := 6) (n := 64) (by simp))).trans hlen1
  obtain ⟨w, haw, hew, hpw, hfw⟩ := decode_check_empty hev hpv' hlen2 hret
  have hpw' : w.RIP = (decodeAddress alphabet) + 241#64 := by simpa using hpw
  refine ⟨w, hau.trans (hav.trans haw), hew, hpw',
    (hfu.trans (hfv.trans hfw)).mono (by simp_all), ?_⟩
  exact (hfw.read (by simp)).trans h9

end Base16ct.Proofs.Base16ctUpperDecodeCorrect
