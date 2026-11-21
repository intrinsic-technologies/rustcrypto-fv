import AesGcm.Proofs.Machine.Runtime.Atoms
import AesGcm.Proofs.Machine.Runtime.Frame
import AesGcm.Proofs.Machine.LIR.Fn102520.Frame
import AesGcm.Proofs.Machine.LIR.Fn102980.Frame

namespace AesGcm.Proofs.Machine.Core.Encrypt

open Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

def ciphertextRegions (use256 : Bool) (fr : Activation) (destination : BitVec 64) (count : Nat) : List MemoryRegion :=
  [span (fr.rsp - BitVec.ofNat 64 (if use256 then 0xb50 else 0x940))
    ((if use256 then 0xb50 else 0x940) - 112), span (fr.rsp - 64) 16, span destination count]

set_option maxRecDepth 2048 in
set_option maxHeartbeats 800000 in
theorem authenticateFrame (use256 : Bool) (code : CodeMap) (fr : Activation)
    (args next : Values Value Reg.count) (mem output : Ram) (destination : BitVec 64) (count : Nat)
    (hworking : Atom.All code args mem
      (if use256 then LIR.Fn102980.frameAt .l102aa2 fr else LIR.Fn102520.frameAt .l102642 fr))
    (hframe : RamWriteFrame mem output (ciphertextRegions use256 fr destination count))
    (hkeep : ∀ r : Fin 53, r.val ∈ [4,22,39,50,51] → next[r] = args[r])
    (hpositive : 0 < count) (hread : Readable mem destination count)
    (hsep : (callStack fr).Disjoint (span destination count))
    (hslots : ∀ slot ∈ ([0x201208, 0x201228] : List (BitVec 64)),
      (span destination count).Disjoint (span slot 8)) :
    Atom.All code next output
      (if use256 then LIR.Fn102980.frameAt .l102b3e fr else LIR.Fn102520.frameAt .l1026de fr) := by
  let window : Nat := if use256 then 0xb50 else 0x940
  let slotHigh : Nat := if use256 then 0x201d88 else 0x201b78
  have facts : args[4] = ⟨64, fr.rsp - 200⟩ ∧ args[22] = ⟨1, 0⟩ ∧
      args[39] = ⟨32, fr.mxcsr⟩ ∧ args[50] = ⟨16, fr.ftw⟩ ∧ args[51] = ⟨16, fr.fcw⟩ ∧
      memLoad mem (fr.rsp - 112) 64 = fr.rdi ∧ memLoad mem (fr.rsp - 104) 64 = fr.rsi ∧
      memLoad mem (fr.rsp - 96) 64 = fr.rcx ∧ memLoad mem (fr.rsp - 88) 64 = fr.r8 ∧
      memLoad mem (fr.rsp - 48) 64 = fr.rbx ∧ memLoad mem (fr.rsp - 40) 64 = fr.r12 ∧
      memLoad mem (fr.rsp - 32) 64 = fr.r13 ∧ memLoad mem (fr.rsp - 24) 64 = fr.r14 ∧
      memLoad mem (fr.rsp - 16) 64 = fr.r15 ∧ memLoad mem (fr.rsp - 8) 64 = fr.rbp ∧
      Readable mem fr.rsp 8 ∧ memLoad mem fr.rsp 64 = fr.ret ∧ fr.ret.toNat < 2^32 ∧
      Writable code mem (fr.rsp - BitVec.ofNat 64 window) window ∧
      fr.low.toNat + window ≤ fr.rsp.toNat ∧ fr.rsp.toNat % 16 = 8 ∧
      Readable mem 0x201208 8 ∧ memLoad mem 0x201208 64 = 0x103f00 ∧
      Readable mem 0x201210 8 ∧ memLoad mem 0x201210 64 = 0x103880 ∧
      Readable mem 0x201228 8 ∧ memLoad mem 0x201228 64 = 0x103eb0 ∧
      Readable mem 0x201230 8 ∧ memLoad mem 0x201230 64 = 0x101230 ∧
      (slotHigh ≤ fr.rsp.toNat ∨ fr.rsp.toNat ≤ 0x201208) ∧ True := by
    cases use256 <;> exact hworking
  obtain ⟨h4,h22,h39,h50,h51,h112,h104,h96,h88,h48,h40,h32,h24,h16,h8,
    hr,hret,hretlow,hw,hroom,halign,s0r,s0v,s1r,s1v,s2r,s2v,s3r,s3v,hsa,_⟩ := facts
  have wmin : 200 ≤ window := by cases use256 <;> decide
  have hrbound := hr.low
  have hdestbound := hread.low
  have hsub (n : Nat) (hn : n ≤ window) : (fr.rsp - BitVec.ofNat 64 n).toNat = fr.rsp.toNat - n := by
    rw [BitVec.toNat_sub_of_le (by change n % 2^64 ≤ fr.rsp.toNat; omega),
      BitVec.toNat_ofNat, Nat.mod_eq_of_lt (by have := fr.rsp.isLt; omega)]
  have hlower : (fr.rsp - BitVec.ofNat 64 (if use256 then 0xb50 else 0x940)).toNat = fr.rsp.toNat - window := hsub window (Nat.le_refl _)
  have h64 : (fr.rsp - 64).toNat = fr.rsp.toNat - 64 := hsub 64 (by omega)
  have hsepNat := disjoint_bounds fr.low.toNat (fr.rsp.toNat + 8 - fr.low.toNat)
    destination.toNat count (by omega) hpositive hsep
  have localOutside (n : Nat) (hn : n ≤ 112) (hnpos : n = 0 ∨ 8 ≤ n)
      (hs : n ≤ 48 ∨ 88 ≤ n) : Outside (ciphertextRegions use256 fr destination count)
        (fr.rsp - BitVec.ofNat 64 n) 8 := by
    have ha := hsub n (by omega)
    refine ⟨by rw [ha]; omega, ?_⟩
    intro r hin
    simp only [ciphertextRegions, List.mem_cons, List.not_mem_nil, or_false] at hin
    rcases hin with rfl | rfl | rfl
    · simp only [span, hlower, ha]
      omega
    · simp only [span, h64, ha]
      omega
    · simp only [span, ha]
      omega
  have slotOutside (a : BitVec 64) (ha : a ∈ ([0x201208, 0x201228] : List (BitVec 64))) :
      Outside (ciphertextRegions use256 fr destination count) a 8 := by
    have hslot := disjoint_bounds destination.toNat count a.toNat 8 hpositive (by decide) (hslots a ha)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl
    all_goals simp only [BitVec.reduceToNat] at hslot
    all_goals refine ⟨by decide, ?_⟩
    all_goals intro r hin
    all_goals simp only [ciphertextRegions, List.mem_cons, List.not_mem_nil, or_false] at hin
    all_goals rcases hin with rfl | rfl | rfl
    all_goals simp only [span, hlower, h64, BitVec.reduceToNat]
    all_goals cases use256 <;> simp only [window, slotHigh, Bool.false_eq_true, ↓reduceIte] at * <;> omega
  have retOutside : Outside (ciphertextRegions use256 fr destination count) fr.rsp 8 := by
    have hh := localOutside 0 (by decide) (by decide) (by decide)
    change Outside _ (fr.rsp - 0) 8 at hh
    have he : fr.rsp - (0#64) = fr.rsp := by bv_omega
    exact he ▸ hh
  have initial : Atom.All code args mem
      (if use256 then LIR.Fn102980.frameAt .l102b3e fr else LIR.Fn102520.frameAt .l1026de fr) := by
    cases use256
    all_goals refine ⟨h4,h22,h39,h50,h51,h112,h104,h96,h88,h48,h40,h32,h24,h16,h8,
      hr,hret,hretlow,hw,hroom,halign,s0r,s0v,s2r,s2v,?_,trivial⟩
    all_goals simp only [slotHigh, Bool.false_eq_true, ↓reduceIte] at hsa
    all_goals change _ ∨ _
    all_goals omega
  apply atomsAll_of_frame hframe ?_ initial
  intro a ha
  cases use256
  all_goals simp only [Bool.false_eq_true, ↓reduceIte, LIR.Fn102980.frameAt, LIR.Fn102520.frameAt,
    LIR.Fn102980.frameAtG2, LIR.Fn102520.frameAtG2, List.mem_cons, List.not_mem_nil, or_false] at ha
  all_goals rcases ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | exact True.intro
    | exact hkeep _ (by decide)
    | exact localOutside 112 (by decide) (by decide) (by decide)
    | exact localOutside 104 (by decide) (by decide) (by decide)
    | exact localOutside 96 (by decide) (by decide) (by decide)
    | exact localOutside 88 (by decide) (by decide) (by decide)
    | exact localOutside 48 (by decide) (by decide) (by decide)
    | exact localOutside 40 (by decide) (by decide) (by decide)
    | exact localOutside 32 (by decide) (by decide) (by decide)
    | exact localOutside 24 (by decide) (by decide) (by decide)
    | exact localOutside 16 (by decide) (by decide) (by decide)
    | exact localOutside 8 (by decide) (by decide) (by decide)
    | exact retOutside
    | exact slotOutside _ (by decide)

end AesGcm.Proofs.Machine.Core.Encrypt
