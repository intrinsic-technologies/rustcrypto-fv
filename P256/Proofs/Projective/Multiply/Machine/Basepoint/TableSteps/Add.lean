import P256.Proofs.Projective.Multiply.Machine.Basepoint.TableSteps.Result
import P256.Proofs.Projective.Multiply.Machine.Loop.Call.Site
import P256.Proofs.Projective.Add
import P256.Proofs.Program.CalleeStack
import P256.Proofs.Program.CalleeStackInput
import P256.Proofs.Projective.Multiply.Machine.Basepoint.Constants

set_option autoImplicit false

namespace P256.Proofs.Projective.Multiply.Machine.Basepoint.TableSteps

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame
open P256.Proofs.Projective.Multiply.Machine.Loop

def addLayout : StackCallLayout 3352 96 96 920 :=
  ⟨1952, 144, 912, by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

theorem add_call_site [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    (pre : CalleePre s boundary 0x10e6f0 32 65 3352) (state : FrameState s t 65 3352 1944)
    (site : CallSite 0x1051f0)
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 site.offset) :
    ∃ v, Advances boundary 1 t v ∧ ReadyToStep v ∧
      (callEffect (fun _ => 0x1051f0) site.returnRip t).Holds t v := by
  have targetProg := inProgram_of_textOffset 0x51f0 (by decide)
  have step := scalar_call pre (by decide) (by decide) state site.offset site.disp
    (Nat.le_of_lt site.bounded) site.bytes
    (by rw [site.target_eq]; exact Program.inProgram_low targetProg)
    (by rw [site.target_eq]; exact targetProg) rip
  rw [site.target_eq] at step
  exact step

theorem add_call [Bindings] {s t : RamState} {boundary : ReturnBoundary} {left right : Projective}
    (pre : CalleePre s boundary 0x10e6f0 32 65 3352) (state : FrameState s t 65 3352 1944)
    (site : CallSite 0x1051f0)
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 site.offset)
    (dst : t.regValue .rdi = stackPtr s - 912)
    (src : t.regValue .rsi = stackPtr s - 144)
    (leftAt : ProjectiveAt t (stackPtr s - 912) left)
    (rightAt : ProjectiveAt t (stackPtr s - 144) right) :
    ∃ u, PointCallResult s t u boundary site.returnRip 912 (left.add right) := by
  obtain ⟨v, run, ready, effect⟩ := add_call_site pre state site rip
  have stateV := state.after_call pre (by decide) (by decide) ready effect
  have dstV : v.regValue .rdi = stackPtr s - 912 :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans dst
  have srcV : v.regValue .rsi = stackPtr s - 144 :=
    (effect.agrees.read (n := 64) (r := 6) (by simp)).trans src
  have cp := CalleePre.of_stack pre addLayout stateV.bindingsSupported stateV.machine stateV.directionFlag
    stateV.loaded stateV.allocated effect.rip stateV.rsp srcV dstV (call_return_program site effect)
  have leftV : ProjectiveAt v (v.regValue .rdi) left := by
    rw [dstV]
    exact leftAt.of_bytes_eq (fun i hi => scalar_call_byte (by decide) state effect (by decide) (by decide) hi)
  have rightV : ProjectiveAt v (v.regValue .rsi) right := by
    rw [srcV]
    exact rightAt.of_bytes_eq (fun i hi => scalar_call_byte (by decide) state effect (by decide) (by decide) hi)
  obtain ⟨u, result, value⟩ := projective_add_correct cp leftV rightV
  exact ⟨u, finish_call pre state run ready effect dstV (by decide) (by decide) (by decide) result value⟩

def generatorAddLayout : StackBufferLayout 3352 96 920 :=
  ⟨1952, 144, by decide, by decide, by decide, by decide⟩

theorem generator_region_inProgram {a : BitVec 64}
    (ha : (MemoryRegion.mk (0x202ac8 : Nat) 96).Contains a.toNat) : InProgram a := by
  change 0x202ac8 ≤ a.toNat ∧ a.toNat < 0x202ac8 + 96 at ha
  have h := generator_byte_inProgram (i := a.toNat - 0x202ac8) (by omega)
  have he : 0x202ac8 + BitVec.ofNat 64 (a.toNat - 0x202ac8) = a := by
    rw [show (0x202ac8 : BitVec 64) = BitVec.ofNat 64 0x202ac8 from rfl,
      ← BitVec.ofNat_add, Nat.add_sub_of_le ha.1, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  rwa [he] at h

theorem add_generator_call [Bindings] {s t : RamState} {boundary : ReturnBoundary}
    {left : Projective}
    (pre : CalleePre s boundary 0x10e6f0 32 65 3352) (state : FrameState s t 65 3352 1944)
    (site : CallSite 0x1051f0)
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 site.offset)
    (dst : t.regValue .rdi = stackPtr s - 144)
    (src : t.regValue .rsi = 0x202ac8)
    (leftAt : ProjectiveAt t (stackPtr s - 144) left) :
    ∃ u, PointCallResult s t u boundary site.returnRip 144 (left.add basePoint) := by
  obtain ⟨v, run, ready, effect⟩ := add_call_site pre state site rip
  have stateV := state.after_call pre (by decide) (by decide) ready effect
  have dstV : v.regValue .rdi = stackPtr s - 144 :=
    (effect.agrees.read (n := 64) (r := 7) (by simp)).trans dst
  have srcV : v.regValue .rsi = 0x202ac8 :=
    (effect.agrees.read (n := 64) (r := 6) (by simp)).trans src
  have region : registerRegion v .rsi 96 = MemoryRegion.mk 0x202ac8 96 := by
    simp only [registerRegion, srcV]; rfl
  have bounded : (registerRegion v .rsi 96).Bounded := by rw [region]; change 0x202ac8 + 96 < 2^32; decide
  have allocated : (registerRegion v .rsi 96).Allocated v.external := by
    rw [region]
    intro a ha
    obtain ⟨b, hb⟩ := generator_region_inProgram ha
    exact ⟨b, stateV.loaded a b hb⟩
  have disjoint : (registerRegion v .rsi 96).Disjoint (Stack.region s 3352) := by
    rw [region]
    intro a ha hs
    have bounds := stack_bounds pre.stack
    have low : a < 2^64 := by
      change 0x202ac8 ≤ a ∧ a < 0x202ac8 + 96 at ha
      omega
    have eq : (BitVec.ofNat 64 a).toNat = a := Nat.mod_eq_of_lt low
    exact pre.avoids (Stack.region s 3352) (by simp) (BitVec.ofNat 64 a)
      (eq.symm ▸ hs) (.inl (generator_region_inProgram (eq.symm ▸ ha)))
  have cp := CalleePre.of_disjoint_input_and_stack generatorAddLayout pre.stack
    (pre.avoids _ (by simp)) stateV.bindingsSupported stateV.machine stateV.directionFlag
    stateV.loaded effect.rip stateV.rsp bounded allocated disjoint dstV stateV.allocated
    pre.outerBoundary (call_return_program site effect)
  have leftV : ProjectiveAt v (v.regValue .rdi) left := by
    rw [dstV]
    exact leftAt.of_bytes_eq (fun i hi =>
      scalar_call_byte (by decide) state effect (by decide) (by decide) hi)
  have rightV : ProjectiveAt v (v.regValue .rsi) basePoint := srcV ▸ generator_at stateV.loaded
  obtain ⟨u, result, value⟩ := projective_add_correct cp leftV rightV
  exact ⟨u, finish_call pre state run ready effect dstV (by decide) (by decide) (by decide)
    result value⟩

def add1164ca : CallSite 0x1051f0 :=
  ⟨0xe75a, 0xffff6a91, by decide, by decide +kernel, by decide +kernel⟩

def add1164fd : CallSite 0x1051f0 :=
  ⟨0xe78d, 0xffff6a5e, by decide, by decide +kernel, by decide +kernel⟩

def add11653e : CallSite 0x1051f0 :=
  ⟨0xe7ce, 0xffff6a1d, by decide, by decide +kernel, by decide +kernel⟩

def add11657f : CallSite 0x1051f0 :=
  ⟨0xe80f, 0xffff69dc, by decide, by decide +kernel, by decide +kernel⟩

def add1165c5 : CallSite 0x1051f0 :=
  ⟨0xe855, 0xffff6996, by decide, by decide +kernel, by decide +kernel⟩

def add11660b : CallSite 0x1051f0 :=
  ⟨0xe89b, 0xffff6950, by decide, by decide +kernel, by decide +kernel⟩

def add116651 : CallSite 0x1051f0 :=
  ⟨0xe8e1, 0xffff690a, by decide, by decide +kernel, by decide +kernel⟩

end P256.Proofs.Projective.Multiply.Machine.Basepoint.TableSteps
