import AesGcm.Proofs.AES16.Encrypt.Loop.HeaderStep
import AesGcm.Proofs.AES16.Encrypt.Loop.MixStep
import AesGcm.Proofs.AES16.Encrypt.Loop.Key1Step
import AesGcm.Proofs.AES16.Encrypt.Loop.SboxStep
import AesGcm.Proofs.AES16.Encrypt.Loop.Inline2Step
import AesGcm.Proofs.AES16.Encrypt.Loop.Key3Step
import AesGcm.Proofs.AES16.Encrypt.Loop.Inline0Step

namespace AesGcm.Proofs.Machine.AES16.Encrypt

open Standards.NIST.AES Prelude X86 X86.Machine X86.UserProcess X86Proofs X86Proofs.CFG X86Proofs.Lift X86Proofs.Refine
open AesGcm.Proofs.Machine.Runtime

def lastIteration (use256 : Bool) : Nat := if use256 then 3 else 2

theorem loop_step (use256 : Bool) (code : CodeMap)
    (hcode : ∀ x ∈ LIR.fnCode, x ∈ code)
    (key : Vector UInt8 (variant use256).keyBytes) (input : Standards.NIST.AES.Block)
    (fr : Activation) (j : Nat) (hj : 4 * j < (variant use256).Nr + 1)
    (hbound : j ≤ lastIteration use256) (loc : LIR.lifted.Location)
    (hsep : (callStack fr).Disjoint (span fr.rsi (16 * ((variant use256).Nr + 1))))
    (hwork : WorkingState code use256 key fr loc)
    (hloop : LoopState use256 key input fr j hj loc) :
    ∃ next : LIR.lifted.Location,
      (LIR.program.sem (dialect code)).Reaches ⟨loc, []⟩ ⟨next, []⟩ ∧
      WorkingState code use256 key fr next ∧
      ((j = lastIteration use256 ∧ FinalState use256 key input fr next) ∨
        (j < lastIteration use256 ∧
          ∃ hnext : 4 * (j + 1) < (variant use256).Nr + 1,
            LoopState use256 key input fr (j + 1) hnext next)) := by
  have hNr1 : 4*j+1 < (variant use256).Nr := by
    cases use256 <;> simp only [lastIteration,variant,Bool.false_eq_true,↓reduceIte,Variant.Nr] at hbound ⊢ <;> omega
  obtain ⟨s1,hr1,hw1,hl1,hp1,hi1,hb1⟩ :=
    Loop.header_step use256 code hcode key input fr j hj loc hsep hwork hloop
  obtain ⟨s2,hr2,hw2,hl2,hp2,hi2,hb2⟩ :=
    Loop.mix_step use256 false code hcode key fr s1
      (Fixslice16.subBytes (roundState (variant use256) key input (4*j)))
      hsep hw1 hl1 hb1 hp1
  obtain ⟨s3,hr3,hw3,hl3,hp3,hg3,hi3,hb3⟩ :=
    Loop.key1_step use256 code hcode key input fr j hNr1 hbound s2 hsep hw2 hl2
      (hi2.trans (hi1.trans hloop.index)) hp2
  have hr123 := hr1.trans (hr2.trans hr3)
  by_cases hlast : j = lastIteration use256
  · have hround : 4*j+1 = (variant use256).Nr-1 := by
      cases use256 <;> simp only [lastIteration,variant,Bool.false_eq_true,↓reduceIte,Variant.Nr] at hlast ⊢ <;> omega
    refine ⟨s3,hr123,hw3,Or.inl ⟨hlast,?_,?_,?_⟩⟩
    · simpa only [show j = (if use256 then 3 else 2) from hlast,ite_true] using hl3
    · simpa only [hround] using hp3
    · simpa only [hround] using hg3
  · have hlt : j < lastIteration use256 := by omega
    have hNr2 : 4*j+2 < (variant use256).Nr := by
      cases use256 <;> simp only [lastIteration,variant,Bool.false_eq_true,↓reduceIte,Variant.Nr] at hlt ⊢ <;> omega
    have hNr3 : 4*j+3 < (variant use256).Nr := by
      cases use256 <;> simp only [lastIteration,variant,Bool.false_eq_true,↓reduceIte,Variant.Nr] at hlt ⊢ <;> omega
    have hNr4 : 4*j+4 < (variant use256).Nr := by
      cases use256 <;> simp only [lastIteration,variant,Bool.false_eq_true,↓reduceIte,Variant.Nr] at hlt ⊢ <;> omega
    obtain ⟨s4,hr4,hw4,hl4,hp4,hi4,hb4⟩ :=
      Loop.sbox_step use256 code hcode key fr s3
        (roundState (variant use256) key input (4*j+1)) hsep hw3
        (by simpa only [show j ≠ (if use256 then 3 else 2) from hlast,ite_false] using hl3)
        (hb3.trans hb2) hp3
    obtain ⟨s5,hr5,hw5,hl5,hp5,hi5,hb5⟩ :=
      Loop.inline2_step use256 code hcode key input fr j hNr2 s4 hsep hw4 hl4
        (hi4.trans (hi3.trans (hi2.trans (hi1.trans hloop.index)))) hp4
    obtain ⟨s6,hr6,hw6,hl6,hp6,hi6,hb6⟩ :=
      Loop.mix_step use256 true code hcode key fr s5
        (Fixslice16.subBytes (roundState (variant use256) key input (4*j+2)))
        hsep hw5 hl5 hb5 hp5
    obtain ⟨s7,hr7,hw7,hl7,hp7,hi7,hb7⟩ :=
      Loop.key3_step use256 code hcode key input fr j hNr3 s6 hsep hw6 hl6
        (hi6.trans (hi5.trans (hi4.trans (hi3.trans (hi2.trans (hi1.trans hloop.index)))))) hp6 hb6
    obtain ⟨s8,hr8,hw8,hn8,hl8⟩ :=
      Loop.inline0_step use256 code hcode key input fr j hNr4 s7 hsep hw7 hl7
        (hi7.trans (hi6.trans (hi5.trans (hi4.trans (hi3.trans (hi2.trans (hi1.trans hloop.index))))))) hp7
    exact ⟨s8,hr123.trans (hr4.trans (hr5.trans (hr6.trans (hr7.trans hr8)))),hw8,
      Or.inr ⟨hlt,hn8,hl8⟩⟩

end AesGcm.Proofs.Machine.AES16.Encrypt
