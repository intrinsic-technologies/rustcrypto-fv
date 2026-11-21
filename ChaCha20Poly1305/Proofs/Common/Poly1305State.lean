import Standards.RFC.ChaCha20Poly1305
import X86Proofs.Program.Execution

   
                                             

                                                                                               
                 

                                                        
                                                              
                                                                  

                                                                     
  

namespace ChaCha20Poly1305.Proofs.Poly1305State

open X86 X86.Machine X86.UserProcess X86Proofs Standards.RFC.ChaCha20Poly1305

def stateBytes : Nat := 0x38

def rOffset : BitVec 64 := 0x10

def hOffset : BitVec 64 := 0x24

def word32 (s : RamState) (address : BitVec 64) : BitVec 32 :=
  (Operand.mem address : Operand 32).read s

def limbsAt (s : RamState) (base : BitVec 64) : Fin 5 → BitVec 32 :=
  fun i => word32 s (base + BitVec.ofNat 64 (4 * i.val))

def padWords (s : RamState) (state : BitVec 64) : Fin 4 → BitVec 32 :=
  fun i => word32 s (state + BitVec.ofNat 64 (4 * i.val))

def rLimbs (s : RamState) (state : BitVec 64) : Fin 5 → BitVec 32 :=
  limbsAt s (state + rOffset)

def hLimbs (s : RamState) (state : BitVec 64) : Fin 5 → BitVec 32 :=
  limbsAt s (state + hOffset)

def prime : Nat := 2 ^ 130 - 5

def limbValue (l : Fin 5 → BitVec 32) : Nat :=
  (l 0).toNat + 2 ^ 26 * (l 1).toNat + 2 ^ 52 * (l 2).toNat + 2 ^ 78 * (l 3).toNat +
    2 ^ 104 * (l 4).toNat

def wordValue (w : Fin 4 → BitVec 32) : Nat :=
  (w 0).toNat + 2 ^ 32 * (w 1).toNat + 2 ^ 64 * (w 2).toNat + 2 ^ 96 * (w 3).toNat

                                                                                         
def ClampedLimbs (l : Fin 5 → BitVec 32) : Prop :=
  ∃ key : Nat, ∀ i : Fin 5, (l i).toNat = clamp key / 2 ^ (26 * i.val) % 2 ^ 26

                                                                                            
def BoundedLimbs (l : Fin 5 → BitVec 32) : Prop :=
  (l 0).toNat < 2 ^ 26 ∧ (l 1).toNat < 2 ^ 26 + 2 ^ 6 ∧ (l 2).toNat < 2 ^ 26 ∧
    (l 3).toNat < 2 ^ 26 ∧ (l 4).toNat < 2 ^ 26

def clampedR (key : Vector UInt8 32) : Nat :=
  clamp (leBytesToNum ⟨key.toArray.extract 0 16⟩)

def padOf (key : Vector UInt8 32) : Nat :=
  leBytesToNum ⟨key.toArray.extract 16 32⟩

theorem limbValue_ext {l l' : Fin 5 → BitVec 32} (h : ∀ i, l i = l' i) :
    limbValue l = limbValue l' := by
  simp [limbValue, h]

theorem limbValue_zero : limbValue (fun _ => 0) = 0 := by
  simp [limbValue]

theorem boundedLimbs_zero : BoundedLimbs (fun _ => 0) := by
  simp [BoundedLimbs]

theorem limbValue_clamped {l : Fin 5 → BitVec 32} (key : Nat)
    (hl : ∀ i : Fin 5, (l i).toNat = clamp key / 2 ^ (26 * i.val) % 2 ^ 26) :
    limbValue l = clamp key := by
  have hc : clamp key < 2 ^ 130 := by
    unfold clamp
    exact Nat.lt_of_le_of_lt Nat.and_le_right (by decide)
  have h0 := hl 0
  have h1 := hl 1
  have h2 := hl 2
  have h3 := hl 3
  have h4 := hl 4
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two] at h0 h1 h2
  change _ = clamp key / 2 ^ 78 % 2 ^ 26 at h3
  change _ = clamp key / 2 ^ 104 % 2 ^ 26 at h4
  unfold limbValue
  omega

theorem ClampedLimbs.value {l : Fin 5 → BitVec 32} (h : ClampedLimbs l) :
    ∃ key, limbValue l = clamp key :=
  let ⟨key, hk⟩ := h
  ⟨key, limbValue_clamped key hk⟩

end ChaCha20Poly1305.Proofs.Poly1305State
