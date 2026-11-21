import P256.Proofs.Verifying.Combination.PointCall
import P256.Proofs.Projective.Multiply.Machine.Basepoint.TableSteps.Copy

set_option autoImplicit false

namespace P256.Proofs.Verifying.Combination.Loop.Multi

open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude
open X86 X86.Machine X86.UserProcess X86Proofs Program Program.ScalarFrame
open P256.Proofs.Projective.Multiply.Machine.Basepoint.TableSteps

theorem point_copy [Bindings] {s t : RamState} {boundary : ReturnBoundary} {point : Projective}
    (pre : Return.Pre s boundary) (state : State s t) (offset source destination : Nat)
    (codeBound : offset + 3 < 118431)
    (code : Extracted.textBytes.toListFrom offset 3 = [0xf3,0x48,0xa5])
    (rip : t.RIP = Extracted.textAddress + BitVec.ofNat 64 offset)
    (hd : destination ≤ 408) (hsaved : 144 ≤ destination)
    (dst : t.regValue .rdi = stackPtr s - BitVec.ofNat 64 destination)
    (count : t.regValue .rcx = 12) (hs : source ≤ 408) (hlen : 96 ≤ source + 8)
    (apart : destination + 96 ≤ source ∨ source + 96 ≤ destination)
    (src : t.regValue .rsi = stackPtr s - BitVec.ofNat 64 source)
    (value : ProjectiveAt t (stackPtr s - BitVec.ofNat 64 source) point) :
    ∃ u, PointCallResult s t u boundary
      (Extracted.textAddress + BitVec.ofNat 64 offset + 3) destination point := by
  obtain ⟨u, run, frame, next, valueU, agrees, _⟩ := copy_stack (frameOffset := 408)
    pre state offset codeBound code rip destination hd hsaved dst count (by omega) hlen apart src value
  refine ⟨u, frame, ⟨12,run⟩, next, valueU, ?_, ?_⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl | rfl
    · exact agrees.read (n := 64) (r := 3) (by simp [copyComponents])
    · exact agrees.read (n := 64) (r := 5) (by simp [copyComponents])
    · exact agrees.read (n := 64) (r := 12) (by simp [copyComponents])
    · exact agrees.read (n := 64) (r := 13) (by simp [copyComponents])
    · exact agrees.read (n := 64) (r := 14) (by simp [copyComponents])
    · exact agrees.read (n := 64) (r := 15) (by simp [copyComponents])
  · intro off len ho hl disjoint i hi
    exact copy_byte pre agrees (by omega) hsaved (by omega) hl disjoint hi

end P256.Proofs.Verifying.Combination.Loop.Multi
