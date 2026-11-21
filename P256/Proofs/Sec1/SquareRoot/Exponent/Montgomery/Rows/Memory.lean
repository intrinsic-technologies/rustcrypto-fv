import P256.Proofs.Sec1.SquareRoot.Exponent.Montgomery.Rows.Blocks

set_option autoImplicit false

namespace P256.Proofs.Sec1.SquareRoot.Montgomery.Rows

open P256.Proofs.Common.Field (AdvanceTriple)
open P256.Spec P256.Spec.Program P256.Spec.Program.Routines Prelude X86 X86.Machine X86.UserProcess X86Proofs

theorem stackPtr_read (s : RamState) : stackPtr s = (Operand.reg 4#5 : Operand 64).read s := rfl

theorem secondStart_saved {p : BitVec 64} {s t : RamState} {b : Vector (BitVec 64) 4}
    (h : (secondStartEffect p s).Holds s t) (hs : Saved s b) : Saved t b := by
  have hrsp := Reduction.scratch_rsp (secondStart_frame h)
  constructor
  · rw [hrsp, secondStart_read h]
    x86_norm [secondStartEffect, stackPtr_read]
    exact hs.b0
  · rw [hrsp, secondStart_read h]
    x86_norm [secondStartEffect, stackPtr_read]
    exact hs.b1
  · rw [hrsp, secondStart_read h]
    x86_norm [secondStartEffect, stackPtr_read]
    exact hs.b2
  · rw [hrsp, secondStart_read h]
    x86_norm [secondStartEffect, stackPtr_read]
    exact hs.b3
  · rw [hrsp, secondStart_read h]
    x86_norm [secondStartEffect, stackPtr_read]
    exact hs.p0
  · rw [hrsp, secondStart_read h]
    x86_norm [secondStartEffect, stackPtr_read]
    exact hs.p1
  · rw [hrsp, secondStart_read h]
    x86_norm [secondStartEffect, stackPtr_read]
    exact hs.p2
  · rw [hrsp, secondStart_read h]
    x86_norm [secondStartEffect, stackPtr_read]
    exact hs.p3
  · rw [hrsp, secondStart_read h]
    x86_norm [secondStartEffect, stackPtr_read]
    exact hs.inverse

theorem secondStart_pointer {p : BitVec 64} {s t : RamState}
    (h : (secondStartEffect p s).Holds s t) : savedPtr t = savedPtr s := by
  have hrsp := Reduction.scratch_rsp (secondStart_frame h)
  unfold savedPtr
  rw [hrsp, secondStart_read h]
  x86_norm [secondStartEffect, stackPtr_read]

theorem secondMiddle_saved {p : BitVec 64} {s t : RamState} {b : Vector (BitVec 64) 4}
    (h : (secondMiddleEffect p s).Holds s t) (hs : Saved s b) : Saved t b := by
  have hrsp := Reduction.scratch_rsp (secondMiddle_frame h)
  constructor
  · rw [hrsp, secondMiddle_read h]
    x86_norm [secondMiddleEffect, stackPtr_read]
    exact hs.b0
  · rw [hrsp, secondMiddle_read h]
    x86_norm [secondMiddleEffect, stackPtr_read]
    exact hs.b1
  · rw [hrsp, secondMiddle_read h]
    x86_norm [secondMiddleEffect, stackPtr_read]
    exact hs.b2
  · rw [hrsp, secondMiddle_read h]
    x86_norm [secondMiddleEffect, stackPtr_read]
    exact hs.b3
  · rw [hrsp, secondMiddle_read h]
    x86_norm [secondMiddleEffect, stackPtr_read]
    exact hs.p0
  · rw [hrsp, secondMiddle_read h]
    x86_norm [secondMiddleEffect, stackPtr_read]
    exact hs.p1
  · rw [hrsp, secondMiddle_read h]
    x86_norm [secondMiddleEffect, stackPtr_read]
    exact hs.p2
  · rw [hrsp, secondMiddle_read h]
    x86_norm [secondMiddleEffect, stackPtr_read]
    exact hs.p3
  · rw [hrsp, secondMiddle_read h]
    x86_norm [secondMiddleEffect, stackPtr_read]
    exact hs.inverse

theorem secondMiddle_pointer {p : BitVec 64} {s t : RamState}
    (h : (secondMiddleEffect p s).Holds s t) : savedPtr t = savedPtr s := by
  have hrsp := Reduction.scratch_rsp (secondMiddle_frame h)
  unfold savedPtr
  rw [hrsp, secondMiddle_read h]
  x86_norm [secondMiddleEffect, stackPtr_read]

theorem secondHigh_saved {p : BitVec 64} {s t : RamState} {b : Vector (BitVec 64) 4}
    (h : (secondHighEffect p s).Holds s t) (hs : Saved s b) : Saved t b := by
  have hrsp := Reduction.scratch_rsp (secondHigh_frame h)
  constructor
  · rw [hrsp, secondHigh_read h]
    x86_norm [secondHighEffect, stackPtr_read]
    exact hs.b0
  · rw [hrsp, secondHigh_read h]
    x86_norm [secondHighEffect, stackPtr_read]
    exact hs.b1
  · rw [hrsp, secondHigh_read h]
    x86_norm [secondHighEffect, stackPtr_read]
    exact hs.b2
  · rw [hrsp, secondHigh_read h]
    x86_norm [secondHighEffect, stackPtr_read]
    exact hs.b3
  · rw [hrsp, secondHigh_read h]
    x86_norm [secondHighEffect, stackPtr_read]
    exact hs.p0
  · rw [hrsp, secondHigh_read h]
    x86_norm [secondHighEffect, stackPtr_read]
    exact hs.p1
  · rw [hrsp, secondHigh_read h]
    x86_norm [secondHighEffect, stackPtr_read]
    exact hs.p2
  · rw [hrsp, secondHigh_read h]
    x86_norm [secondHighEffect, stackPtr_read]
    exact hs.p3
  · rw [hrsp, secondHigh_read h]
    x86_norm [secondHighEffect, stackPtr_read]
    exact hs.inverse

theorem secondHigh_pointer {p : BitVec 64} {s t : RamState}
    (h : (secondHighEffect p s).Holds s t) : savedPtr t = savedPtr s := by
  have hrsp := Reduction.scratch_rsp (secondHigh_frame h)
  unfold savedPtr
  rw [hrsp, secondHigh_read h]
  x86_norm [secondHighEffect, stackPtr_read]

theorem secondTop_saved {p : BitVec 64} {s t : RamState} {b : Vector (BitVec 64) 4}
    (h : (secondTopEffect p s).Holds s t) (hs : Saved s b) : Saved t b := by
  have hrsp := Reduction.scratch_rsp (secondTop_frame h)
  constructor
  · rw [hrsp, secondTop_read h]
    x86_norm [secondTopEffect, stackPtr_read]
    exact hs.b0
  · rw [hrsp, secondTop_read h]
    x86_norm [secondTopEffect, stackPtr_read]
    exact hs.b1
  · rw [hrsp, secondTop_read h]
    x86_norm [secondTopEffect, stackPtr_read]
    exact hs.b2
  · rw [hrsp, secondTop_read h]
    x86_norm [secondTopEffect, stackPtr_read]
    exact hs.b3
  · rw [hrsp, secondTop_read h]
    x86_norm [secondTopEffect, stackPtr_read]
    exact hs.p0
  · rw [hrsp, secondTop_read h]
    x86_norm [secondTopEffect, stackPtr_read]
    exact hs.p1
  · rw [hrsp, secondTop_read h]
    x86_norm [secondTopEffect, stackPtr_read]
    exact hs.p2
  · rw [hrsp, secondTop_read h]
    x86_norm [secondTopEffect, stackPtr_read]
    exact hs.p3
  · rw [hrsp, secondTop_read h]
    x86_norm [secondTopEffect, stackPtr_read]
    exact hs.inverse

theorem secondTop_pointer {p : BitVec 64} {s t : RamState}
    (h : (secondTopEffect p s).Holds s t) : savedPtr t = savedPtr s := by
  have hrsp := Reduction.scratch_rsp (secondTop_frame h)
  unfold savedPtr
  rw [hrsp, secondTop_read h]
  x86_norm [secondTopEffect, stackPtr_read]

theorem thirdStart_saved {p : BitVec 64} {s t : RamState} {b : Vector (BitVec 64) 4}
    (h : (thirdStartEffect p s).Holds s t) (hs : Saved s b) : Saved t b := by
  have hrsp := Reduction.scratch_rsp (thirdStart_frame h)
  constructor
  · rw [hrsp, thirdStart_read h]
    x86_norm [thirdStartEffect, stackPtr_read]
    exact hs.b0
  · rw [hrsp, thirdStart_read h]
    x86_norm [thirdStartEffect, stackPtr_read]
    exact hs.b1
  · rw [hrsp, thirdStart_read h]
    x86_norm [thirdStartEffect, stackPtr_read]
    exact hs.b2
  · rw [hrsp, thirdStart_read h]
    x86_norm [thirdStartEffect, stackPtr_read]
    exact hs.b3
  · rw [hrsp, thirdStart_read h]
    x86_norm [thirdStartEffect, stackPtr_read]
    exact hs.p0
  · rw [hrsp, thirdStart_read h]
    x86_norm [thirdStartEffect, stackPtr_read]
    exact hs.p1
  · rw [hrsp, thirdStart_read h]
    x86_norm [thirdStartEffect, stackPtr_read]
    exact hs.p2
  · rw [hrsp, thirdStart_read h]
    x86_norm [thirdStartEffect, stackPtr_read]
    exact hs.p3
  · rw [hrsp, thirdStart_read h]
    x86_norm [thirdStartEffect, stackPtr_read]
    exact hs.inverse

theorem thirdStart_pointer {p : BitVec 64} {s t : RamState}
    (h : (thirdStartEffect p s).Holds s t) : savedPtr t = savedPtr s := by
  have hrsp := Reduction.scratch_rsp (thirdStart_frame h)
  unfold savedPtr
  rw [hrsp, thirdStart_read h]
  x86_norm [thirdStartEffect, stackPtr_read]

theorem thirdMiddle_saved {p : BitVec 64} {s t : RamState} {b : Vector (BitVec 64) 4}
    (h : (thirdMiddleEffect p s).Holds s t) (hs : Saved s b) : Saved t b := by
  have hrsp := Reduction.scratch_rsp (thirdMiddle_frame h)
  constructor
  · rw [hrsp, thirdMiddle_read h]
    x86_norm [thirdMiddleEffect, stackPtr_read]
    exact hs.b0
  · rw [hrsp, thirdMiddle_read h]
    x86_norm [thirdMiddleEffect, stackPtr_read]
    exact hs.b1
  · rw [hrsp, thirdMiddle_read h]
    x86_norm [thirdMiddleEffect, stackPtr_read]
    exact hs.b2
  · rw [hrsp, thirdMiddle_read h]
    x86_norm [thirdMiddleEffect, stackPtr_read]
    exact hs.b3
  · rw [hrsp, thirdMiddle_read h]
    x86_norm [thirdMiddleEffect, stackPtr_read]
    exact hs.p0
  · rw [hrsp, thirdMiddle_read h]
    x86_norm [thirdMiddleEffect, stackPtr_read]
    exact hs.p1
  · rw [hrsp, thirdMiddle_read h]
    x86_norm [thirdMiddleEffect, stackPtr_read]
    exact hs.p2
  · rw [hrsp, thirdMiddle_read h]
    x86_norm [thirdMiddleEffect, stackPtr_read]
    exact hs.p3
  · rw [hrsp, thirdMiddle_read h]
    x86_norm [thirdMiddleEffect, stackPtr_read]
    exact hs.inverse

theorem thirdMiddle_pointer {p : BitVec 64} {s t : RamState}
    (h : (thirdMiddleEffect p s).Holds s t) : savedPtr t = savedPtr s := by
  have hrsp := Reduction.scratch_rsp (thirdMiddle_frame h)
  unfold savedPtr
  rw [hrsp, thirdMiddle_read h]
  x86_norm [thirdMiddleEffect, stackPtr_read]

theorem thirdHigh_saved {p : BitVec 64} {s t : RamState} {b : Vector (BitVec 64) 4}
    (h : (thirdHighEffect p s).Holds s t) (hs : Saved s b) : Saved t b := by
  have hrsp := Reduction.scratch_rsp (thirdHigh_frame h)
  constructor
  · rw [hrsp, thirdHigh_read h]
    x86_norm [thirdHighEffect, stackPtr_read]
    exact hs.b0
  · rw [hrsp, thirdHigh_read h]
    x86_norm [thirdHighEffect, stackPtr_read]
    exact hs.b1
  · rw [hrsp, thirdHigh_read h]
    x86_norm [thirdHighEffect, stackPtr_read]
    exact hs.b2
  · rw [hrsp, thirdHigh_read h]
    x86_norm [thirdHighEffect, stackPtr_read]
    exact hs.b3
  · rw [hrsp, thirdHigh_read h]
    x86_norm [thirdHighEffect, stackPtr_read]
    exact hs.p0
  · rw [hrsp, thirdHigh_read h]
    x86_norm [thirdHighEffect, stackPtr_read]
    exact hs.p1
  · rw [hrsp, thirdHigh_read h]
    x86_norm [thirdHighEffect, stackPtr_read]
    exact hs.p2
  · rw [hrsp, thirdHigh_read h]
    x86_norm [thirdHighEffect, stackPtr_read]
    exact hs.p3
  · rw [hrsp, thirdHigh_read h]
    x86_norm [thirdHighEffect, stackPtr_read]
    exact hs.inverse

theorem thirdHigh_pointer {p : BitVec 64} {s t : RamState}
    (h : (thirdHighEffect p s).Holds s t) : savedPtr t = savedPtr s := by
  have hrsp := Reduction.scratch_rsp (thirdHigh_frame h)
  unfold savedPtr
  rw [hrsp, thirdHigh_read h]
  x86_norm [thirdHighEffect, stackPtr_read]

theorem thirdTop_saved {p : BitVec 64} {s t : RamState} {b : Vector (BitVec 64) 4}
    (h : (thirdTopEffect p s).Holds s t) (hs : Saved s b) : Saved t b := by
  have hrsp := Reduction.scratch_rsp (thirdTop_frame h)
  constructor
  · rw [hrsp, thirdTop_read h]
    x86_norm [thirdTopEffect, stackPtr_read]
    exact hs.b0
  · rw [hrsp, thirdTop_read h]
    x86_norm [thirdTopEffect, stackPtr_read]
    exact hs.b1
  · rw [hrsp, thirdTop_read h]
    x86_norm [thirdTopEffect, stackPtr_read]
    exact hs.b2
  · rw [hrsp, thirdTop_read h]
    x86_norm [thirdTopEffect, stackPtr_read]
    exact hs.b3
  · rw [hrsp, thirdTop_read h]
    x86_norm [thirdTopEffect, stackPtr_read]
    exact hs.p0
  · rw [hrsp, thirdTop_read h]
    x86_norm [thirdTopEffect, stackPtr_read]
    exact hs.p1
  · rw [hrsp, thirdTop_read h]
    x86_norm [thirdTopEffect, stackPtr_read]
    exact hs.p2
  · rw [hrsp, thirdTop_read h]
    x86_norm [thirdTopEffect, stackPtr_read]
    exact hs.p3
  · rw [hrsp, thirdTop_read h]
    x86_norm [thirdTopEffect, stackPtr_read]
    exact hs.inverse
end P256.Proofs.Sec1.SquareRoot.Montgomery.Rows
