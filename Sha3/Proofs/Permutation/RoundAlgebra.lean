import Sha3.Proofs.Keccak

namespace Sha3.Proofs.Permutation.RoundAlgebra

open Sha3.Proofs.Keccak

structure State where
  regs : Fin 16 → BitVec 64
  stack : Nat → BitVec 64

inductive Location where
  | reg (index : Fin 16)
  | stack (offset : Nat)
  deriving DecidableEq

def read (s : State) : Location → BitVec 64
  | .reg i => s.regs i
  | .stack o => s.stack o

def write (s : State) (dst : Location) (v : BitVec 64) : State :=
  match dst with
  | .reg i => { s with regs := fun j ↦ if j = i then v else s.regs j }
  | .stack o => { s with stack := fun p ↦ if p = o then v else s.stack p }

inductive Instruction where
  | mov (dst src : Location)
  | xor (dst src : Location)
  | and (dst src : Location)
  | not (dst : Location)
  | rol (dst : Location) (count : Nat)
  | xorConstant (dst : Location)
  deriving DecidableEq

def execute (rc : BitVec 64) (s : State) : Instruction → State
  | .mov dst src => write s dst (read s src)
  | .xor dst src => write s dst (read s dst ^^^ read s src)
  | .and dst src => write s dst (read s dst &&& read s src)
  | .not dst => write s dst (~~~ read s dst)
  | .rol dst n => write s dst ((read s dst).rotateLeft n)
  | .xorConstant dst => write s dst (read s dst ^^^ rc)

def laneLocations : Vector Location 25 := #v[
  .stack 24, .stack 128, .stack 136, .stack 120, .stack 112, .stack 32, .reg 9, .stack 48, .reg 11,
    .stack 16, .reg 0, .stack 40, .reg 12, .stack 56, .reg 13, .reg 5, .reg 1, .reg 15, .reg 14,
    .reg 3, .stack 80, .stack 96, .stack 88, .stack 104, .stack 0]

def lanes (s : State) : Lanes := fun i ↦ read s laneLocations[i.val]

def program : List (Nat × Instruction) := [
  (0x1000f0, .mov (.stack 8) (.reg 14)),
  (0x1000f5, .mov (.stack 64) (.reg 13)),
  (0x1000fa, .mov (.stack 208) (.reg 2)),
  (0x100102, .mov (.reg 2) (.stack 80)),
  (0x100107, .xor (.reg 2) (.stack 32)),
  (0x10010c, .mov (.reg 8) (.reg 5)),
  (0x10010f, .xor (.reg 8) (.reg 0)),
  (0x100112, .xor (.reg 8) (.reg 2)),
  (0x100115, .mov (.reg 2) (.stack 128)),
  (0x10011d, .xor (.reg 2) (.reg 9)),
  (0x100120, .mov (.reg 6) (.reg 15)),
  (0x100123, .mov (.stack 72) (.reg 15)),
  (0x100128, .mov (.reg 15) (.stack 96)),
  (0x10012d, .xor (.reg 15) (.reg 1)),
  (0x100130, .xor (.reg 15) (.reg 2)),
  (0x100133, .mov (.reg 2) (.reg 6)),
  (0x100136, .xor (.reg 2) (.stack 88)),
  (0x10013b, .mov (.reg 6) (.reg 12)),
  (0x10013e, .xor (.reg 6) (.stack 48)),
  (0x100143, .xor (.reg 6) (.reg 2)),
  (0x100146, .mov (.reg 7) (.reg 3)),
  (0x100149, .mov (.stack 152) (.reg 3)),
  (0x100151, .mov (.reg 3) (.reg 14)),
  (0x100154, .xor (.reg 3) (.stack 104)),
  (0x100159, .mov (.reg 2) (.stack 56)),
  (0x10015e, .mov (.reg 13) (.reg 0)),
  (0x100161, .mov (.reg 0) (.reg 2)),
  (0x100164, .xor (.reg 0) (.stack 120)),
  (0x100169, .xor (.reg 0) (.reg 3)),
  (0x10016c, .mov (.reg 3) (.reg 7)),
  (0x10016f, .xor (.reg 3) (.stack 0)),
  (0x100173, .mov (.reg 7) (.stack 64)),
  (0x100178, .xor (.reg 7) (.stack 112)),
  (0x10017d, .xor (.reg 7) (.reg 3)),
  (0x100180, .mov (.reg 3) (.stack 24)),
  (0x100185, .xor (.reg 8) (.reg 3)),
  (0x100188, .mov (.reg 10) (.reg 1)),
  (0x10018b, .mov (.reg 1) (.stack 40)),
  (0x100190, .xor (.reg 15) (.reg 1)),
  (0x100193, .xor (.reg 0) (.reg 11)),
  (0x100196, .mov (.reg 2) (.reg 0)),
  (0x100199, .rol (.reg 2) 1),
  (0x10019c, .xor (.reg 2) (.reg 15)),
  (0x10019f, .rol (.reg 15) 1),
  (0x1001a2, .mov (.reg 14) (.stack 16)),
  (0x1001a7, .xor (.reg 7) (.reg 14)),
  (0x1001aa, .xor (.reg 15) (.reg 7)),
  (0x1001ad, .xor (.reg 3) (.reg 15)),
  (0x1001b0, .mov (.stack 144) (.reg 3)),
  (0x1001b8, .xor (.stack 32) (.reg 15)),
  (0x1001bd, .xor (.reg 13) (.reg 15)),
  (0x1001c0, .mov (.stack 192) (.reg 13)),
  (0x1001c8, .xor (.reg 5) (.reg 15)),
  (0x1001cb, .xor (.reg 15) (.stack 80)),
  (0x1001d0, .mov (.stack 200) (.reg 15)),
  (0x1001d8, .mov (.reg 15) (.stack 136)),
  (0x1001e0, .xor (.reg 6) (.reg 15)),
  (0x1001e3, .rol (.reg 7) 1),
  (0x1001e6, .xor (.reg 7) (.reg 6)),
  (0x1001e9, .rol (.reg 6) 1),
  (0x1001ec, .xor (.reg 6) (.reg 8)),
  (0x1001ef, .mov (.reg 3) (.stack 128)),
  (0x1001f7, .xor (.reg 3) (.reg 6)),
  (0x1001fa, .xor (.reg 9) (.reg 6)),
  (0x1001fd, .xor (.reg 1) (.reg 6)),
  (0x100200, .mov (.stack 40) (.reg 1)),
  (0x100205, .xor (.reg 10) (.reg 6)),
  (0x100208, .mov (.stack 184) (.reg 10)),
  (0x100210, .xor (.reg 6) (.stack 96)),
  (0x100215, .xor (.reg 15) (.reg 2)),
  (0x100218, .xor (.stack 48) (.reg 2)),
  (0x10021d, .xor (.reg 12) (.reg 2)),
  (0x100220, .xor (.stack 72) (.reg 2)),
  (0x100225, .xor (.reg 2) (.stack 88)),
  (0x10022a, .mov (.reg 13) (.reg 2)),
  (0x10022d, .mov (.reg 10) (.stack 120)),
  (0x100232, .xor (.reg 10) (.reg 7)),
  (0x100235, .xor (.reg 11) (.reg 7)),
  (0x100238, .xor (.stack 56) (.reg 7)),
  (0x10023d, .mov (.reg 2) (.stack 8)),
  (0x100242, .xor (.reg 2) (.reg 7)),
  (0x100245, .rol (.reg 8) 1),
  (0x100248, .xor (.reg 7) (.stack 104)),
  (0x10024d, .mov (.stack 8) (.reg 7)),
  (0x100252, .xor (.reg 8) (.reg 0)),
  (0x100255, .mov (.reg 0) (.stack 112)),
  (0x10025a, .xor (.reg 0) (.reg 8)),
  (0x10025d, .xor (.reg 14) (.reg 8)),
  (0x100260, .mov (.stack 16) (.reg 14)),
  (0x100265, .mov (.reg 7) (.stack 64)),
  (0x10026a, .xor (.reg 7) (.reg 8)),
  (0x10026d, .xor (.stack 152) (.reg 8)),
  (0x100275, .rol (.reg 2) 21),
  (0x100279, .xor (.reg 8) (.stack 0)),
  (0x10027d, .rol (.reg 11) 55),
  (0x100281, .rol (.reg 6) 2),
  (0x100285, .rol (.reg 8) 14),
  (0x100289, .rol (.reg 5) 41),
  (0x10028d, .mov (.stack 64) (.reg 3)),
  (0x100292, .rol (.reg 12) 43),
  (0x100296, .mov (.reg 1) (.reg 15)),
  (0x100299, .rol (.reg 1) 62),
  (0x10029d, .rol (.reg 7) 39),
  (0x1002a1, .mov (.stack 176) (.reg 0)),
  (0x1002a9, .rol (.reg 9) 44),
  (0x1002ad, .mov (.reg 0) (.reg 9)),
  (0x1002b0, .not (.reg 0)),
  (0x1002b3, .and (.reg 0) (.reg 12)),
  (0x1002b6, .mov (.stack 24) (.reg 0)),
  (0x1002bb, .mov (.reg 0) (.reg 2)),
  (0x1002be, .not (.reg 2)),
  (0x1002c1, .and (.reg 2) (.reg 8)),
  (0x1002c4, .xor (.reg 2) (.reg 12)),
  (0x1002c7, .mov (.stack 136) (.reg 2)),
  (0x1002cf, .not (.reg 12)),
  (0x1002d2, .and (.reg 12) (.reg 0)),
  (0x1002d5, .mov (.reg 14) (.reg 0)),
  (0x1002d8, .xor (.reg 12) (.reg 9)),
  (0x1002db, .mov (.stack 128) (.reg 12)),
  (0x1002e3, .mov (.reg 12) (.stack 144)),
  (0x1002eb, .mov (.reg 3) (.reg 12)),
  (0x1002ee, .not (.reg 3)),
  (0x1002f1, .and (.reg 3) (.reg 9)),
  (0x1002f4, .mov (.reg 2) (.reg 11)),
  (0x1002f7, .not (.reg 2)),
  (0x1002fa, .and (.reg 2) (.reg 7)),
  (0x1002fd, .xor (.reg 2) (.reg 1)),
  (0x100300, .mov (.stack 80) (.reg 2)),
  (0x100305, .mov (.reg 2) (.reg 5)),
  (0x100308, .not (.reg 2)),
  (0x10030b, .mov (.stack 168) (.reg 6)),
  (0x100313, .and (.reg 2) (.reg 6)),
  (0x100316, .xor (.reg 2) (.reg 7)),
  (0x100319, .mov (.stack 88) (.reg 2)),
  (0x10031e, .mov (.reg 15) (.reg 7)),
  (0x100321, .not (.reg 15)),
  (0x100324, .and (.reg 15) (.reg 5)),
  (0x100327, .xor (.reg 15) (.reg 11)),
  (0x10032a, .mov (.stack 96) (.reg 15)),
  (0x10032f, .mov (.reg 7) (.reg 6)),
  (0x100332, .not (.reg 7)),
  (0x100335, .and (.reg 7) (.reg 1)),
  (0x100338, .not (.reg 1)),
  (0x10033b, .and (.reg 1) (.reg 11)),
  (0x10033e, .mov (.stack 0) (.reg 1)),
  (0x100342, .mov (.reg 0) (.stack 192)),
  (0x10034a, .rol (.reg 0) 3),
  (0x10034e, .mov (.reg 6) (.reg 10)),
  (0x100351, .rol (.reg 6) 28),
  (0x100355, .mov (.reg 1) (.stack 32)),
  (0x10035a, .mov (.reg 10) (.stack 184)),
  (0x100362, .rol (.reg 10) 45),
  (0x100366, .rol (.reg 13) 61),
  (0x10036a, .mov (.reg 15) (.stack 16)),
  (0x10036f, .rol (.reg 15) 20),
  (0x100373, .mov (.reg 9) (.reg 15)),
  (0x100376, .not (.reg 9)),
  (0x100379, .and (.reg 9) (.reg 0)),
  (0x10037c, .xor (.reg 9) (.reg 6)),
  (0x10037f, .mov (.stack 32) (.reg 9)),
  (0x100384, .mov (.reg 9) (.reg 0)),
  (0x100387, .not (.reg 9)),
  (0x10038a, .and (.reg 9) (.reg 10)),
  (0x10038d, .xor (.reg 9) (.reg 15)),
  (0x100390, .mov (.reg 11) (.reg 13)),
  (0x100393, .not (.reg 11)),
  (0x100396, .and (.reg 11) (.reg 6)),
  (0x100399, .not (.reg 6)),
  (0x10039c, .and (.reg 15) (.reg 6)),
  (0x10039f, .mov (.reg 6) (.reg 8)),
  (0x1003a2, .not (.reg 6)),
  (0x1003a5, .and (.reg 6) (.reg 12)),
  (0x1003a8, .xor (.reg 6) (.reg 14)),
  (0x1003ab, .mov (.stack 120) (.reg 6)),
  (0x1003b0, .xor (.reg 3) (.reg 8)),
  (0x1003b3, .mov (.stack 112) (.reg 3)),
  (0x1003b8, .mov (.reg 6) (.stack 48)),
  (0x1003bd, .mov (.reg 3) (.reg 10)),
  (0x1003c0, .not (.reg 3)),
  (0x1003c3, .and (.reg 3) (.reg 13)),
  (0x1003c6, .xor (.reg 3) (.reg 0)),
  (0x1003c9, .mov (.stack 48) (.reg 3)),
  (0x1003ce, .xor (.reg 11) (.reg 10)),
  (0x1003d1, .xor (.reg 15) (.reg 13)),
  (0x1003d4, .mov (.stack 16) (.reg 15)),
  (0x1003d9, .xor (.reg 7) (.reg 5)),
  (0x1003dc, .mov (.stack 104) (.reg 7)),
  (0x1003e1, .mov (.reg 0) (.stack 40)),
  (0x1003e6, .rol (.reg 0) 10),
  (0x1003ea, .mov (.reg 3) (.stack 72)),
  (0x1003ef, .rol (.reg 3) 15),
  (0x1003f3, .mov (.reg 5) (.reg 1)),
  (0x1003f6, .rol (.reg 5) 36),
  (0x1003fa, .mov (.stack 72) (.reg 5)),
  (0x1003ff, .mov (.reg 8) (.stack 176)),
  (0x100407, .rol (.reg 8) 27),
  (0x10040b, .mov (.reg 2) (.stack 8)),
  (0x100410, .rol (.reg 2) 56),
  (0x100414, .mov (.stack 8) (.reg 2)),
  (0x100419, .not (.reg 5)),
  (0x10041c, .and (.reg 5) (.reg 0)),
  (0x10041f, .mov (.reg 1) (.reg 0)),
  (0x100422, .not (.reg 1)),
  (0x100425, .and (.reg 1) (.reg 3)),
  (0x100428, .mov (.reg 14) (.reg 2)),
  (0x10042b, .not (.reg 14)),
  (0x10042e, .and (.reg 14) (.reg 8)),
  (0x100431, .xor (.reg 14) (.reg 3)),
  (0x100434, .mov (.reg 15) (.reg 3)),
  (0x100437, .not (.reg 15)),
  (0x10043a, .and (.reg 15) (.reg 2)),
  (0x10043d, .xor (.reg 15) (.reg 0)),
  (0x100440, .mov (.reg 2) (.stack 64)),
  (0x100445, .rol (.reg 2) 1),
  (0x100448, .rol (.reg 6) 6),
  (0x10044c, .mov (.reg 7) (.stack 152)),
  (0x100454, .rol (.reg 7) 8),
  (0x100458, .mov (.reg 3) (.stack 56)),
  (0x10045d, .rol (.reg 3) 25),
  (0x100461, .mov (.reg 10) (.stack 200)),
  (0x100469, .rol (.reg 10) 18),
  (0x10046d, .mov (.reg 0) (.reg 6)),
  (0x100470, .not (.reg 0)),
  (0x100473, .and (.reg 0) (.reg 3)),
  (0x100476, .mov (.reg 12) (.reg 7)),
  (0x100479, .not (.reg 12)),
  (0x10047c, .and (.reg 12) (.reg 10)),
  (0x10047f, .xor (.reg 12) (.reg 3)),
  (0x100482, .not (.reg 3)),
  (0x100485, .and (.reg 3) (.reg 7)),
  (0x100488, .mov (.reg 13) (.reg 10)),
  (0x10048b, .not (.reg 13)),
  (0x10048e, .and (.reg 13) (.reg 2)),
  (0x100491, .xor (.reg 13) (.reg 7)),
  (0x100494, .mov (.stack 56) (.reg 13)),
  (0x100499, .xor (.reg 0) (.reg 2)),
  (0x10049c, .xor (.reg 3) (.reg 6)),
  (0x10049f, .mov (.stack 40) (.reg 3)),
  (0x1004a4, .not (.reg 2)),
  (0x1004a7, .and (.reg 2) (.reg 6)),
  (0x1004aa, .mov (.reg 13) (.reg 2)),
  (0x1004ad, .xor (.reg 13) (.reg 10)),
  (0x1004b0, .xor (.reg 5) (.reg 8)),
  (0x1004b3, .mov (.reg 2) (.stack 72)),
  (0x1004b8, .xor (.reg 1) (.reg 2)),
  (0x1004bb, .not (.reg 8)),
  (0x1004be, .and (.reg 8) (.reg 2)),
  (0x1004c1, .mov (.reg 2) (.stack 208)),
  (0x1004c9, .mov (.reg 3) (.reg 8)),
  (0x1004cc, .xor (.reg 3) (.stack 8)),
  (0x1004d1, .mov (.reg 6) (.stack 24)),
  (0x1004d6, .xorConstant (.reg 6)),
  (0x1004dd, .mov (.reg 7) (.stack 0)),
  (0x1004e1, .xor (.reg 7) (.stack 168)),
  (0x1004e9, .mov (.stack 0) (.reg 7)),
  (0x1004ed, .xor (.reg 6) (.stack 144)),
  (0x1004f5, .mov (.stack 24) (.reg 6))]

def run (rc : BitVec 64) (s : State) : State :=
  program.foldl (fun s entry ↦ execute rc s entry.2) s


def rotated (a : Lanes) : Lanes :=
  let c0 := ((((a 15) ^^^ (a 10)) ^^^ ((a 20) ^^^ (a 5))) ^^^ (a 0))
  let c1 := ((((a 21) ^^^ (a 16)) ^^^ ((a 1) ^^^ (a 6))) ^^^ (a 11))
  let c2 := ((((a 12) ^^^ (a 7)) ^^^ ((a 17) ^^^ (a 22))) ^^^ (a 2))
  let c3 := ((((a 13) ^^^ (a 3)) ^^^ ((a 18) ^^^ (a 23))) ^^^ (a 8))
  let c4 := ((((a 14) ^^^ (a 4)) ^^^ ((a 19) ^^^ (a 24))) ^^^ (a 9))
  let d0 := ((c1).rotateLeft 1 ^^^ c4)
  let d1 := ((c2).rotateLeft 1 ^^^ c0)
  let d2 := ((c3).rotateLeft 1 ^^^ c1)
  let d3 := ((c4).rotateLeft 1 ^^^ c2)
  let d4 := ((c0).rotateLeft 1 ^^^ c3)
  let b0 := (a 0 ^^^ d0)
  let b1 := ((a 1 ^^^ d1)).rotateLeft 1
  let b2 := ((a 2 ^^^ d2)).rotateLeft 62
  let b3 := ((a 3 ^^^ d3)).rotateLeft 28
  let b4 := ((a 4 ^^^ d4)).rotateLeft 27
  let b5 := ((a 5 ^^^ d0)).rotateLeft 36
  let b6 := ((a 6 ^^^ d1)).rotateLeft 44
  let b7 := ((a 7 ^^^ d2)).rotateLeft 6
  let b8 := ((a 8 ^^^ d3)).rotateLeft 55
  let b9 := ((a 9 ^^^ d4)).rotateLeft 20
  let b10 := ((a 10 ^^^ d0)).rotateLeft 3
  let b11 := ((a 11 ^^^ d1)).rotateLeft 10
  let b12 := ((a 12 ^^^ d2)).rotateLeft 43
  let b13 := ((a 13 ^^^ d3)).rotateLeft 25
  let b14 := ((a 14 ^^^ d4)).rotateLeft 39
  let b15 := ((a 15 ^^^ d0)).rotateLeft 41
  let b16 := ((a 16 ^^^ d1)).rotateLeft 45
  let b17 := ((a 17 ^^^ d2)).rotateLeft 15
  let b18 := ((a 18 ^^^ d3)).rotateLeft 21
  let b19 := ((a 19 ^^^ d4)).rotateLeft 8
  let b20 := ((d0 ^^^ a 20)).rotateLeft 18
  let b21 := ((d1 ^^^ a 21)).rotateLeft 2
  let b22 := ((d2 ^^^ a 22)).rotateLeft 61
  let b23 := ((d3 ^^^ a 23)).rotateLeft 56
  let b24 := ((d4 ^^^ a 24)).rotateLeft 14
  let result : Vector (BitVec 64) 25 := #v[b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12,
    b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24]
  fun i ↦ result[i.val]

def outputExpression (b : Lanes) (rc : BitVec 64) : Lanes :=
  let result : Vector (BitVec 64) 25 := #v[
    (((~~~ (b 6) &&& b 12) ^^^ rc) ^^^ b 0),
    ((~~~ (b 12) &&& b 18) ^^^ b 6),
    ((~~~ (b 18) &&& b 24) ^^^ b 12),
    ((~~~ (b 24) &&& b 0) ^^^ b 18),
    ((~~~ (b 0) &&& b 6) ^^^ b 24),
    ((~~~ (b 9) &&& b 10) ^^^ b 3),
    ((~~~ (b 10) &&& b 16) ^^^ b 9),
    ((~~~ (b 16) &&& b 22) ^^^ b 10),
    ((~~~ (b 22) &&& b 3) ^^^ b 16),
    ((b 9 &&& ~~~ (b 3)) ^^^ b 22),
    ((~~~ (b 7) &&& b 13) ^^^ b 1),
    ((~~~ (b 13) &&& b 19) ^^^ b 7),
    ((~~~ (b 19) &&& b 20) ^^^ b 13),
    ((~~~ (b 20) &&& b 1) ^^^ b 19),
    ((~~~ (b 1) &&& b 7) ^^^ b 20),
    ((~~~ (b 5) &&& b 11) ^^^ b 4),
    ((~~~ (b 11) &&& b 17) ^^^ b 5),
    ((~~~ (b 17) &&& b 23) ^^^ b 11),
    ((~~~ (b 23) &&& b 4) ^^^ b 17),
    ((~~~ (b 4) &&& b 5) ^^^ b 23),
    ((~~~ (b 8) &&& b 14) ^^^ b 2),
    ((~~~ (b 14) &&& b 15) ^^^ b 8),
    ((~~~ (b 15) &&& b 21) ^^^ b 14),
    ((~~~ (b 21) &&& b 2) ^^^ b 15),
    ((~~~ (b 2) &&& b 8) ^^^ b 21)]
  fun i ↦ result[i.val]

def expression (a : Lanes) (rc : BitVec 64) : Lanes :=
  outputExpression (rotated a) rc

set_option maxRecDepth 4096 in
theorem lanes_run_expression (s : State) (rc : BitVec 64) :
    lanes (run rc s) = expression (lanes s) rc := by
  funext i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨
    i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21
    ∨ i = 22 ∨ i = 23 ∨ i = 24 := by omega
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl

theorem rotateLeft_zero (a : BitVec n) : a.rotateLeft 0 = a := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro z hz
  simp only [BitVec.getLsbD_rotateLeft, Nat.zero_mod, Nat.not_lt_zero, ite_false,
    hz, decide_true, Bool.true_and, Nat.sub_zero]

theorem rotated_eq (a : Lanes) : rotated a = rho (theta a) := by
  have h0 : ((((a 15) ^^^ (a 10)) ^^^ ((a 20) ^^^ (a 5))) ^^^ (a 0)) = columnParity a 0 := by
    change ((((a 15) ^^^ (a 10)) ^^^ ((a 20) ^^^ (a 5))) ^^^ (a 0)) = (((((a 0) ^^^ (a 5)) ^^^ (a
      10)) ^^^ (a 15)) ^^^ (a 20))
    ac_rfl
  have h1 : ((((a 21) ^^^ (a 16)) ^^^ ((a 1) ^^^ (a 6))) ^^^ (a 11)) = columnParity a 1 := by
    change ((((a 21) ^^^ (a 16)) ^^^ ((a 1) ^^^ (a 6))) ^^^ (a 11)) = (((((a 1) ^^^ (a 6)) ^^^ (a
      11)) ^^^ (a 16)) ^^^ (a 21))
    ac_rfl
  have h2 : ((((a 12) ^^^ (a 7)) ^^^ ((a 17) ^^^ (a 22))) ^^^ (a 2)) = columnParity a 2 := by
    change ((((a 12) ^^^ (a 7)) ^^^ ((a 17) ^^^ (a 22))) ^^^ (a 2)) = (((((a 2) ^^^ (a 7)) ^^^ (a
      12)) ^^^ (a 17)) ^^^ (a 22))
    ac_rfl
  have h3 : ((((a 13) ^^^ (a 3)) ^^^ ((a 18) ^^^ (a 23))) ^^^ (a 8)) = columnParity a 3 := by
    change ((((a 13) ^^^ (a 3)) ^^^ ((a 18) ^^^ (a 23))) ^^^ (a 8)) = (((((a 3) ^^^ (a 8)) ^^^ (a
      13)) ^^^ (a 18)) ^^^ (a 23))
    ac_rfl
  have h4 : ((((a 14) ^^^ (a 4)) ^^^ ((a 19) ^^^ (a 24))) ^^^ (a 9)) = columnParity a 4 := by
    change ((((a 14) ^^^ (a 4)) ^^^ ((a 19) ^^^ (a 24))) ^^^ (a 9)) = (((((a 4) ^^^ (a 9)) ^^^ (a
      14)) ^^^ (a 19)) ^^^ (a 24))
    ac_rfl
  funext i
  rw [rho_apply]
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨
    i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21
    ∨ i = 22 ∨ i = 23 ∨ i = 24 := by omega
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change ((a 0) ^^^ ((((((a 21) ^^^ (a 16)) ^^^ ((a 1) ^^^ (a 6))) ^^^ (a 11)).rotateLeft 1) ^^^
    ((((a 14) ^^^ (a 4)) ^^^ ((a 19) ^^^ (a 24))) ^^^ (a 9)))) = ((a 0) ^^^ (columnParity a 4 ^^^
    (columnParity a 1).rotateLeft 1)).rotateLeft 0
    rw [h1, h4]
    rw [rotateLeft_zero]
    rw [BitVec.xor_comm ((columnParity a 1).rotateLeft 1) (columnParity a 4)]
  · change (((a 1) ^^^ ((((((a 12) ^^^ (a 7)) ^^^ ((a 17) ^^^ (a 22))) ^^^ (a 2)).rotateLeft 1) ^^^
    ((((a 15) ^^^ (a 10)) ^^^ ((a 20) ^^^ (a 5))) ^^^ (a 0)))).rotateLeft 1) = ((a 1) ^^^
    (columnParity a 0 ^^^ (columnParity a 2).rotateLeft 1)).rotateLeft 1
    rw [h0, h2]
    rw [BitVec.xor_comm ((columnParity a 2).rotateLeft 1) (columnParity a 0)]
  · change (((a 2) ^^^ ((((((a 13) ^^^ (a 3)) ^^^ ((a 18) ^^^ (a 23))) ^^^ (a 8)).rotateLeft 1) ^^^
    ((((a 21) ^^^ (a 16)) ^^^ ((a 1) ^^^ (a 6))) ^^^ (a 11)))).rotateLeft 62) = ((a 2) ^^^
    (columnParity a 1 ^^^ (columnParity a 3).rotateLeft 1)).rotateLeft 62
    rw [h1, h3]
    rw [BitVec.xor_comm ((columnParity a 3).rotateLeft 1) (columnParity a 1)]
  · change (((a 3) ^^^ ((((((a 14) ^^^ (a 4)) ^^^ ((a 19) ^^^ (a 24))) ^^^ (a 9)).rotateLeft 1) ^^^
    ((((a 12) ^^^ (a 7)) ^^^ ((a 17) ^^^ (a 22))) ^^^ (a 2)))).rotateLeft 28) = ((a 3) ^^^
    (columnParity a 2 ^^^ (columnParity a 4).rotateLeft 1)).rotateLeft 28
    rw [h2, h4]
    rw [BitVec.xor_comm ((columnParity a 4).rotateLeft 1) (columnParity a 2)]
  · change (((a 4) ^^^ ((((((a 15) ^^^ (a 10)) ^^^ ((a 20) ^^^ (a 5))) ^^^ (a 0)).rotateLeft 1) ^^^
    ((((a 13) ^^^ (a 3)) ^^^ ((a 18) ^^^ (a 23))) ^^^ (a 8)))).rotateLeft 27) = ((a 4) ^^^
    (columnParity a 3 ^^^ (columnParity a 0).rotateLeft 1)).rotateLeft 27
    rw [h0, h3]
    rw [BitVec.xor_comm ((columnParity a 0).rotateLeft 1) (columnParity a 3)]
  · change (((a 5) ^^^ ((((((a 21) ^^^ (a 16)) ^^^ ((a 1) ^^^ (a 6))) ^^^ (a 11)).rotateLeft 1) ^^^
    ((((a 14) ^^^ (a 4)) ^^^ ((a 19) ^^^ (a 24))) ^^^ (a 9)))).rotateLeft 36) = ((a 5) ^^^
    (columnParity a 4 ^^^ (columnParity a 1).rotateLeft 1)).rotateLeft 36
    rw [h1, h4]
    rw [BitVec.xor_comm ((columnParity a 1).rotateLeft 1) (columnParity a 4)]
  · change (((a 6) ^^^ ((((((a 12) ^^^ (a 7)) ^^^ ((a 17) ^^^ (a 22))) ^^^ (a 2)).rotateLeft 1) ^^^
    ((((a 15) ^^^ (a 10)) ^^^ ((a 20) ^^^ (a 5))) ^^^ (a 0)))).rotateLeft 44) = ((a 6) ^^^
    (columnParity a 0 ^^^ (columnParity a 2).rotateLeft 1)).rotateLeft 44
    rw [h0, h2]
    rw [BitVec.xor_comm ((columnParity a 2).rotateLeft 1) (columnParity a 0)]
  · change (((a 7) ^^^ ((((((a 13) ^^^ (a 3)) ^^^ ((a 18) ^^^ (a 23))) ^^^ (a 8)).rotateLeft 1) ^^^
    ((((a 21) ^^^ (a 16)) ^^^ ((a 1) ^^^ (a 6))) ^^^ (a 11)))).rotateLeft 6) = ((a 7) ^^^
    (columnParity a 1 ^^^ (columnParity a 3).rotateLeft 1)).rotateLeft 6
    rw [h1, h3]
    rw [BitVec.xor_comm ((columnParity a 3).rotateLeft 1) (columnParity a 1)]
  · change (((a 8) ^^^ ((((((a 14) ^^^ (a 4)) ^^^ ((a 19) ^^^ (a 24))) ^^^ (a 9)).rotateLeft 1) ^^^
    ((((a 12) ^^^ (a 7)) ^^^ ((a 17) ^^^ (a 22))) ^^^ (a 2)))).rotateLeft 55) = ((a 8) ^^^
    (columnParity a 2 ^^^ (columnParity a 4).rotateLeft 1)).rotateLeft 55
    rw [h2, h4]
    rw [BitVec.xor_comm ((columnParity a 4).rotateLeft 1) (columnParity a 2)]
  · change (((a 9) ^^^ ((((((a 15) ^^^ (a 10)) ^^^ ((a 20) ^^^ (a 5))) ^^^ (a 0)).rotateLeft 1) ^^^
    ((((a 13) ^^^ (a 3)) ^^^ ((a 18) ^^^ (a 23))) ^^^ (a 8)))).rotateLeft 20) = ((a 9) ^^^
    (columnParity a 3 ^^^ (columnParity a 0).rotateLeft 1)).rotateLeft 20
    rw [h0, h3]
    rw [BitVec.xor_comm ((columnParity a 0).rotateLeft 1) (columnParity a 3)]
  · change (((a 10) ^^^ ((((((a 21) ^^^ (a 16)) ^^^ ((a 1) ^^^ (a 6))) ^^^ (a 11)).rotateLeft 1) ^^^
    ((((a 14) ^^^ (a 4)) ^^^ ((a 19) ^^^ (a 24))) ^^^ (a 9)))).rotateLeft 3) = ((a 10) ^^^
    (columnParity a 4 ^^^ (columnParity a 1).rotateLeft 1)).rotateLeft 3
    rw [h1, h4]
    rw [BitVec.xor_comm ((columnParity a 1).rotateLeft 1) (columnParity a 4)]
  · change (((a 11) ^^^ ((((((a 12) ^^^ (a 7)) ^^^ ((a 17) ^^^ (a 22))) ^^^ (a 2)).rotateLeft 1) ^^^
    ((((a 15) ^^^ (a 10)) ^^^ ((a 20) ^^^ (a 5))) ^^^ (a 0)))).rotateLeft 10) = ((a 11) ^^^
    (columnParity a 0 ^^^ (columnParity a 2).rotateLeft 1)).rotateLeft 10
    rw [h0, h2]
    rw [BitVec.xor_comm ((columnParity a 2).rotateLeft 1) (columnParity a 0)]
  · change (((a 12) ^^^ ((((((a 13) ^^^ (a 3)) ^^^ ((a 18) ^^^ (a 23))) ^^^ (a 8)).rotateLeft 1) ^^^
    ((((a 21) ^^^ (a 16)) ^^^ ((a 1) ^^^ (a 6))) ^^^ (a 11)))).rotateLeft 43) = ((a 12) ^^^
    (columnParity a 1 ^^^ (columnParity a 3).rotateLeft 1)).rotateLeft 43
    rw [h1, h3]
    rw [BitVec.xor_comm ((columnParity a 3).rotateLeft 1) (columnParity a 1)]
  · change (((a 13) ^^^ ((((((a 14) ^^^ (a 4)) ^^^ ((a 19) ^^^ (a 24))) ^^^ (a 9)).rotateLeft 1) ^^^
    ((((a 12) ^^^ (a 7)) ^^^ ((a 17) ^^^ (a 22))) ^^^ (a 2)))).rotateLeft 25) = ((a 13) ^^^
    (columnParity a 2 ^^^ (columnParity a 4).rotateLeft 1)).rotateLeft 25
    rw [h2, h4]
    rw [BitVec.xor_comm ((columnParity a 4).rotateLeft 1) (columnParity a 2)]
  · change (((a 14) ^^^ ((((((a 15) ^^^ (a 10)) ^^^ ((a 20) ^^^ (a 5))) ^^^ (a 0)).rotateLeft 1) ^^^
    ((((a 13) ^^^ (a 3)) ^^^ ((a 18) ^^^ (a 23))) ^^^ (a 8)))).rotateLeft 39) = ((a 14) ^^^
    (columnParity a 3 ^^^ (columnParity a 0).rotateLeft 1)).rotateLeft 39
    rw [h0, h3]
    rw [BitVec.xor_comm ((columnParity a 0).rotateLeft 1) (columnParity a 3)]
  · change (((a 15) ^^^ ((((((a 21) ^^^ (a 16)) ^^^ ((a 1) ^^^ (a 6))) ^^^ (a 11)).rotateLeft 1) ^^^
    ((((a 14) ^^^ (a 4)) ^^^ ((a 19) ^^^ (a 24))) ^^^ (a 9)))).rotateLeft 41) = ((a 15) ^^^
    (columnParity a 4 ^^^ (columnParity a 1).rotateLeft 1)).rotateLeft 41
    rw [h1, h4]
    rw [BitVec.xor_comm ((columnParity a 1).rotateLeft 1) (columnParity a 4)]
  · change (((a 16) ^^^ ((((((a 12) ^^^ (a 7)) ^^^ ((a 17) ^^^ (a 22))) ^^^ (a 2)).rotateLeft 1) ^^^
    ((((a 15) ^^^ (a 10)) ^^^ ((a 20) ^^^ (a 5))) ^^^ (a 0)))).rotateLeft 45) = ((a 16) ^^^
    (columnParity a 0 ^^^ (columnParity a 2).rotateLeft 1)).rotateLeft 45
    rw [h0, h2]
    rw [BitVec.xor_comm ((columnParity a 2).rotateLeft 1) (columnParity a 0)]
  · change (((a 17) ^^^ ((((((a 13) ^^^ (a 3)) ^^^ ((a 18) ^^^ (a 23))) ^^^ (a 8)).rotateLeft 1) ^^^
    ((((a 21) ^^^ (a 16)) ^^^ ((a 1) ^^^ (a 6))) ^^^ (a 11)))).rotateLeft 15) = ((a 17) ^^^
    (columnParity a 1 ^^^ (columnParity a 3).rotateLeft 1)).rotateLeft 15
    rw [h1, h3]
    rw [BitVec.xor_comm ((columnParity a 3).rotateLeft 1) (columnParity a 1)]
  · change (((a 18) ^^^ ((((((a 14) ^^^ (a 4)) ^^^ ((a 19) ^^^ (a 24))) ^^^ (a 9)).rotateLeft 1) ^^^
    ((((a 12) ^^^ (a 7)) ^^^ ((a 17) ^^^ (a 22))) ^^^ (a 2)))).rotateLeft 21) = ((a 18) ^^^
    (columnParity a 2 ^^^ (columnParity a 4).rotateLeft 1)).rotateLeft 21
    rw [h2, h4]
    rw [BitVec.xor_comm ((columnParity a 4).rotateLeft 1) (columnParity a 2)]
  · change (((a 19) ^^^ ((((((a 15) ^^^ (a 10)) ^^^ ((a 20) ^^^ (a 5))) ^^^ (a 0)).rotateLeft 1) ^^^
    ((((a 13) ^^^ (a 3)) ^^^ ((a 18) ^^^ (a 23))) ^^^ (a 8)))).rotateLeft 8) = ((a 19) ^^^
    (columnParity a 3 ^^^ (columnParity a 0).rotateLeft 1)).rotateLeft 8
    rw [h0, h3]
    rw [BitVec.xor_comm ((columnParity a 0).rotateLeft 1) (columnParity a 3)]
  · change ((((((((a 21) ^^^ (a 16)) ^^^ ((a 1) ^^^ (a 6))) ^^^ (a 11)).rotateLeft 1) ^^^ ((((a 14)
    ^^^ (a 4)) ^^^ ((a 19) ^^^ (a 24))) ^^^ (a 9))) ^^^ (a 20)).rotateLeft 18) = ((a 20) ^^^
    (columnParity a 4 ^^^ (columnParity a 1).rotateLeft 1)).rotateLeft 18
    rw [h1, h4]
    rw [BitVec.xor_comm ((columnParity a 1).rotateLeft 1 ^^^ columnParity a 4) (a 20)]
    rw [BitVec.xor_comm ((columnParity a 1).rotateLeft 1) (columnParity a 4)]
  · change ((((((((a 12) ^^^ (a 7)) ^^^ ((a 17) ^^^ (a 22))) ^^^ (a 2)).rotateLeft 1) ^^^ ((((a 15)
    ^^^ (a 10)) ^^^ ((a 20) ^^^ (a 5))) ^^^ (a 0))) ^^^ (a 21)).rotateLeft 2) = ((a 21) ^^^
    (columnParity a 0 ^^^ (columnParity a 2).rotateLeft 1)).rotateLeft 2
    rw [h0, h2]
    rw [BitVec.xor_comm ((columnParity a 2).rotateLeft 1 ^^^ columnParity a 0) (a 21)]
    rw [BitVec.xor_comm ((columnParity a 2).rotateLeft 1) (columnParity a 0)]
  · change ((((((((a 13) ^^^ (a 3)) ^^^ ((a 18) ^^^ (a 23))) ^^^ (a 8)).rotateLeft 1) ^^^ ((((a 21)
    ^^^ (a 16)) ^^^ ((a 1) ^^^ (a 6))) ^^^ (a 11))) ^^^ (a 22)).rotateLeft 61) = ((a 22) ^^^
    (columnParity a 1 ^^^ (columnParity a 3).rotateLeft 1)).rotateLeft 61
    rw [h1, h3]
    rw [BitVec.xor_comm ((columnParity a 3).rotateLeft 1 ^^^ columnParity a 1) (a 22)]
    rw [BitVec.xor_comm ((columnParity a 3).rotateLeft 1) (columnParity a 1)]
  · change ((((((((a 14) ^^^ (a 4)) ^^^ ((a 19) ^^^ (a 24))) ^^^ (a 9)).rotateLeft 1) ^^^ ((((a 12)
    ^^^ (a 7)) ^^^ ((a 17) ^^^ (a 22))) ^^^ (a 2))) ^^^ (a 23)).rotateLeft 56) = ((a 23) ^^^
    (columnParity a 2 ^^^ (columnParity a 4).rotateLeft 1)).rotateLeft 56
    rw [h2, h4]
    rw [BitVec.xor_comm ((columnParity a 4).rotateLeft 1 ^^^ columnParity a 2) (a 23)]
    rw [BitVec.xor_comm ((columnParity a 4).rotateLeft 1) (columnParity a 2)]
  · change ((((((((a 15) ^^^ (a 10)) ^^^ ((a 20) ^^^ (a 5))) ^^^ (a 0)).rotateLeft 1) ^^^ ((((a 13)
    ^^^ (a 3)) ^^^ ((a 18) ^^^ (a 23))) ^^^ (a 8))) ^^^ (a 24)).rotateLeft 14) = ((a 24) ^^^
    (columnParity a 3 ^^^ (columnParity a 0).rotateLeft 1)).rotateLeft 14
    rw [h0, h3]
    rw [BitVec.xor_comm ((columnParity a 0).rotateLeft 1 ^^^ columnParity a 3) (a 24)]
    rw [BitVec.xor_comm ((columnParity a 0).rotateLeft 1) (columnParity a 3)]

theorem outputExpression_eq (b : Lanes) (ir : Int) :
    outputExpression b (roundConstant ir) = iota (chi (pi b)) ir := by
  funext i
  have hi : i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 ∨ i = 4 ∨ i = 5 ∨ i = 6 ∨ i = 7 ∨ i = 8 ∨ i = 9 ∨ i = 10 ∨
    i = 11 ∨ i = 12 ∨ i = 13 ∨ i = 14 ∨ i = 15 ∨ i = 16 ∨ i = 17 ∨ i = 18 ∨ i = 19 ∨ i = 20 ∨ i = 21
    ∨ i = 22 ∨ i = 23 ∨ i = 24 := by omega
  rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · change (((~~~ (b 6) &&& b 12) ^^^ (roundConstant ir)) ^^^ b 0) = (b 0 ^^^ (~~~ b 6 &&& b 12))
    ^^^ roundConstant ir
    ac_rfl
  · change ((~~~ (b 12) &&& b 18) ^^^ b 6) = b 6 ^^^ (~~~ b 12 &&& b 18)
    ac_rfl
  · change ((~~~ (b 18) &&& b 24) ^^^ b 12) = b 12 ^^^ (~~~ b 18 &&& b 24)
    ac_rfl
  · change ((~~~ (b 24) &&& b 0) ^^^ b 18) = b 18 ^^^ (~~~ b 24 &&& b 0)
    ac_rfl
  · change ((~~~ (b 0) &&& b 6) ^^^ b 24) = b 24 ^^^ (~~~ b 0 &&& b 6)
    ac_rfl
  · change ((~~~ (b 9) &&& b 10) ^^^ b 3) = b 3 ^^^ (~~~ b 9 &&& b 10)
    ac_rfl
  · change ((~~~ (b 10) &&& b 16) ^^^ b 9) = b 9 ^^^ (~~~ b 10 &&& b 16)
    ac_rfl
  · change ((~~~ (b 16) &&& b 22) ^^^ b 10) = b 10 ^^^ (~~~ b 16 &&& b 22)
    ac_rfl
  · change ((~~~ (b 22) &&& b 3) ^^^ b 16) = b 16 ^^^ (~~~ b 22 &&& b 3)
    ac_rfl
  · change ((b 9 &&& ~~~ (b 3)) ^^^ b 22) = b 22 ^^^ (~~~ b 3 &&& b 9)
    ac_rfl
  · change ((~~~ (b 7) &&& b 13) ^^^ b 1) = b 1 ^^^ (~~~ b 7 &&& b 13)
    ac_rfl
  · change ((~~~ (b 13) &&& b 19) ^^^ b 7) = b 7 ^^^ (~~~ b 13 &&& b 19)
    ac_rfl
  · change ((~~~ (b 19) &&& b 20) ^^^ b 13) = b 13 ^^^ (~~~ b 19 &&& b 20)
    ac_rfl
  · change ((~~~ (b 20) &&& b 1) ^^^ b 19) = b 19 ^^^ (~~~ b 20 &&& b 1)
    ac_rfl
  · change ((~~~ (b 1) &&& b 7) ^^^ b 20) = b 20 ^^^ (~~~ b 1 &&& b 7)
    ac_rfl
  · change ((~~~ (b 5) &&& b 11) ^^^ b 4) = b 4 ^^^ (~~~ b 5 &&& b 11)
    ac_rfl
  · change ((~~~ (b 11) &&& b 17) ^^^ b 5) = b 5 ^^^ (~~~ b 11 &&& b 17)
    ac_rfl
  · change ((~~~ (b 17) &&& b 23) ^^^ b 11) = b 11 ^^^ (~~~ b 17 &&& b 23)
    ac_rfl
  · change ((~~~ (b 23) &&& b 4) ^^^ b 17) = b 17 ^^^ (~~~ b 23 &&& b 4)
    ac_rfl
  · change ((~~~ (b 4) &&& b 5) ^^^ b 23) = b 23 ^^^ (~~~ b 4 &&& b 5)
    ac_rfl
  · change ((~~~ (b 8) &&& b 14) ^^^ b 2) = b 2 ^^^ (~~~ b 8 &&& b 14)
    ac_rfl
  · change ((~~~ (b 14) &&& b 15) ^^^ b 8) = b 8 ^^^ (~~~ b 14 &&& b 15)
    ac_rfl
  · change ((~~~ (b 15) &&& b 21) ^^^ b 14) = b 14 ^^^ (~~~ b 15 &&& b 21)
    ac_rfl
  · change ((~~~ (b 21) &&& b 2) ^^^ b 15) = b 15 ^^^ (~~~ b 21 &&& b 2)
    ac_rfl
  · change ((~~~ (b 2) &&& b 8) ^^^ b 21) = b 21 ^^^ (~~~ b 2 &&& b 8)
    ac_rfl

theorem expression_eq_roundLanes (a : Lanes) (ir : Int) :
    expression a (roundConstant ir) = roundLanes a ir := by
  rw [expression, rotated_eq, outputExpression_eq]
  rfl

theorem lanes_run (s : State) (ir : Int) :
    lanes (run (roundConstant ir) s) = roundLanes (lanes s) ir := by
  rw [lanes_run_expression, expression_eq_roundLanes]

def runPrefix (rc : BitVec 64) (s : State) (n : Nat) : State :=
  (program.take n).foldl (fun s entry ↦ execute rc s entry.2) s

set_option maxRecDepth 4096 in
theorem regs_counter_beforeConstant (s : State) (rc : BitVec 64) :
    (runPrefix rc s 251).regs 2 = s.regs 2 := by
  rfl

set_option maxRecDepth 4096 in
theorem regs_counter_run (s : State) (rc : BitVec 64) :
    (run rc s).regs 2 = s.regs 2 := by
  rfl

set_option maxRecDepth 4096 in
theorem regs_rsp_run (s : State) (rc : BitVec 64) :
    (run rc s).regs 4 = s.regs 4 := by
  rfl

end Sha3.Proofs.Permutation.RoundAlgebra
