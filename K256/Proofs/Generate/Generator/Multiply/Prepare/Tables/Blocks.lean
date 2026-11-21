import K256.Proofs.Generate.Generator.Multiply.Prepare.State
import K256.Proofs.Generate.Generator.Multiply.Prepare.Copy
import K256.Proofs.Generate.Generator.Entry

namespace K256.Proofs.Generate.Generator.Multiply.Prepare.Table

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Tactic K256.Proofs.Generate.LIR

def site (first : Bool) (i : Fin 8) : Label :=
  (if first then
    #v[.l11cf0d,.l11cf51,.l11cfae,.l11d003,.l11d058,.l11d0ad,.l11d102,.l11d157]
  else
    #v[.l11d2e1,.l11d31e,.l11d371,.l11d3bc,.l11d407,.l11d452,.l11d49d,.l11d4e8])[i]

abbrev offset (first : Bool) : BitVec 64 := if first then 0x850 else 0x490
abbrev baseOffset (first : Bool) : BitVec 64 := if first then 0x328 else 0xc10

def copyOperands (first : Bool) (i : Nat) (q : BitVec 64) (m : Ram) : Ram :=
  let base := q + baseOffset first
  let prev := q + BitVec.ofNat 64 ((if first then 0x850 else 0x490) + 120*i)
  let stage := if i = 0 then memCopy m prev base 120 else
    memCopy (memCopy m (q+0x418) (q+0x1d0) 120) prev (q+0x418) 120
  memCopy (memCopy stage (q+0x128) (if i = 0 then base else prev) 120) (q+0x1d0) base 120

def savedReg (first : Bool) (i : Nat) (q : BitVec 64) (a : Registers) (r : Fin Reg.count) : Value :=
  if !first && i == 0 && r.val == 13 then ⟨64,q+0x490⟩
  else if i == 1 && r.val == (if first then 13 else 5) then ⟨64,q+0x418⟩
  else a[r]

structure Inputs (first : Bool) (i : Nat) (q : BitVec 64) (a : Registers) : Prop where
  rsp : a[4].get 64 = q
  df : a[22].get 1 = 0
  base : (if first then a[5] else a[3]).get 64 = q + baseOffset first
  work : a[15].get 64 = q+0x1d0
  src : first = false → a[12].get 64 = q+0x128
  temp : 2 ≤ i → (if first then a[13] else a[5]).get 64 = q+0x418

structure Block (first : Bool) (i : Fin 7) (q : BitVec 64) (a b : Registers) (m : Ram) : Prop where
  run : let resume := site first i.succ
        program.runBlock (dialect Extracted.programImage) ⟨site first i.castSucc,a,m⟩ =
          .call ⟨.l10a410,b,memStore (copyOperands first i q m) (q-8) (address resume)⟩
            (callFrame resume (address resume))
  rsp : b[4] = ⟨64,q-8⟩
  dst : b[7].get 64 = q+0x1d0
  src : b[6].get 64 = q+0x128
  widths : ParseSignature.ArgumentWidths b
  saved : ∀ r : Fin Reg.count, r.val ∈ Activation.calleeSavedNumbers → b[r] = savedReg first i q a r
  ctrl : ∀ r : Fin Reg.count, r.val ∈ [22,39,50,51] → b[r] = a[r]


def BlockFor (first : Bool) (i : Fin 7) : Prop :=
  ∀ (a : Registers) (m : Ram) (q : BitVec 64),
    Writable Extracted.programImage m (q-544) 3800 → 544 ≤ q.toNat →
    q.toNat + 3256 < 2^32 → ParseSignature.ArgumentWidths a →
    Inputs first i q a → ∃ b, Block first i q a b m

local macro "table_block " first:term:max i:num start:term:max resume:term:max code:term:max
    : tactic =>
  `(tactic| (
  intro a m q win room high w inputs
  have win0 : Writable Extracted.programImage m q 3256 := by
    apply win.sub
    all_goals rw [BitVec.toNat_sub_of_le (by exact room)]; simp only [BitVec.reduceToNat]; omega
  obtain ⟨rsp, df, base, work, src, temp⟩ := inputs
  first | change a[5].get 64 = q + 0x328 at base | change a[3].get 64 = q + 0xc10 at base
  first | have srcPtr : a[12].get 64 = q+0x128 := src rfl | have srcPtr : True := trivial
  first
    | have tmpPtr : a[13].get 64 = q+0x418 := temp (by decide)
    | have tmpPtr : a[5].get 64 = q+0x418 := temp (by decide)
    | have tmpPtr : True := trivial
  refine ⟨?b, ?run, ?rsp, ?dst, ?src, ?widths, ?saved, ?ctrl⟩
  case run =>
    change program.runBlock (dialect Extracted.programImage) ⟨$start,a,m⟩ =
      .call ⟨.l10a410,?b,memStore (copyOperands $first $i q m) (q-8) (address $resume)⟩ (callFrame $resume (address $resume))
    arithmetic_segment using $code [rsp,df,base,work,srcPtr,tmpPtr]
    repeat' (refine Eq.trans (ite_eq_left ?_) ?_; first | rep_copy_guard using $code | (dsimp only [memCopy]; slot_guard using $code))
    rfl
  case rsp => rfl
  case dst => first | rfl | exact work
  case src => first | rfl | exact srcPtr
  case widths =>
    intro ⟨j,hj⟩ hj'
    have ww := w ⟨j,hj⟩ hj'
    simp only [Activation.argumentNumbers,List.mem_cons,List.not_mem_nil,or_false] at hj'
    rcases hj' with h|h|h|h|h|h <;> subst j <;> first | rfl | exact ww
  case saved =>
    intro ⟨j,hj⟩ hj'
    simp only [Activation.calleeSavedNumbers,List.mem_cons,List.not_mem_nil,or_false] at hj'
    rcases hj' with h|h|h|h|h|h <;> subst j <;> rfl
  case ctrl =>
    intro ⟨j,hj⟩ hj'
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hj'
    rcases hj' with h|h|h|h <;> subst j <;> rfl))

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem block_11cf0d : BlockFor true 0 := by
  table_block true 0 .l11cf0d .l11cf51 code_l11cf0d

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem block_11cf51 : BlockFor true 1 := by
  table_block true 1 .l11cf51 .l11cfae code_l11cf51

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem block_11cfae : BlockFor true 2 := by
  table_block true 2 .l11cfae .l11d003 code_l11cfae

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem block_11d003 : BlockFor true 3 := by
  table_block true 3 .l11d003 .l11d058 code_l11d003

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem block_11d058 : BlockFor true 4 := by
  table_block true 4 .l11d058 .l11d0ad code_l11d058

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem block_11d0ad : BlockFor true 5 := by
  table_block true 5 .l11d0ad .l11d102 code_l11d0ad

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem block_11d102 : BlockFor true 6 := by
  table_block true 6 .l11d102 .l11d157 code_l11d102

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem block_11d2e1 : BlockFor false 0 := by
  table_block false 0 .l11d2e1 .l11d31e code_l11d2e1

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem block_11d31e : BlockFor false 1 := by
  table_block false 1 .l11d31e .l11d371 code_l11d31e

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem block_11d371 : BlockFor false 2 := by
  table_block false 2 .l11d371 .l11d3bc code_l11d371

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem block_11d3bc : BlockFor false 3 := by
  table_block false 3 .l11d3bc .l11d407 code_l11d3bc

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem block_11d407 : BlockFor false 4 := by
  table_block false 4 .l11d407 .l11d452 code_l11d407

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem block_11d452 : BlockFor false 5 := by
  table_block false 5 .l11d452 .l11d49d code_l11d452

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
private theorem block_11d49d : BlockFor false 6 := by
  table_block false 6 .l11d49d .l11d4e8 code_l11d49d

theorem blockFor (first : Bool) (i : Fin 7) : BlockFor first i := by
  cases first <;> finite_cases i
  · exact block_11d2e1
  · exact block_11d31e
  · exact block_11d371
  · exact block_11d3bc
  · exact block_11d407
  · exact block_11d452
  · exact block_11d49d
  · exact block_11cf0d
  · exact block_11cf51
  · exact block_11cfae
  · exact block_11d003
  · exact block_11d058
  · exact block_11d0ad
  · exact block_11d102

end K256.Proofs.Generate.Generator.Multiply.Prepare.Table
