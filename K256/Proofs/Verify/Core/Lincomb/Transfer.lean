import K256.Proofs.Generate.Serialize.Transfer.Relabel
import K256.Proofs.Generate.LIR.Program
import K256.Proofs.Verify.LIR.Program

namespace K256.Proofs.Verify.Core.Lincomb

open Generate.Serialize X86.Machine X86.UserProcess X86Proofs CFG Lift
open Lean Elab Tactic

def sharedEntry : List (Generate.LIR.Label × LIR.Label) :=
  [(.l1099c0, .l1099c0),
   (.l109be7, .l109be7),
   (.l10a410, .l10a410),
   (.l10e010, .l10e010),
   (.l1109b0, .l1109b0),
   (.l110b80, .l110b80),
   (.l1145f0, .l1145f0),
   (.l11b510, .l11b510),
   (.l11b53b, .l11b53b),
   (.l11b5a3, .l11b5a3),
   (.l11b5ba, .l11b5ba),
   (.l11b864, .l11b864),
   (.l11b874, .l11b874),
   (.l11b880, .l11b880),
   (.l11b88c, .l11b88c),
   (.l11b8f0, .l11b8f0),
   (.l11badf, .l11badf),
   (.l11bae7, .l11bae7),
   (.l127d50, .l127d50)]

private def target : Generate.LIR.Label → Option LIR.Label
  | .l1099c0 => some .l1099c0
  | .l109be7 => some .l109be7
  | .l10a410 => some .l10a410
  | .l10e010 => some .l10e010
  | .l1109b0 => some .l1109b0
  | .l110b80 => some .l110b80
  | .l1145f0 => some .l1145f0
  | .l11b510 => some .l11b510
  | .l11b53b => some .l11b53b
  | .l11b5a3 => some .l11b5a3
  | .l11b5ba => some .l11b5ba
  | .l11b864 => some .l11b864
  | .l11b874 => some .l11b874
  | .l11b880 => some .l11b880
  | .l11b88c => some .l11b88c
  | .l11b8f0 => some .l11b8f0
  | .l11badf => some .l11badf
  | .l11bae7 => some .l11bae7
  | .l127d50 => some .l127d50
  | _ => none

local elab "transfer_chunks " label:ident " through " last:num : tactic => do
  let h := mkIdent `relabeled
  for offset in [:last.getNat + 1] do
    let i := last.getNat - offset
    let stem := label.getId.toString
    let name := if i = 0 then stem else stem ++ "_" ++ toString i
    let src := mkIdent (Name.str `K256.Proofs.Generate.LIR name)
    let dst := mkIdent (Name.str `K256.Proofs.Verify.LIR name)
    if offset = 0 then
      evalTactic (← `(tactic|
        have $h : Relabel.block target $src = Relabel.block some $dst := by rfl))
    else
      evalTactic (← `(tactic|
        have $h : Relabel.block target $src = Relabel.block some $dst := by
          simp only [$src:ident, $dst:ident, Relabel.block, $h:ident]))
  evalTactic (← `(tactic| exact $h))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 4000000 in
private theorem pointAddition :
    Relabel.block target Generate.LIR.b_l10a410 = Relabel.block some LIR.b_l10a410 := by
  transfer_chunks b_l10a410 through 171

set_option maxRecDepth 8192 in
private theorem sharedBlocks (a : Generate.LIR.Label) (b : LIR.Label) (h : target a = some b) :
    Relabel.block target (Generate.LIR.program.blocks a) = Relabel.block some (LIR.program.blocks b) := by
  unfold target at h
  split at h <;> cases h <;> first | exact pointAddition | rfl

theorem transfer {src : Generate.LIR.Label} {dst : LIR.Label} (entry : (src, dst) ∈ sharedEntry)
    {code : CodeMap} {a : Values Value Reg.count} {m : Ram} {out : Output Value Ram Reg.count}
    (run : Generate.LIR.program.Exec (dialect code) ⟨⟨src,a,m⟩,[]⟩ out) :
    LIR.program.Exec (dialect code) ⟨⟨dst,a,m⟩,[]⟩ out := by
  have mapping : target src = some dst := by
    simp only [sharedEntry, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at entry
    rcases entry with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> rfl
  exact Relabel.exec sharedBlocks run (by simp only [Relabel.state, Relabel.location, mapping, List.map_nil])

end K256.Proofs.Verify.Core.Lincomb
