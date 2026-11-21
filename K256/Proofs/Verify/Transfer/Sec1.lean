import K256.Proofs.Verify.Transfer.Padding
import K256.Proofs.Generate.Serialize.Transfer.Relabel
import K256.Proofs.Verify.LIR.Program
import K256.Proofs.Sec1.LIR.Program

namespace K256.Proofs.Verify.Transfer

open Lean Elab Tactic X86Proofs CFG Lift Generate.Serialize

local elab "sec1_target" : tactic => do
  let tag ← (← getMainGoal).getTag
  let target := mkIdent (Name.str ``LIR.Label tag.getString!)
  evalTactic (← `(tactic| exact some $target))

def sec1Target : Sec1.LIR.Label → Option LIR.Label := by
  intro a
  cases a <;> rename_i l <;> cases l <;> sec1_target

private def padding : LIR.Label → Option (Padding.Site Op LIR.Label Reg.count)
  | .l1065ac => some ⟨(.exec 0x1065ac (fun s => s.RIP = 0x1065ac) (fun _ => nopEffect 0x1065ac 4) (Reg.operands [] [])), .l1065b0,
      RegMap.args [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 54⟩
  | .l125788 => some ⟨(.exec 0x125788 (fun s => s.RIP = 0x125788) (fun _ => nopEffect 0x125788 8) (Reg.operands [] [])), .l125790,
      RegMap.args [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (8, 8), (9, 9), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 54⟩
  | .l12962f => some ⟨(.exec 0x12962f (fun s => s.RIP = 0x12962f) (fun _ => nopEffect 0x12962f 1) (Reg.operands [] [])), .l129630,
      RegMap.args [(1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7)] 54⟩
  | .l12974b => some ⟨(.exec 0x12974b (fun s => s.RIP = 0x12974b) (fun _ => nopEffect 0x12974b 5) (Reg.operands [] [])), .l129750,
      RegMap.args [(2, 2), (4, 4), (5, 5), (6, 6), (7, 7)] 54⟩
  | _ => none

private theorem paddingPrefix (l : LIR.Label) (s : Padding.Site Op LIR.Label Reg.count)
    (h : padding l = some s) : LIR.program.blocks l = s.prefix := by
  unfold padding at h
  split at h <;> cases h <;> rfl

set_option maxRecDepth 4096 in
set_option maxHeartbeats 3000000 in
private theorem sec1Blocks (a : Sec1.LIR.Label) (b : LIR.Label) (h : sec1Target a = some b) :
    Relabel.block sec1Target (Sec1.LIR.program.blocks a) =
      Relabel.block some ((Padding.join LIR.program padding).blocks b) := by
  cases a <;> rename_i l <;> cases l <;> cases h <;> with_unfolding_all rfl

theorem sec1Exec {V S : Type} {d : Dialect Op V S} {src : Sec1.LIR.Label} {dst : LIR.Label}
    (label : sec1Target src = some dst)
    {a : Values V Reg.count} {m : S} {o : Output V S Reg.count}
    (run : Sec1.LIR.program.Exec d ⟨⟨src,a,m⟩,[]⟩ o) :
    LIR.program.Exec d ⟨⟨dst,a,m⟩,[]⟩ o := by
  apply Padding.exec paddingPrefix
  apply Relabel.exec sec1Blocks run
  simp only [Relabel.state, Relabel.location, label, List.map_nil]

end K256.Proofs.Verify.Transfer
