import K256.Proofs.Verify.Transfer.Padding
import K256.Proofs.Generate.Serialize.Transfer.Relabel
import K256.Proofs.Generate.LIR.Program
import K256.Proofs.Verify.LIR.Program

namespace K256.Proofs.Signing.Transfer.Generator

open Lean Elab Tactic X86Proofs CFG Lift Generate.Serialize Verify.Transfer

local elab "generator_target" : tactic => do
  let name := (← (← getMainGoal).getTag).getString!
  let ranges := [("l100a20", "l100a20"), ("l1084e0", "l109c00"), ("l10a410", "l1145f0"),
    ("l114930", "l120470"), ("l127d50", "l127d50"), ("l129560", "l129b4a"), ("l12a820", "l12a820")]
  if ranges.any fun (lo, hi) => lo ≤ name && name ≤ hi then
    let target := mkIdent (Name.str ``Verify.LIR.Label name)
    evalTactic (← `(tactic| exact some $target))
  else
    evalTactic (← `(tactic| exact none))

def target : Generate.LIR.Label → Option Verify.LIR.Label := by
  intro a
  cases a <;> rename_i l <;> cases l <;> generator_target

def sites : Verify.LIR.Label → Option (Padding.Site Op Verify.LIR.Label Reg.count)
  | .l11f77b => some ⟨(.exec 0x11f77b (fun s => s.RIP = 0x11f77b) (fun _ => nopEffect 0x11f77b 5) (Reg.operands [] [])), .l11f780,
      RegMap.args [(2, 2), (3, 3), (4, 4), (5, 5), (6, 6), (7, 7), (10, 10), (11, 11), (12, 12), (13, 13), (14, 14), (15, 15), (22, 22), (39, 39), (50, 50), (51, 51)] 54⟩
  | .l12962f => some ⟨(.exec 0x12962f (fun s => s.RIP = 0x12962f) (fun _ => nopEffect 0x12962f 1) (Reg.operands [] [])), .l129630,
      RegMap.args [(1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7)] 54⟩
  | .l12974b => some ⟨(.exec 0x12974b (fun s => s.RIP = 0x12974b) (fun _ => nopEffect 0x12974b 5) (Reg.operands [] [])), .l129750,
      RegMap.args [(2, 2), (4, 4), (5, 5), (6, 6), (7, 7)] 54⟩
  | _ => none

theorem paddingPrefix (l : Verify.LIR.Label) (s : Padding.Site Op Verify.LIR.Label Reg.count)
    (h : sites l = some s) : Verify.LIR.program.blocks l = s.prefix := by
  unfold sites at h
  split at h <;> cases h <;> rfl

abbrev Matches (a : Generate.LIR.Label) (b : Verify.LIR.Label) :=
  Relabel.block target (Generate.LIR.program.blocks a) =
    Relabel.block some ((Padding.join Verify.LIR.program sites).blocks b)

end K256.Proofs.Signing.Transfer.Generator
