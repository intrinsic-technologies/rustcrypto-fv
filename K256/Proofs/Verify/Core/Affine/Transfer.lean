import K256.Proofs.Verify.Transfer.Padding
import K256.Proofs.Generate.Serialize.Transfer.Relabel
import K256.Proofs.Verify.LIR.Program
import K256.Proofs.Generate.LIR.Program

namespace K256.Proofs.Verify.Core.Affine

open X86Proofs CFG Lift Generate.Serialize Verify.Transfer

private def target : Generate.LIR.Label → Option Verify.LIR.Label
  | .l100a20 => some .l100a20
  | .l1084e0 => some .l1084e0
  | .l108890 => some .l108890
  | .l1088a6 => some .l1088a6
  | .l1088b6 => some .l1088b6
  | .l1088bb => some .l1088bb
  | .l1088c3 => some .l1088c3
  | .l10893a => some .l10893a
  | .l108952 => some .l108952
  | .l10896a => some .l10896a
  | .l108980 => some .l108980
  | .l10899e => some .l10899e
  | .l1089b2 => some .l1089b2
  | .l108bb1 => some .l108bb1
  | .l108bc1 => some .l108bc1
  | .l108df9 => some .l108df9
  | .l108e11 => some .l108e11
  | .l108e27 => some .l108e27
  | .l108e30 => some .l108e30
  | .l108f80 => some .l108f80
  | .l108f97 => some .l108f97
  | .l108fe2 => some .l108fe2
  | .l109036 => some .l109036
  | .l109107 => some .l109107
  | .l10914e => some .l10914e
  | .l1091e4 => some .l1091e4
  | .l109246 => some .l109246
  | .l1092a0 => some .l1092a0
  | .l1093f9 => some .l1093f9
  | .l1093fe => some .l1093fe
  | .l109448 => some .l109448
  | .l109c00 => some .l109c00
  | .l10e4c0 => some .l10e4c0
  | .l10ecb2 => some .l10ecb2
  | .l10ecc3 => some .l10ecc3
  | .l10ece0 => some .l10ece0
  | .l10ed05 => some .l10ed05
  | .l10ed84 => some .l10ed84
  | .l10eda1 => some .l10eda1
  | .l10ee37 => some .l10ee37
  | .l10ee65 => some .l10ee65
  | .l10fe50 => some .l10fe50
  | .l114930 => some .l114930
  | .l114a10 => some .l114a10
  | .l120470 => some .l120470
  | .l127d50 => some .l127d50
  | .l129560 => some .l129560
  | .l129594 => some .l129594
  | .l1295a0 => some .l1295a0
  | .l1295f2 => some .l1295f2
  | .l12962f => some .l12962f
  | .l12965d => some .l12965d
  | .l1296a9 => some .l1296a9
  | .l1296eb => some .l1296eb
  | .l12974b => some .l12974b
  | .l129762 => some .l129762
  | .l129770 => some .l129770
  | .l12979c => some .l12979c
  | .l1297a0 => some .l1297a0
  | .l1297b6 => some .l1297b6
  | .l1297bb => some .l1297bb
  | .l1297c6 => some .l1297c6
  | .l1297cf => some .l1297cf
  | .l1297d8 => some .l1297d8
  | .l1297eb => some .l1297eb
  | .l1297f3 => some .l1297f3
  | .l12980a => some .l12980a
  | .l129815 => some .l129815
  | .l129818 => some .l129818
  | .l129820 => some .l129820
  | .l129860 => some .l129860
  | .l129865 => some .l129865
  | .l129870 => some .l129870
  | .l129885 => some .l129885
  | .l129886 => some .l129886
  | .l1298a0 => some .l1298a0
  | .l1298e6 => some .l1298e6
  | .l1298eb => some .l1298eb
  | .l129900 => some .l129900
  | .l129915 => some .l129915
  | .l129921 => some .l129921
  | .l12993c => some .l12993c
  | .l129950 => some .l129950
  | .l129964 => some .l129964
  | .l129978 => some .l129978
  | .l12998c => some .l12998c
  | .l1299a0 => some .l1299a0
  | .l1299b0 => some .l1299b0
  | .l1299b2 => some .l1299b2
  | .l1299e0 => some .l1299e0
  | .l1299e3 => some .l1299e3
  | .l129a14 => some .l129a14
  | .l129a1d => some .l129a1d
  | .l129a45 => some .l129a45
  | .l129a50 => some .l129a50
  | .l129ac4 => some .l129ac4
  | .l129ac9 => some .l129ac9
  | .l129af1 => some .l129af1
  | .l129b13 => some .l129b13
  | .l129b2f => some .l129b2f
  | .l129b4a => some .l129b4a
  | _ => none

private def padding : Verify.LIR.Label → Option (Padding.Site Op Verify.LIR.Label Reg.count)
  | .l12962f => some ⟨(.exec 0x12962f (fun s => s.RIP = 0x12962f) (fun _ => nopEffect 0x12962f 1) (Reg.operands [] [])), .l129630,
      RegMap.args [(1, 1), (2, 2), (4, 4), (5, 5), (6, 6), (7, 7)] 54⟩
  | .l12974b => some ⟨(.exec 0x12974b (fun s => s.RIP = 0x12974b) (fun _ => nopEffect 0x12974b 5) (Reg.operands [] [])), .l129750,
      RegMap.args [(2, 2), (4, 4), (5, 5), (6, 6), (7, 7)] 54⟩
  | _ => none

private theorem paddingPrefix (l : Verify.LIR.Label) (s : Padding.Site Op Verify.LIR.Label Reg.count)
    (h : padding l = some s) : Verify.LIR.program.blocks l = s.prefix := by
  unfold padding at h
  split at h <;> cases h <;> rfl

set_option maxRecDepth 8192 in
set_option maxHeartbeats 6000000 in
private theorem blocks (a : Generate.LIR.Label) (b : Verify.LIR.Label) (h : target a = some b) :
    Relabel.block target (Generate.LIR.program.blocks a) =
      Relabel.block some ((Padding.join Verify.LIR.program padding).blocks b) := by
  cases a <;> rename_i l <;> cases l <;> cases h <;> with_unfolding_all rfl

theorem transferAt {V S : Type} {d : Dialect Op V S}
    {a : Values V Reg.count} {m : S} {o : Output V S Reg.count}
    {src : Generate.LIR.Label} {dst : Verify.LIR.Label} (pair : target src = some dst)
    (run : Generate.LIR.program.Exec d ⟨⟨src,a,m⟩,[]⟩ o) :
    Verify.LIR.program.Exec d ⟨⟨dst,a,m⟩,[]⟩ o := by
  apply Padding.exec paddingPrefix
  apply Relabel.exec blocks run
  simp only [Relabel.state, Relabel.location, pair, List.map_nil]

theorem transfer {V S : Type} {d : Dialect Op V S}
    {a : Values V Reg.count} {m : S} {o : Output V S Reg.count}
    (run : Generate.LIR.program.Exec d ⟨⟨.l10fe50,a,m⟩,[]⟩ o) :
    Verify.LIR.program.Exec d ⟨⟨.l10fe50,a,m⟩,[]⟩ o := transferAt rfl run

end K256.Proofs.Verify.Core.Affine
