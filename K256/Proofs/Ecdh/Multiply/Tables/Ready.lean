import K256.Proofs.Ecdh.Multiply.Tables.Export

namespace K256.Proofs.Generate.Generator.Multiply.Prepare.Table

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR

local macro "peer_outside_copy" e:ident : tactic =>
  `(tactic| (dsimp only [exportWrites,copyDst,copySrc,ite_true,ite_false,Bool.false_eq_true]; peer_acc_bounds using $e))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
theorem peerExportTables {fr : Activation} {initial a : Registers} {m : Ram} {d : Nat} {peer : Projective}
    (entry : PeerCoreEntry fr initial d peer) (s : State .l11d514 fr a m)
    (first : TableAt m (sp fr+2128) (peerFirstBase d peer)) (second : TableAt m (sp fr+1168) (peerSecondBase d peer))
    (ptr : memLoad m (sp fr+216) 64 = fr.rcx) (mag : Magnitudes fr m d)
    (extra : Locals fr m [(0x60,66),(0x88,152),(0xc0,0)])
    (r12 : a[12] = ⟨64,sp fr+296⟩) (r13 : a[13] = ⟨64,sp fr+1168⟩)
    (r14 : a[14] = ⟨64,0⟩) (r15 : a[15] = ⟨64,sp fr+464⟩) :
    ∃ b n, Reaches .l11d514 a m .l11d546 b n ∧ PeerTablesReady fr b n d peer := by
  obtain ⟨b,n,r,sb,t1,f,fn1,tab1,saved⟩ := peerExportOne true entry s first ptr (by simp) (by simp) (by simp)
  obtain ⟨c,o,r',sc,t2,g,_,tab2,kept⟩ := peerExportOne false entry sb (second.of_frame f (by peer_outside_copy entry))
    ((f.memLoad_eq (by peer_outside_copy entry)).trans ptr) (fun _ => fn1) (fun _ => tab1)
    (fun _ => congrArg (Value.get 64) ((saved 13 (by decide)).trans r13))
  refine ⟨c,o,r.trans r',sc,⟨?_,?_⟩,⟨t1.of_frame g (by peer_outside_copy entry),t2⟩,?_,
    (kept 14 (by decide)).trans ((saved 14 (by decide)).trans r14),tab2,
    (kept 12 (by decide)).trans ((saved 12 (by decide)).trans r12),
    (kept 15 (by decide)).trans ((saved 15 (by decide)).trans r15)⟩
  · exact WordsAt.of_frame (WordsAt.of_frame mag.first f (by decide) (by peer_outside_copy entry)) g (by decide) (by peer_outside_copy entry)
  · exact WordsAt.of_frame (WordsAt.of_frame mag.second f (by decide) (by peer_outside_copy entry)) g (by decide) (by peer_outside_copy entry)
  · apply Locals.of_frame (Locals.of_frame extra f ?_) g
    all_goals
      intro kv hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl|rfl|rfl <;> peer_outside_copy entry

end K256.Proofs.Generate.Generator.Multiply.Prepare.Table
