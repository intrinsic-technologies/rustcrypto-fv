import K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.Loop
import K256.Proofs.Signing.Nonce.Initialize.Update.Absorb.Prefix.Second.Blocks

namespace K256.Proofs.Signing.Nonce.Initialize.Update

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Verify.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters Standards.NIST.SHA2

open Absorb Absorb.Prefix

private theorem secondJump {l k : Label} {a b : Verify.Core.Registers} {m n : Ram}
    (run : program.runBlock (dialect Extracted.programImage) ⟨l,a,m⟩ = .jump ⟨k,b,n⟩) :
    Verify.Core.Reaches l a m k b n := by
  apply Semantics.Reaches.single
  change (program.runBlock (dialect Extracted.programImage) _).next _ [] = _
  rw [run]
  rfl

local macro "second_regs" "[" xs:ident,* "]" : tactic =>
  `(tactic| simp only [branchRegisters, copiedRegisters, Vector.getElem_set,
    Nat.reduceEqDiff, ↓reduceIte, $[$xs:ident],*])

set_option maxHeartbeats 800000 in
theorem Absorb.appendSecondPrefix {fr : Activation} {input : Input} {state : State}
    {a : Verify.Core.Registers} {m : Ram} (env : Environment fr input)
    (roundOk : true = true → seeded input = true)
    (live : Live (appendAt true) fr a m state) (slots : true = true → Slots fr m)
    (buf : true = true → a[13] = ⟨64, sp fr + 392⟩)
    (ctx : UpdateV.HmacStateAt m (context fr true) state.key ByteArray.empty) :
    ∃ b n, Verify.Core.Reaches (appendAt true) a m (Absorb.afterPrefix true input) b n ∧
      Live (Absorb.afterPrefix true input) fr b n state ∧ (seeded input = true → Slots fr n) ∧
      (seeded input = true → Absorb.Cursor true fr b 0) ∧
      UpdateV.HmacStateAt n (context fr true) state.key (Absorb.taggedValue true state) := by
  obtain ⟨rsp,df,_,slice,mx,ft,fc,tail⟩ := live.atoms
  have rspv : a[4].get 64 = sp fr := congrArg (Value.get 64) rsp
  let src := fr.rdi + 32
  let b := branchRegisters a (sp fr)
  let c := copiedRegisters b m src (fr.rsi+48)
  let w₀ := RamWriteFrame.refl m (area fr 392 456)
  let copied := copiedMemory m (sp fr) (sp fr+392) src
  let marked := memStore copied (sp fr+424) (1 : BitVec 8)
  let n := taggedMemory m (context fr true) src 1
  have markAddr : context fr true + 127 = sp fr + 455 := by
    change sp fr + 328 + 127 = _
    bv_omega
  have bufferAddr : context fr true + 64 = sp fr + 392 := by
    change sp fr + 328 + 64 = _
    bv_omega
  have getUsed : memLoad m (sp fr+455) 8 = 0 := by
    rw [← markAddr]
    exact ctx.used
  have rdAt (i k : Nat) (h : i+k ≤ 712) :
      LoadOk m (sp fr + BitVec.ofNat 64 i) k := by
    have r := (Prefix.stackWritable env live w₀ i k h).readable
    exact ⟨r.low,r.present⟩
  have start := secondBranch rspv (rdAt 455 1 (by decide)) getUsed
  have wc : RamWriteFrame m copied (area fr 392 456) :=
    stackStore (i := 455) env (storedFrame (off := 392) env w₀ src (by decide) (by decide) (by decide))
      (32 : BitVec 8) (by decide) (by decide) (by decide)
  have wm : RamWriteFrame m marked (area fr 392 456) :=
    stackStore (i := 424) env wc (1 : BitVec 8) (by decide) (by decide) (by decide)
  have wn : RamWriteFrame m n (area fr 392 456) :=
    taggedFrame (off := 328) env w₀ src 1 (by decide) (by decide) (by decide)
  have stopRead : LoadOk copied (sp fr+8) 8 := by
    have r := (Prefix.stackWritable env live wc 8 8 (by decide)).readable
    exact ⟨r.low,r.present⟩
  have stopEq : memLoad copied (sp fr+8) 64 = fr.rsi+48 :=
    (wc.memLoad_eq (stackOutside (i := 8) env (by decide) (by decide) (by decide))).trans
      (slots rfl).stop
  have copy := secondCopy (a := b) (s := sp fr) (m := m) (src := src) (dst := sp fr+392)
    (by second_regs [b]; exact rspv) (by second_regs [b]; rfl)
    (by second_regs [b]; exact congrArg (Value.get 64) (buf rfl))
    (rdAt 112 8 (by decide)) (slots rfl).value (wordAccess env live w₀ 392 (by decide))
    stopRead stopEq
  have wtag := ParseSignature.storeOk_of_codeRange (off := 0) (len := 8)
    (Prefix.stackWritable env live wc 424 1 (by decide))
    (fun x hx => Common.fnCode_subset_programImage x (code_l1045d5 x hx)) (by decide)
  have wused := ParseSignature.storeOk_of_codeRange (off := 0) (len := 7)
    (Prefix.stackWritable env live wm 455 1 (by decide))
    (fun x hx => Common.fnCode_subset_programImage x (code_l1047c4 x hx)) (by decide)
  have rsC : c[4].get 64 = sp fr := by second_regs [c,b]; exact rspv
  have tagStep := secondTag (a := c) rsC (by second_regs [c]; rfl) wtag
  have usedStep := secondUsed (a := c.set 0 ⟨64,33⟩)
    (by second_regs []; exact rsC) (by second_regs []; rfl) wused
  have nEq : memStore marked (sp fr+455) (33 : BitVec 8) = n := by
    simp only [n,marked,copied,copiedMemory,taggedMemory,context,ite_true,
      BitVec.add_assoc,BitVec.reduceAdd]
    rfl
  rw [nEq] at usedStep
  have finish : afterPrefix true input = .l1047fb := by
    simp only [afterPrefix,roundOk rfl,ite_true,loopAt]
  rw [finish]
  let d := c.set 0 ⟨64,33⟩
  refine ⟨d, n,
    (((secondJump start).trans (secondJump copy)).trans (secondJump tagStep)).trans (secondJump usedStep),
    ?_, ?_, ?_, ?_⟩
  · have loc := areaLocal (lo := 392) (hi := 456) env (by decide) (by decide)
    apply liveAfter env live wn loc
    · exact ⟨(show d[4] = a[4] by second_regs [d,c,b]).trans rsp,
        (show d[22] = a[22] by second_regs [d,c,b]).trans df,
        (show d[39] = a[39] by second_regs [d,c,b]).trans mx,
        (show d[50] = a[50] by second_regs [d,c,b]).trans ft,
        (show d[51] = a[51] by second_regs [d,c,b]).trans fc,
        frameTailAfter env (show FrameTail fr a m from tail) wn loc⟩
    · intro i h
      have old := live.savedWidths i h
      change (c.set 0 ⟨64,33⟩)[i.val].width = 64
      rcases i with ⟨i,hi⟩
      simp only [Activation.calleeSavedNumbers,List.mem_cons,List.not_mem_nil,or_false] at h
      rcases h with rfl|rfl|rfl|rfl|rfl|rfl <;> second_regs [c,b] <;>
        first | rfl | exact old
    · intro h; cases h
  · intro _
    exact slotsAfter (slots rfl) wn (stackOutside (i := 8) env (by decide) (by decide) (by decide))
      (stackOutside (i := 112) env (by decide) (by decide) (by decide))
      (stackOutside (i := 120) env (by decide) (by decide) (by decide))
  · intro _
    refine ⟨?_, ?_, ?_, ?_⟩
    · change (c.set 0 ⟨64,33⟩)[13] = ⟨64,context fr true+64⟩
      rw [bufferAddr]
      second_regs [c,b]
      exact buf rfl
    · change (c.set 0 ⟨64,33⟩)[14] = ⟨64,fr.rsi+0⟩
      rw [show fr.rsi + 0 = fr.rsi from BitVec.add_zero _]
      second_regs [c,b]
      exact slice
    · intro _
      change (c.set 0 ⟨64,33⟩)[5] = ⟨64,context fr true+128⟩
      rw [show context fr true + 128 = sp fr + 456 by change sp fr+328+128 = _; bv_omega]
      second_regs [c,b]
    · intro _
      second_regs [d,c]
  · have bytes : (⟨src.toNat,32⟩ : MemoryRegion).HasBytes m state.value := by
      rw [show src.toNat = fr.rdi.toNat + 32 from valueNat env]
      exact live.bytes.value
    exact taggedState 1 ctx bytes (by rw [bufferAddr]; exact (Prefix.stackWritable env live w₀ 392 32 (by decide)).readable)

end K256.Proofs.Signing.Nonce.Initialize.Update
