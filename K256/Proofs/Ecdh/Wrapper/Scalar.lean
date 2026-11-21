import K256.Proofs.Ecdh.Wrapper.State
import K256.Proofs.Ecdh.Scalar.Entry
import K256.Proofs.Ecdh.Scalar.Selection
import K256.Proofs.Ecdh.Scalar.Finish
import K256.Proofs.Ecdh.Scalar.Value
import K256.Proofs.Ecdh.Transfer

namespace K256.Proofs.Ecdh.Wrapper

open K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  K256.Proofs.CFG K256.Proofs.Lift K256.Proofs.Refine Ecdh.LIR
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1

open Scalar

local macro "entry_register" : tactic =>
  `(tactic| (simp only [entryArgs, parserArgs, Vector.getElem_set,
    ↓reduceIte, Lifted.locationOf, Vector.getElem_ofFn] <;> first | rfl | exact Reg.read_df_iff.mpr (by assumption)))

set_option maxHeartbeats 800000 in
set_option maxRecDepth 4096 in
theorem scalarPrefix {s : RamState} {secret key : ByteArray} (call : ValidCall ecdhDiffieHellman s [secret, key]) :
    ∃ d a m, (program.sem (dialect Extracted.programImage)).Reaches
      ⟨lifted.locationOf .l101660 s, []⟩ ⟨⟨.l1017b1, a, m⟩, []⟩ ∧
      Keys.decodeSecret domain secret = some d ∧ 0 < d ∧ d < domain.n ∧
      Caller s a m ∧ a[14] = ⟨64, s.regValue .rdx⟩ ∧ ScalarAt s m 0xc0 d := by
  let w := Common.scalarWord s.external (s.regValue .rsi)
  let d := Generate.Sampling.limbsValue (w 0) (w 1) (w 2) (w 3)
  let sp := localSp s
  obtain ⟨decoded, flag, nz, limbs⟩ := acceptedSecret call
  have bounds : 0 < d ∧ d < domain.n := by
    change Keys.decodeSecret domain secret = some d at decoded
    dsimp only [Keys.decodeSecret] at decoded
    split at decoded
    · rename_i h
      simp only [Bool.and_eq_true, decide_eq_true_eq] at h
      exact Option.some.inj decoded ▸ And.intro h.1.2 h.2
    · contradiction
  obtain ⟨room, limit, base⟩ := stack_geometry call
  change sp.toNat = _ at base
  let fr := childActivation s (entryMemory s) (entryArgs s) 65 0x1016be
  have pre : ChildRegisters s (entryArgs s) := by
    have df := call.directionFlagUnset
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    case refine_1 => change (entryArgs s)[(4 : Nat)] = _; entry_register
    case refine_2 => change (entryArgs s)[(22 : Nat)] = _; entry_register
    case refine_4 => change (entryArgs s)[(39 : Nat)].width = _; entry_register
    case refine_5 => change (entryArgs s)[(50 : Nat)].width = _; entry_register
    case refine_6 => change (entryArgs s)[(51 : Nat)].width = _; entry_register
    intro ⟨i,hi⟩ h
    change (entryArgs s)[i].width = 64
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> entry_register
  have mem : Memory s (entryMemory s) := ⟨entryMemory_frame call, entryMemory_saved s⟩
  obtain ⟨_,_,_,_,_,_,_,q3,q2,q1,q0,ret⟩ := entryMemory_load s
  have atoms := childEntry call mem.frame pre Generate.LIR.Fn109e60.frameInfo rfl (by decide)
    (by decide) (by decide +kernel) ret
  have v6 : (entryArgs s)[(6 : Nat)] = ⟨64,stackPtr s - 6064⟩ := by entry_register
  have si : fr.rsi = sp + 88 := by
    simp only [fr, childActivation, v6]
    change stackPtr s - 6064 = stackPtr s - 6152 + 88
    bv_omega
  have v7 : (entryArgs s)[(7 : Nat)] = ⟨64,stackPtr s - 5808⟩ := by entry_register
  have di : fr.rdi = sp + 344 := by
    simp only [fr, childActivation, v7]
    change stackPtr s - 5808 = stackPtr s - 6152 + 344
    bv_omega
  have lo : fr.low.toNat = (stackPtr s).toNat - 6225 :=
    Common.stackOffset call.stackAvailable (off := 6225) (by decide)
  have top : fr.rsp.toNat = (stackPtr s).toNat - 6160 :=
    Common.stackOffset call.stackAvailable (off := 6160) (by decide)
  have aw {a : BitVec 64} {k : Nat} (h : a = sp + 88 ∧ k = 32 ∨ a = sp + 344 ∧ k = 33) :
      Outside [ParseSignature.callStack fr] a k := by
    simp only [Outside, List.mem_singleton, forall_eq, ParseSignature.callStack, lo, top]
    rcases h with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩
    all_goals constructor
    all_goals first | right; bv_omega | bv_omega
  have win := mem.window call
  obtain ⟨out, run, tag, done_, writes, widths, words, bit⟩ := Generate.Generator.Sample.decodeScalar fr
    (by rw [si]; exact win.readable.of_offsets rfl (addr_sub _ _) (by decide))
    (by rw [di]; exact win.of_offsets rfl (addr_sub _ _) (by decide))
    (aw (.inl ⟨si,rfl⟩)) (aw (.inr ⟨di,rfl⟩)) _ atoms
  have reach := resumeCall (entry call) (Ecdh.Transfer.generateExec (by decide) rfl run) tag
  obtain ⟨rsp, keep⟩ := childReturn pre (win := 65) (ret := 0x1016be) done_
  have regs : Registers s out.values := by
    refine ⟨rsp, widths, ?_, (keep 3 (by decide)).trans ?_, (keep 14 (by decide)).trans ?_,
      (keep 13 (by decide)).trans ?_, (keep 22 (by decide)).trans pre.df,
      (keep 39 (by decide)).trans ?_, (keep 50 (by decide)).trans ?_, (keep 51 (by decide)).trans ?_⟩
    case refine_2 => change (entryArgs s)[(3 : Nat)] = _; entry_register
    case refine_3 => change (entryArgs s)[(14 : Nat)] = _; entry_register
    case refine_4 => change (entryArgs s)[(13 : Nat)] = _; entry_register
    case refine_5 => change (entryArgs s)[(39 : Nat)] = _; entry_register
    case refine_6 => change (entryArgs s)[(50 : Nat)] = _; entry_register
    case refine_7 => change (entryArgs s)[(51 : Nat)] = _; entry_register
    intro i hi
    exact (congrArg Value.width (keep i (by
      simp only [Generate.Generator.Sample.nonzeroPreserved, Activation.calleeSavedNumbers,
        List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
      grind))).trans (pre.gp i (by
      simp only [Activation.calleeSavedNumbers, List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
      grind))
  have nowMem : Memory s out.store := by
    apply mem.advance call writes
    intro r hr
    rcases List.mem_cons.mp hr with rfl | hr
    · simp only [Activation.region, lo, top]; omega
    · obtain rfl := List.mem_singleton.mp hr
      simp only [di]
      bv_omega
  have eqw (i : Nat) (hi : i < 4) : Common.scalarWord fr.original fr.rsi i = w i := by
    change Common.scalarWord (entryMemory s) fr.rsi i = _
    have rawsi : fr.rsi = stackPtr s - 6064 := by simp only [fr, childActivation, v6]; rfl
    rw [rawsi]
    rcases show i = 0 ∨ i = 1 ∨ i = 2 ∨ i = 3 by omega with rfl | rfl | rfl | rfl
    · change bswapSpec (memLoad (entryMemory s) (stackPtr s - 6064 + 24) 64) = _
      rw [show stackPtr s - 6064 + 24 = stackPtr s - 6040 by bv_omega, q3]
      rfl
    · change bswapSpec (memLoad (entryMemory s) (stackPtr s - 6064 + 16) 64) = _
      rw [show stackPtr s - 6064 + 16 = stackPtr s - 6048 by bv_omega, q2]
      rfl
    · change bswapSpec (memLoad (entryMemory s) (stackPtr s - 6064 + 8) 64) = _
      rw [show stackPtr s - 6064 + 8 = stackPtr s - 6056 by bv_omega, q1]
      rfl
    · change bswapSpec (memLoad (entryMemory s) (stackPtr s - 6064 + 0) 64) = _
      rw [show stackPtr s - 6064 + 0 = stackPtr s - 6064 by bv_omega, q0]
      simp only [w, Common.scalarWord, Nat.reduceSub, Nat.mul_zero, BitVec.add_zero]
  have wds : WordsAt out.store (sp + 344) 64 (Vector.ofFn fun i : Fin 4 => w i.val) := by
    rw [← di]
    intro i hi
    simpa only [Vector.getElem_ofFn] using (words i hi).trans (by simpa only [Vector.getElem_ofFn] using eqw i hi : _ = w i)
  have valid : memLoad out.store (sp + 376) 8 = 1 := by
    rw [di, show sp + 344 + 32 = sp + 376 by bv_omega,
      eqw 0 (by decide), eqw 1 (by decide), eqw 2 (by decide), eqw 3 (by decide)] at bit
    change Generate.Sampling.orderFlag (w 0) (w 1) (w 2) (w 3) = 1 at flag
    rw [flag] at bit
    exact bit.trans (by decide)
  have r15 : out.values[15] = ⟨64, sp + 344⟩ := by
    refine (keep 15 (by decide)).trans ?_
    have h : (entryArgs s)[(15 : Nat)] = ⟨64,stackPtr s - 5808⟩ := by entry_register
    exact h.trans (congrArg (Value.mk 64) (by change stackPtr s - 5808 = stackPtr s - 6152 + 344; bv_omega))
  obtain ⟨b,n,sel,br,bm,b12,b5,bw⟩ := selectPrefix call regs nowMem r15 wds valid
  let ca := compareArgs b sp
  let cm := prepareMemory n sp 0x1058 0x101752
  let cf := childActivation s cm ca 16 0x101752
  have prev (i : Fin Reg.count) (hi : i.val ∈ [3,5,13,14,22,39,50,51]) : ca[i] = b[i] := by
    obtain ⟨i, bound⟩ := i
    change ca[i] = b[i]
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [ca, compareArgs]
  have cpre : ChildRegisters s ca := childRegisters br (by simp [ca, compareArgs, sp]) (compareArgs_width sp) (fun i hi => prev i (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
    grind))
  obtain ⟨cmem, cret⟩ := stageMemory call bm 0x1058 0x101752 (.inr rfl)
  have catoms := childEntry call cmem.frame cpre Generate.LIR.Fn10a280.frameInfo rfl (by decide)
    (by decide) (by decide +kernel) cret
  have cwin := cmem.window call
  have cdi : cf.rdi = sp + 0xc98 := by
    have h : ca[(7 : Nat)] = ⟨64,sp + 0xc98⟩ := by simp [ca, compareArgs]
    change ca[(7 : Nat)].get 64 = _
    rw [h]
    rfl
  have csi : cf.rsi = sp + 0x1058 := by
    have h : ca[(6 : Nat)] = ⟨64,sp + 0x1058⟩ := by simp [ca, compareArgs]
    change ca[(6 : Nat)].get 64 = _
    rw [h]
    rfl
  have clo : cf.low.toNat = (stackPtr s).toNat - 6176 := Common.stackOffset call.stackAvailable (off := 6176) (by decide)
  have ctop : cf.rsp.toNat = (stackPtr s).toNat - 6160 := Common.stackOffset call.stackAvailable (off := 6160) (by decide)
  have apart {p : BitVec 64} (h : p = sp + 0xc98 ∨ p = sp + 0x1058) : Outside [cf.region] p 32 := by
    simp only [Outside, List.mem_singleton, forall_eq, Activation.region, clo, ctop]
    rcases h with rfl | rfl
    all_goals constructor
    all_goals first | right; bv_omega | bv_omega
  obtain ⟨c, crun, ctag, cdone, cwrites, cwidths, eq, val⟩ := Generate.Generator.Sample.compareFour cf
    (by rw [cdi]; exact cwin.readable.of_offsets rfl (addr_sub _ _) (by decide))
    (by rw [csi]; exact cwin.readable.of_offsets rfl (addr_sub _ _) (by decide))
    (apart (.inl cdi)) (apart (.inr csi)) _ catoms
  have bwin := bm.window call
  have code : ∀ x ∈ fnCode, x ∈ Extracted.programImage := Common.fnCode_subset_programImage
  have push := prepareCompare code (congrArg (Value.get 64) br.rsp) (congrArg (Value.get 64) b12)
    (bwin.of_offsets (addr_sub _ 8) (addr_sub _ 3936) (by decide))
  have cmp := resumeCall push (Ecdh.Transfer.generateExec (by decide) rfl crun) ctag
  obtain ⟨csp, kept⟩ := childReturn cpre (win := 16) (ret := 0x101752) cdone
  have cregs := returnedRegisters br cpre csp cwidths kept (fun i hi => prev i (by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
    grind))
  have cbp := (congrArg (Value.get 8) ((kept 5 (by decide)).trans (prev 5 (by decide)))).trans b5
  have src : WordsAt cm cf.rdi 64 (Vector.ofFn fun i : Fin 4 => w i.val) := by
    rw [cdi]
    apply preparedWords bw (bwin.of_offsets (addr_sub _ 8) (addr_sub _ 3936) (by decide))
    change Outside [⟨(sp - 8).toNat, 8⟩, ⟨(sp + 0x1058).toNat, 32⟩] (sp + 0xc98) 32
    simp only [Outside, List.mem_cons, List.not_mem_nil, or_false]
    constructor
    · bv_omega
    · intro r hr
      rcases hr with rfl | rfl <;> dsimp only <;> bv_omega
  have zero : WordsAt cm cf.rsi 64 (Vector.replicate 4 0) := by
    rw [csi]
    exact prepareMemory_words n sp 0x101752 (.inr rfl)
  have al : c.values[0].get 8 = 0 := by
    apply val.resolve_right
    intro h
    apply nz
    intro i hi
    simpa only [Vector.getElem_ofFn, Vector.getElem_replicate] using
      (src i hi).symm.trans ((eq.mp h i hi).trans (zero i hi))
  have after : Memory s c.store := cmem.advance call cwrites (by
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    simp only [Activation.region, clo, ctop]
    omega)
  have limbsAt := WordsAt.of_frame src cwrites (by decide) (apart (.inl cdi))
  rw [cdi] at limbsAt
  obtain ⟨v,m,finish,vsp,result,vwrites,stable,hcx,hdx⟩ := finishScalar (sp := sp) (congrArg (Value.get 64) csp)
    al cbp ((after.window call).of_offsets (addr_sub _ 9) (addr_sub _ 3936) (by decide)) limbsAt []
  have vm : Memory s m := after.advance call vwrites (by
    intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    rcases hr with rfl | rfl
    all_goals change _ ≤ _ ∧ _ ≤ _; dsimp only; bv_omega)
  refine ⟨d,v,m,reach.trans (sel.trans (cmp.trans finish)), decoded, bounds.1, bounds.2,
    ⟨vm, vsp, (stable 3 (by decide)).trans cregs.output, (stable 22 (by decide)).trans cregs.df, ?_,
    congrArg Value.width ((stable 39 (by decide)).trans cregs.mx),
    congrArg Value.width ((stable 50 (by decide)).trans cregs.ft),
    congrArg Value.width ((stable 51 (by decide)).trans cregs.fc)⟩,
    (stable 14 (by decide)).trans cregs.peer, ?_⟩
  · intro ⟨i,hi⟩ h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    all_goals first
      | exact hcx (cregs.args 1 (by decide))
      | exact hdx (cregs.args 2 (by decide))
      | exact (congrArg Value.width (stable _ (by decide +revert))).trans (cregs.savedWidths _ (by decide +revert))
      | exact (congrArg Value.width (stable _ (by decide +revert))).trans (cregs.args _ (by decide +revert))
  · change WordsAt m (sp + 0xc0) 64 (Generate.Generator.Multiply.scalarWords d)
    change (Vector.ofFn fun i : Fin 4 => w i.val) = Generate.Generator.Multiply.scalarWords d at limbs
    rw [← limbs]
    exact result

end K256.Proofs.Ecdh.Wrapper
