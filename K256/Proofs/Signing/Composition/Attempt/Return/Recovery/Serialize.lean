import K256.Proofs.Signing.Composition.Attempt.Return.Recovery.State
import K256.Proofs.Signing.Composition.Attempt.Return.Recovery.Memory
import K256.Proofs.Signing.Composition.Attempt.Coordinates.Serialize
import K256.Proofs.Signing.Composition.Attempt.Call
import K256.Proofs.Signing.Transfer.Verify
import K256.Proofs.Signing.LIR.Generated.Values
import K256.Proofs.Common.Tactic

namespace K256.Proofs.Signing.Composition.Attempt.Return.Recovery

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs CFG Lift Refine
  Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Verify.Core (Registers)
open Generate.Generator.Multiply (scalarWords)

private theorem serializePush {a : Registers} {m : Ram} {p : BitVec 64}
    (rsp : a[4].get 64 = p)
    (push : StoreOk Extracted.programImage m (p-8) 8 0x105de5 5) :
    ∃ b, LIR.program.runBlock (dialect Extracted.programImage) ⟨.l105dd5,a,m⟩ =
      .call ⟨.l120350,b,memStore m (p-8) (0x105dea : BitVec 64)⟩ (resume .l105dea 0x105dea) ∧
      b[3] = ⟨64,p+256⟩ ∧ b[4] = ⟨64,p-8⟩ ∧ b[6] = ⟨64,p+256⟩ ∧
      b[7] = ⟨64,p+8⟩ ∧
      ∀ i : Fin Reg.count, i.val ∈ [5,12,13,14,15,22,39,50,51] → b[i] = a[i] := by
  refine ⟨?_,?run,?post⟩
  case run =>
    cfg_eval [rsp,push]
    rfl
  refine ⟨rfl,rfl,rfl,rfl,?_⟩
  intro ⟨i,_⟩ hi
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
  rcases hi with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> rfl

theorem serialize {s : RamState} {secret msg : ByteArray} {d : Nat}
    (call : ValidCall signingKeyTrySign s [secret,msg])
    {a : Registers} {m : Ram} {r sigS : Nat}
    (input : Staged s d r sigS a m) :
    ∃ b n, Reach (core .l105dd5 a m) (core .l105dea b n) ∧ Staged s d r sigS b n ∧ b[3] = ⟨64,sp s+256⟩ := by
  obtain ⟨room,high,spNat⟩ := stackBounds call
  let base := sp s-112
  have baseNat : base.toNat = (sp s).toNat-112 := belowNat call (by decide)
  have baseAlign : base.toNat % 16 = 0 := by
    have aligned : (stackPtr s).toNat % 16 = 8 := call.stackAvailable.2.2.2
    rw [baseNat,spNat]
    omega
  have slotNat : (sp s-8).toNat = (sp s).toNat-8 := belowNat call (by decide)
  have floorEq : base-121 = sp s-233 := by dsimp [base]; bv_omega
  have floorNat : (base-121).toNat = (sp s).toNat-233 := by
    rw [floorEq]
    exact belowNat call (by decide)
  have slotEq : base+104 = sp s-8 := by dsimp [base]; bv_omega
  have outSp : base+112 = sp s := BitVec.sub_add_cancel _ _
  have destNat : (sp s+8).toNat = (sp s).toNat+8 := offsetNat call (by decide)
  have sourceNat : (sp s+256).toNat = (sp s).toNat+256 := offsetNat call (by decide)
  have slot : Writable Extracted.programImage m (sp s-8) 8 := by
    rw [addr_sub]
    exact stackWindow call input.toMemory (by decide)
  have guard : StoreOk Extracted.programImage m (sp s-8) 8 0x105de5 5 :=
    ParseSignature.storeOk_of_codeRange (off := 16) slot
      (fun x hx => Common.fnCode_subset_programImage x (LIR.code_l105dd5 x hx)) (by decide)
  obtain ⟨b,step,bx,rsp,rsi,rdi,keep⟩ :=
    serializePush (p := sp s) (congrArg (Value.get 64) input.rsp) guard
  let t := memStore m (sp s-8) (0x105dea : BitVec 64)
  have win : Writable Extracted.programImage t (base-121) 433 := by
    apply Writable.memStore
    rw [floorEq,addr_sub]
    exact stackWindow call input.toMemory (by decide)
  have rd : Readable t (sp s+256) 40 :=
    ((stackWindow call input.toMemory (by decide)).readable).memStore _ _
  have wr : Writable Extracted.programImage t (sp s+8) 32 :=
    (stackWindow call input.toMemory (by decide)).memStore _ _
  have ret : memLoad t (base+104) 64 = 0x105dea := by
    rw [slotEq]
    exact memLoad_memStore_same _ _ _ (by decide) (by decide)
  have width (i : Fin Reg.count) (hi : i.val ∈ [5,12,13,14,15,22,39,50,51])
      (hs : i.val ∈ Activation.calleeSavedNumbers) : b[i].width = 64 :=
    (congrArg Value.width (keep i hi)).trans (input.saved i hs)
  let w : Common.Field.Limbs := Vector.ofFn fun i => memLoad t (wordAddr (sp s+256) 64 i) 64
  have words : WordsAt t (sp s+256) 64 w := by
    intro i hi
    simp only [w,Vector.getElem_ofFn]
  obtain ⟨out,run,tag,o4,o3,o22,kept,args,o14,writes,_⟩ := Serializer.serializeWords
    (base := base) (src := sp s+256) (dst := sp s+8)
    (by rw [rsp,slotEq]; rfl) (congrArg (Value.get 64) rsi)
    (congrArg (Value.get 64) rdi) (width 5 (by decide) (by decide))
    (width 12 (by decide) (by decide)) (width 13 (by decide) (by decide))
    (width 15 (by decide) (by decide)) ((keep 22 (by decide)).trans input.df)
    (rfl : b[14].get 64 = _) win rd wr (by omega) (by omega) baseAlign (by decide) ret words
  have reach := callReaches step
    (Signing.Transfer.verifyExecAt (Signing.Transfer.attemptCalleesCovered (.l120350,.l120350)
      (by repeat' first | apply List.mem_cons_self | apply List.mem_cons_of_mem))
      (Serializer.transfer run)) tag
  let regions : List MemoryRegion := [⟨(base-121).toNat,233⟩,⟨(sp s+8).toNat,32⟩]
  have pushed : RamWriteFrame m t regions := by
    apply (RamWriteFrame.refl _ _).memStore
    refine ⟨_,List.mem_cons_self ..,?_⟩
    simp only [InRegion,Nat.reduceDiv]
    have := slot.readable.low
    omega
  have frame : RamWriteFrame m out.store regions :=
    pushed.trans writes (fun g hr => ⟨g,hr,Nat.le_refl _,Nat.le_refl _⟩)
  have memory := preserveCore call input.toCoreMemory frame (by
    intro g hr
    rcases List.mem_cons.mp hr with h|h
    · subst g
      change _ ≤ (base-121).toNat ∧ (base-121).toNat+233 ≤ _
      omega
    · obtain rfl := List.mem_singleton.mp h
      change _ ≤ (sp s+8).toNat ∧ (sp s+8).toNat+32 ≤ _
      omega)
  have rb : out.values[3] = ⟨64,sp s+256⟩ := o3.trans (by rw [bx]; rfl)
  have saved (i : Fin Reg.count) (hi : i.val ∈ Activation.calleeSavedNumbers) : out.values[i].width = 64 := by
    rcases i with ⟨i,_⟩
    simp only [Activation.calleeSavedNumbers,List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl|rfl|rfl|rfl|rfl|rfl
    · exact congrArg Value.width rb
    · exact (congrArg Value.width (kept 5 (by decide))).trans (width 5 (by decide) (by decide))
    · exact (congrArg Value.width (kept 12 (by decide))).trans (width 12 (by decide) (by decide))
    · exact (congrArg Value.width (kept 13 (by decide))).trans (width 13 (by decide) (by decide))
    · exact congrArg Value.width o14
    · exact (congrArg Value.width (kept 15 (by decide))).trans (width 15 (by decide) (by decide))
  have fp : out.values[39].width = 32 ∧ out.values[50].width = 16 ∧ out.values[51].width = 16 :=
    ⟨(congrArg Value.width ((kept 39 (by decide)).trans (keep 39 (by decide)))).trans input.fp.1,
     (congrArg Value.width ((kept 50 (by decide)).trans (keep 50 (by decide)))).trans input.fp.2.1,
     (congrArg Value.width ((kept 51 (by decide)).trans (keep 51 (by decide)))).trans input.fp.2.2⟩
  have apartOutput (i : Nat) (lo : 192 ≤ i) (hi : i ≤ 224) :
      Outside regions (sp s+BitVec.ofNat 64 i) 32 := by
    rw [Outside,offsetNat call (by omega)]
    refine ⟨by omega,fun g hr => Or.inr ?_⟩
    rcases List.mem_cons.mp hr with h|h
    · subst g
      change (base-121).toNat+233 ≤ _
      omega
    · obtain rfl := List.mem_singleton.mp h
      change (sp s+8).toNat+32 ≤ _
      omega
  refine ⟨_,_,reach,⟨memory,outSp ▸ o4,o22,saved,args,fp,?_,?_⟩,rb⟩
  · exact input.first.of_frame frame (by decide) (apartOutput 192 (by decide) (by decide))
  · exact input.second.of_frame frame (by decide) (apartOutput 224 (by decide) (by decide))

end K256.Proofs.Signing.Composition.Attempt.Return.Recovery
