import K256.Proofs.Signing.Composition.Wrapper.Frame
import K256.Proofs.Verify.LIR.Generated.Values
import K256.Proofs.Common.Tactic
import K256.Proofs.Signing.SecretDecode
import K256.Proofs.Signing.Transfer.Verify
import K256.Proofs.Common.Lift.Generated.Values.Load

namespace K256.Proofs.Signing.Composition.Wrapper

open K256.Spec K256.Spec.Program Prelude X86 X86.Machine X86.UserProcess X86Proofs
  CFG Lift Refine Standards.SECG.ECC Standards.SECG.DomainParameters.Secp256k1
open Verify.Core (Registers)
open Verify.LIR

private abbrev decodeTop (s : RamState) := stackPtr s - 480
private abbrev decodeDst (s : RamState) := stackPtr s - 440
private abbrev decodeResume := resume .l102651 0x102651

private def decodeArgs (a : Registers) (top : BitVec 64) : Registers :=
  Vector.ofFn fun i =>
    match i.val with
    | 3 => ⟨64, a[7].get 64⟩
    | 4 => ⟨64, top⟩
    | 7 => ⟨64, top + 40⟩
    | 14 => ⟨64, a[1].get 64⟩
    | 15 => ⟨64, a[2].get 64⟩
    | _ => a[i]

private abbrev entryRegisters (s : RamState) : Registers :=
  Vector.ofFn fun i => (Reg.ofIndex i).read s

private abbrev decodeRegisters (s : RamState) : Registers := decodeArgs (entryRegisters s) (decodeTop s)

private abbrev pushed15 (a : Registers) (top : BitVec 64) (m : Ram) :=
  memStore m (top - 8) (a[15].get 64)
private abbrev pushed14 (a : Registers) (top : BitVec 64) (m : Ram) :=
  memStore (pushed15 a top m) (top - 16) (a[14].get 64)
private abbrev pushed12 (a : Registers) (top : BitVec 64) (m : Ram) :=
  memStore (pushed14 a top m) (top - 24) (a[12].get 64)
private abbrev pushedBX (a : Registers) (top : BitVec 64) (m : Ram) :=
  memStore (pushed12 a top m) (top - 32) (a[3].get 64)

private abbrev push15 (s : RamState) := pushed15 (entryRegisters s) (stackPtr s) s.external
private abbrev push14 (s : RamState) := pushed14 (entryRegisters s) (stackPtr s) s.external
private abbrev push12 (s : RamState) := pushed12 (entryRegisters s) (stackPtr s) s.external
private abbrev pushBX (s : RamState) := pushedBX (entryRegisters s) (stackPtr s) s.external

private abbrev decodeMemory (s : RamState) := memStore (pushBX s) (decodeTop s) (0x102651 : BitVec 64)

set_option maxHeartbeats 500000 in
private theorem entryBlock {a : Registers} {code : CodeMap} {top : BitVec 64} {m : Ram}
    (rsp : a[4].get 64 = top)
    (g1 : StoreOk code m (top - 8) 8 0x102630 2)
    (g2 : StoreOk code (pushed15 a top m) (top - 16) 8 0x102632 2)
    (g3 : StoreOk code (pushed14 a top m) (top - 24) 8 0x102634 2)
    (g4 : StoreOk code (pushed12 a top m) (top - 32) 8 0x102636 1)
    (g5 : StoreOk code (pushedBX a top m) (top - 480) 8 0x10264c 5) :
    LIR.program.runBlock (dialect code) ⟨.l102630,a,m⟩ =
      .call ⟨.l106dd0,decodeArgs a (top - 480),
        memStore (pushedBX a top m) (top - 480) (0x102651 : BitVec 64)⟩ decodeResume := by
  cfg_eval [rsp]
  refine (ite_eq_left g1).trans ((ite_eq_left g2).trans ((ite_eq_left g3).trans
    ((ite_eq_left g4).trans ((ite_eq_left g5).trans ?_))))
  apply congrArg (fun b => CFG.Transfer.call ⟨.l106dd0,b,_⟩ decodeResume)
  apply (show ∀ {u v : Registers}, (∀ i : Fin 53, u[i.val] = v[i.val]) → u = v from
    fun eq => Vector.ext fun i hi => eq ⟨i,hi⟩)
  intro i
  have dst : top - 440 = top - 480 + 40 := by bv_omega
  finite_cases i <;> simp only [decodeArgs, Vector.getElem_ofFn] <;>
    first | rfl | exact congrArg (Value.mk 64) dst

private theorem push {s : RamState} {secret msg : ByteArray} {m : Ram} {off : Nat}
    (call : ValidCall signingKeyTrySign s [secret,msg]) (depth : off ≤ 11192)
    (w : RamWriteFrame s.external m [Stack.region s signingKeyTrySign.minStackBytes]) (v : BitVec 64) :
    RamWriteFrame s.external (memStore m (stackPtr s - BitVec.ofNat 64 off) v)
      [Stack.region s signingKeyTrySign.minStackBytes] :=
  w.memStore v ⟨_, List.mem_cons_self, Common.stackRange call.stackAvailable depth (by omega)⟩

private theorem pushFrames {s : RamState} {secret msg : ByteArray}
    (call : ValidCall signingKeyTrySign s [secret,msg]) :
    RamWriteFrame s.external (push15 s) [Stack.region s signingKeyTrySign.minStackBytes] ∧
    RamWriteFrame s.external (push14 s) [Stack.region s signingKeyTrySign.minStackBytes] ∧
    RamWriteFrame s.external (push12 s) [Stack.region s signingKeyTrySign.minStackBytes] ∧
    RamWriteFrame s.external (pushBX s) [Stack.region s signingKeyTrySign.minStackBytes] := by
  have f1 := push (off := 8) call (by decide) (.refl s.external _) ((entryRegisters s)[15].get 64)
  have f2 := push (off := 16) call (by decide) f1 ((entryRegisters s)[14].get 64)
  have f3 := push (off := 24) call (by decide) f2 ((entryRegisters s)[12].get 64)
  exact ⟨f1,f2,f3,push (off := 32) call (by decide) f3 ((entryRegisters s)[3].get 64)⟩

private theorem entryGuard {s : RamState} {secret msg : ByteArray} {m : Ram}
    (call : ValidCall signingKeyTrySign s [secret,msg])
    (f : RamWriteFrame s.external m [Stack.region s signingKeyTrySign.minStackBytes])
    (off pos len : Nat) (depth : off ≤ 11192) (fits : pos+len ≤ LIR.bytes_l102630.length) :
    StoreOk Extracted.programImage m (stackPtr s - BitVec.ofNat 64 off) 8
      (0x102630 + BitVec.ofNat 64 pos) len :=
  ParseSignature.storeOk_of_codeRange (base := 0x102630) (bytes := LIR.bytes_l102630)
    ((Common.stackWritable (off := off) (len := 8) call depth (by omega) (by decide)).of_frame f)
    (fun x hx => Common.fnCode_subset_programImage x (LIR.code_l102630 x hx)) fits

private theorem decodeEntry {s : RamState} {secret msg : ByteArray}
    (call : ValidCall signingKeyTrySign s [secret,msg]) :
    LIR.program.runBlock (dialect Extracted.programImage) (LIR.lifted.locationOf .l102630 s) =
      .call ⟨.l106dd0,decodeRegisters s,decodeMemory s⟩ decodeResume := by
  let a := entryRegisters s
  have rsp : a[4].get 64 = stackPtr s := by
    simp only [a,entryRegisters,Vector.getElem_ofFn]
    rfl
  obtain ⟨f1,f2,f3,f4⟩ := pushFrames call
  have g1 := entryGuard call (.refl s.external _) 8 0 2 (by decide) (by decide)
  have g2 := entryGuard call f1 16 2 2 (by decide) (by decide)
  have g3 := entryGuard call f2 24 4 2 (by decide) (by decide)
  have g4 := entryGuard call f3 32 6 1 (by decide) (by decide)
  have g5 := entryGuard call f4 480 28 5 (by decide) (by decide)
  have e := @entryBlock a Extracted.programImage (stackPtr s) s.external rsp
  specialize e g1
  specialize e g2
  specialize e g3
  specialize e g4
  specialize e g5
  have loc : LIR.lifted.locationOf .l102630 s = ⟨.l102630,a,s.external⟩ := rfl
  rw [loc]
  exact e

private theorem decodeMemory_state {s : RamState} {secret msg : ByteArray}
    (call : ValidCall signingKeyTrySign s [secret,msg]) :
    Memory s (decodeMemory s) ∧ memLoad (decodeMemory s) (decodeTop s) 64 = 0x102651 := by
  have old := (pushFrames call).2.2.2
  have v15 : (entryRegisters s)[15].get 64 = s.regValue .r15 := by
    simp only [entryRegisters,Vector.getElem_ofFn]
    rfl
  have v14 : (entryRegisters s)[14].get 64 = s.regValue .r14 := by
    simp only [entryRegisters,Vector.getElem_ofFn]
    rfl
  have v12 : (entryRegisters s)[12].get 64 = s.regValue .r12 := by
    simp only [entryRegisters,Vector.getElem_ofFn]
    rfl
  have v3 : (entryRegisters s)[3].get 64 = s.regValue .rbx := by
    simp only [entryRegisters,Vector.getElem_ofFn]
    rfl
  refine ⟨⟨push (off := 480) call (by decide) old _,?_,?_,?_,?_,?_⟩,?_⟩
  · change _ = memLoad s.external (stackPtr s) 64
    simp (disch := store_disch) only [decodeMemory, decodeTop, pushBX, pushedBX, pushed12,
      pushed14, pushed15, memLoad_memStore_of_rangeApart]
  all_goals
    simp (disch := store_disch) only [decodeMemory, decodeTop, pushBX, pushedBX, pushed12,
      pushed14, pushed15, v3, v12, v14, v15, memLoad_memStore_same, memLoad_memStore_of_rangeApart]

private abbrev decodeActivation (s : RamState) : Activation where
  original := decodeMemory s
  rsp := decodeTop s
  ret := 0x102651
  low := stackPtr s - 816
  rcx := s.regValue .rcx
  rdx := s.regValue .rdx
  rbx := s.regValue .rdi
  rbp := s.regValue .rbp
  rsi := s.regValue .rsi
  rdi := decodeDst s
  r8 := s.regValue .r8
  r9 := s.regValue .r9
  r12 := s.regValue .r12
  r13 := s.regValue .r13
  r14 := s.regValue .rcx
  r15 := s.regValue .rdx
  mxcsr := (Operand.mxcsr : Operand 32).read s
  ftw := (Operand.ftw : Operand 16).read s
  fcw := (Operand.fcw : Operand 16).read s
  fs := s.FS

private theorem stackMember (s : RamState) :
    Stack.region s signingKeyTrySign.minStackBytes ∈ writtenRegions signingKeyTrySign s := by
  simp [writtenRegions]

set_option maxHeartbeats 500000 in
private theorem decodeAtoms {s : RamState} {secret msg : ByteArray}
    (call : ValidCall signingKeyTrySign s [secret,msg]) (mem : Memory s (decodeMemory s))
    (ret : memLoad (decodeMemory s) (decodeTop s) 64 = 0x102651) :
    Atom.All Extracted.programImage (decodeRegisters s) (decodeMemory s)
      (Fn106dd0.frameAt .l106dd0 (decodeActivation s)) := by
  have top : (decodeTop s).toNat = (stackPtr s).toNat - 480 :=
    Common.stackOffset call.stackAvailable (by decide)
  have bottom : (decodeActivation s).low.toNat = (stackPtr s).toNat - 816 :=
    Common.stackOffset call.stackAvailable (by decide)
  obtain ⟨room, limit, _⟩ := stackBounds call
  have align := call.stackAvailable.2.2.2
  change (stackPtr s).toNat % 16 = 8 at align
  have readable := ((Common.stackWritable (off := 480) (len := 8) call
    (by decide) (by decide) (by decide)).of_frame mem.written).readable
  have writable := (Common.stackWritable (off := 816) (len := 336) call
    (by decide) (by decide) (by decide)).of_frame mem.written
  have addr : decodeTop s - 336 = stackPtr s - 816 := by unfold decodeTop; bv_omega
  have ro : Sec1.LIR.rodataSection ∈ Extracted.programSections :=
    .tail _ (.head _)
  have slots := Fn106dd0.callSlots_loaded ro (mem.image call)
  obtain ⟨r1,v1⟩ := slots (0x203dd0,0x12a820) (by decide)
  obtain ⟨r2,v2⟩ := slots (0x203de0,0x129770) (by decide)
  obtain ⟨r3,v3⟩ := slots (0x203e20,0x100a20) (by decide)
  have span := Fn106dd0.callSlots_span ro
  have avoid := (call.separation.2 _ (stackMember s)).1
  have apart := apart_of_avoids (lo := 0x203dd0) (hi := 0x203e28) avoid
    (fun a h₁ h₂ => by
      obtain ⟨b,hb⟩ := span a h₁ h₂
      exact Or.inl ⟨b,Common.programSections_fetchByte_of_mem hb⟩)
    (by rw [stackRegion call]; exact (by decide : 0 < 11200)) (by decide) (by decide)
  rw [stackRegion call] at apart
  change (stackPtr s - 11192#64).toNat + 11200 ≤ 0x203dd0 ∨
    0x203e28 ≤ (stackPtr s - 11192#64).toNat at apart
  rw [Common.stackOffset (off := 11192) call.stackAvailable (by decide)] at apart
  have slotApart : 0x203f78 ≤ (decodeTop s).toNat ∨ (decodeTop s).toNat ≤ 0x203dd0 := by omega
  simp only [Fn106dd0.frameAt, Fn106dd0.frameAtG9, Atom.All, Atom.Holds]
  refine ⟨?rsp, ?df, ?cx, ?dx, ?bx, ?bp, ?si, ?di, ?r8, ?r9, ?r12, ?r13, ?r14, ?r15,
    ?mx, ?ft, ?fc, ?read, ?ret, ?tag, ?write, ?space, ?aligned, ?read1, ?v1, ?read2, ?v2,
    ?read3, ?v3, ?apart, trivial⟩
  case df =>
    simp only [decodeRegisters,decodeArgs,entryRegisters,Fin.getElem_fin,Vector.getElem_ofFn]
    change (Reg.ofIndex 22).read s = ⟨1,0⟩
    exact (Reg.read_df_iff (s := s)).mpr call.directionFlagUnset
  case di =>
    have dest : decodeTop s + 40 = decodeDst s := by unfold decodeTop decodeDst; bv_omega
    simp only [decodeRegisters,decodeArgs,Fin.getElem_fin,Vector.getElem_ofFn]
    change (⟨64,decodeTop s + 40⟩ : Value) = ⟨64,decodeDst s⟩
    exact congrArg (Value.mk 64) dest
  case read => exact readable
  case ret => exact ret
  case tag => exact (by decide : (0x102651 : BitVec 64).toNat < 2^32)
  case write =>
    change Writable Extracted.programImage (decodeMemory s) (decodeTop s - 336) 336
    rw [addr]
    exact writable
  case space =>
    change (decodeActivation s).low.toNat + 336 ≤ (decodeTop s).toNat
    omega
  case aligned =>
    change (decodeTop s).toNat % 16 = 8
    omega
  case read1 => exact r1
  case v1 => exact v1
  case read2 => exact r2
  case v2 => exact v2
  case read3 => exact r3
  case v3 => exact v3
  case apart => exact slotApart
  all_goals
    simp only [decodeRegisters,decodeArgs,entryRegisters,Fin.getElem_fin,Vector.getElem_ofFn] <;> rfl

private theorem decodeMemory_advance {s : RamState} {secret msg : ByteArray} {n : Ram}
    (call : ValidCall signingKeyTrySign s [secret,msg]) (mem : Memory s (decodeMemory s))
    (writes : RamWriteFrame (decodeMemory s) n
      [(decodeActivation s).region, ⟨(decodeDst s).toNat,40⟩]) : Memory s n := by
  obtain ⟨room, _, _⟩ := stackBounds call
  have top : (decodeTop s).toNat = (stackPtr s).toNat - 480 :=
    Common.stackOffset call.stackAvailable (by decide)
  have bottom : (decodeActivation s).low.toNat = (stackPtr s).toNat - 816 :=
    Common.stackOffset call.stackAvailable (by decide)
  have dest : (decodeDst s).toNat = (stackPtr s).toNat - 440 :=
    Common.stackOffset call.stackAvailable (by decide)
  have bounds (r : MemoryRegion) (hr : r ∈ [(decodeActivation s).region, ⟨(decodeDst s).toNat,40⟩]) :
      (stackPtr s).toNat - 11192 ≤ r.start ∧ r.start + r.size ≤ (stackPtr s).toNat - 32 := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl
    · change _ ≤ (decodeActivation s).low.toNat ∧
        (decodeActivation s).low.toNat + ((decodeTop s).toNat - (decodeActivation s).low.toNat) ≤ _
      omega
    · change _ ≤ (decodeDst s).toNat ∧ (decodeDst s).toNat + 40 ≤ _
      omega
  exact preserveSlots call mem writes bounds

private theorem decodeCall {s : RamState} {secret msg : ByteArray} {d : Nat}
    (call : ValidCall signingKeyTrySign s [secret,msg]) (decoded : Keys.decodeSecret domain secret = some d) :
    ∃ out : Output Value Ram Reg.count,
      Reach ⟨LIR.lifted.locationOf .l102630 s, []⟩ (atBlock .l102651 out.values out.store) ∧
      Saved s out.values ∧ ParseSignature.ArgumentWidths out.values ∧
      Memory s out.store ∧ memLoad out.store (decodeDst s) 64 = 0 ∧
      WordsAt out.store (decodeDst s + 8) 64 (Generate.Generator.Multiply.scalarWords d) := by
  obtain ⟨mem,ret⟩ := decodeMemory_state call
  have atoms := decodeAtoms call mem ret
  obtain ⟨room, limit, _⟩ := stackBounds call
  have top : (decodeTop s).toNat = (stackPtr s).toNat - 480 :=
    Common.stackOffset call.stackAvailable (by decide)
  let src := registerRegion s .rsi 32
  have input : ValidInput s src secret := call.inputsInMemory.1
  have dst := (Common.stackWritable (off := 440) (len := 40) call
    (by decide) (by decide) (by decide)).of_frame mem.written
  have separate : (Stack.region s signingKeyTrySign.minStackBytes).Disjoint src :=
    (call.separation.2 _ (stackMember s)).2 src List.mem_cons_self
  have writeFrame : MemoryWriteFrame s {s with external := decodeMemory s}
      #v[Stack.region s signingKeyTrySign.minStackBytes] :=
    mem.written.memoryWriteFrame fun _ none _ hr => none _ (Vector.mem_toList_iff.mp hr)
  have bytes : src.HasBytes (decodeMemory s) secret := Common.hasBytes_of_memoryWriteFrame writeFrame input.2.2 input.2.1 (by
    intro r hr
    obtain rfl := Vector.mem_singleton.mp hr
    exact fun _ h₁ h₂ => separate _ h₂ h₁)
  have length : secret.size = 32 := bytes.1
  have read := Readable.of_hasBytes bytes input.2.1
  rw [length] at read
  change Readable _ (BitVec.ofNat 64 (s.regValue .rsi).toNat) 32 at read
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq] at read
  have srcLimit : (s.regValue .rsi).toNat + 32 < 2^32 := input.2.1
  have pos : 0 < (Stack.region s signingKeyTrySign.minStackBytes).size := by
    rw [stackRegion call]
    exact (by decide : 0 < 11200)
  have apart := apart_of_disjoint separate pos (show 0 < src.size from (by decide : 0 < 32))
  rw [stackRegion call] at apart
  change (stackPtr s - 11192#64).toNat + 11200 ≤ (s.regValue .rsi).toNat ∨
    (s.regValue .rsi).toNat + 32 ≤ (stackPtr s - 11192#64).toNat at apart
  rw [Common.stackOffset (off := 11192) call.stackAvailable (by decide)] at apart
  have low : (decodeActivation s).low = (decodeTop s) - 336 := by unfold decodeActivation decodeTop; bv_omega
  have addr : decodeDst s = decodeTop s + 40 := by unfold decodeDst decodeTop; bv_omega
  obtain ⟨out, run, tag, done_, widths, writes, zero, key⟩ := SecretDecode.execution atoms
    (mem.image call) low (by change 336 ≤ (decodeTop s).toNat; omega)
    (by change (decodeTop s).toNat + 80 < 2^32; omega) addr dst length bytes read srcLimit
    (by change (s.regValue .rsi).toNat + 32 ≤ (decodeTop s).toNat - 336 ∨
        (decodeTop s).toNat + 80 ≤ (s.regValue .rsi).toNat; omega) decoded
  have run := Transfer.verifyExec (dst := .l106dd0) (List.mem_cons_self) run
  have reach : Reach ⟨LIR.lifted.locationOf .l102630 s,[]⟩ (atBlock .l102651 out.values out.store) := by
    refine .step (b := ⟨⟨.l106dd0,decodeRegisters s,decodeMemory s⟩,[decodeResume]⟩) ?_ ?_
    · change (LIR.program.runBlock _ _).next _ _ = _
      rw [decodeEntry call]
      rfl
    · exact ParseSignature.exec_reaches_resume run decodeResume [] (by rw [tag]; rfl)
  simp only [Fn106dd0.doneAt, Atom.All, Atom.Holds] at done_
  obtain ⟨rsp,df,bx,bp,r12,r13,r14,r15,mx,ftw,fcw,_⟩ := done_
  have stack : decodeTop s + 8 = localSp s := by unfold decodeTop localSp sp; bv_omega
  change out.values[4] = ⟨64,decodeTop s + 8⟩ at rsp
  rw [stack] at rsp
  refine ⟨out, reach, ⟨rsp,bx,bp,r13,r15,r14,?_,df,?_⟩,
    widths,decodeMemory_advance call mem writes,zero,key⟩
  · exact congrArg Value.width r12
  · exact ⟨congrArg Value.width mx,congrArg Value.width ftw,congrArg Value.width fcw⟩

private theorem decodeSuccess {s : RamState} {a : Verify.Core.Registers} {m : Ram}
    (saved : Saved s a) (widths : ParseSignature.ArgumentWidths a) (read : LoadOk m (localSp s + 32) 4)
    (flag : memLoad m (localSp s + 32) 32 = 0) :
    ∃ b, Reach (atBlock .l102651 a m) (atBlock .l10265c b m) ∧ Saved s b ∧ (∀ i : Fin Reg.count, i.val ∈ [2,8,9] → b[i].width = 64) := by
  have rsp : a[4].get 64 = localSp s := by rw [saved.rsp]; rfl
  refine ⟨?_, .single ?step, ?saved, ?widths⟩
  case step =>
    change (LIR.program.runBlock _ _).next _ [] = _
    cfg_eval [rsp, read, flag, cmpSpec_ZF]
    rfl
  case saved => exact ⟨saved.rsp,saved.output,saved.rbp,saved.r13,saved.message,saved.length,
    saved.r12,saved.df,saved.fp⟩
  case widths =>
    rintro ⟨i, hi⟩ h
    have hw := widths ⟨i, hi⟩ (by
      simp only [Activation.argumentNumbers, List.mem_cons, List.not_mem_nil, or_false] at h ⊢
      omega)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl <;> exact hw

theorem decode {s : RamState} {secret msg : ByteArray} {d : Nat}
    (call : ValidCall signingKeyTrySign s [secret,msg])
    (decoded : Keys.decodeSecret domain secret = some d) :
    ∃ a m, Reach ⟨LIR.lifted.locationOf .l102630 s,[]⟩ (atBlock .l10265c a m) ∧
      DecodeResult s d a m := by
  obtain ⟨out, reach, saved, widths, mem, zero, key⟩ := decodeCall call decoded
  have dst : localSp s + 32 = decodeDst s := by unfold localSp sp decodeDst; bv_omega
  have flag : memLoad out.store (localSp s + 32) 32 = 0 := by
    have low := extractLsb'_memLoad out.store (decodeDst s) (n := 64) 0 32
      (by decide) (by decide) (by decide)
    rw [zero, Nat.zero_div, BitVec.add_zero] at low
    rw [dst, ← low]
    rfl
  have read : LoadOk out.store (localSp s + 32) 4 := by
    rw [dst]
    have slot := (Common.stackWritable (off := 440) (len := 4) call
      (by decide) (by decide) (by decide)).of_frame mem.written
    exact ⟨slot.readable.low,slot.readable.present⟩
  obtain ⟨b, branch, preserved, hwidths⟩ := decodeSuccess saved widths read flag
  have keyAddr : localSp s + 40 = decodeDst s + 8 := by unfold localSp sp decodeDst; bv_omega
  have words : WordsAt out.store (localSp s + 40) 64 (Generate.Generator.Multiply.scalarWords d) := by
    rw [keyAddr]
    exact key
  exact ⟨b,out.store,reach.trans branch,⟨⟨preserved,mem,words⟩,hwidths⟩⟩

end K256.Proofs.Signing.Composition.Wrapper
