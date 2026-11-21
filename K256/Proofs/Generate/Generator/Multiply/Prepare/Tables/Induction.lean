import K256.Proofs.Generate.Generator.Multiply.Prepare.Tables.Step
import K256.Proofs.Generate.Generator.Multiply.Add

namespace K256.Proofs.Generate.Generator.Multiply.Prepare.Table

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Common.Tactic K256.Proofs.Generate.LIR

def tableWrites (q : BitVec 64) (first : Bool) : List MemoryRegion :=
  [⟨q.toNat-544,544⟩,⟨q.toNat+1048,120⟩,⟨q.toNat + entryOff first 0,960⟩,
    ⟨q.toNat+296,120⟩,⟨q.toNat+464,120⟩]

private theorem nextInputs {first : Bool} {i : Nat} {q : BitVec 64} {a b : Registers}
    (prev : Inputs first i q a) (rsp : b[4].get 64 = q) (df : b[22].get 1 = 0)
    (regs : ∀ j : Fin Reg.count, j.val ∈ Activation.calleeSavedNumbers → b[j] = savedReg first i q a j) :
    Inputs first (i+1) q b := by
  obtain ⟨_,_,base,work,src,temp⟩ := prev
  have eq (j : Fin Reg.count) (h : j.val ∈ Activation.calleeSavedNumbers) :
      b[j.val].get 64 = (savedReg first i q a j).get 64 := congrArg (Value.get 64) (regs j h)
  refine ⟨rsp,df,?_,?_,?_,?_⟩
  · cases first
    · exact (eq ⟨3,by decide⟩ (by decide)).trans (by simpa [savedReg] using base)
    · exact (eq ⟨5,by decide⟩ (by decide)).trans (by simpa [savedReg] using base)
  · cases first <;> exact (eq ⟨15,by decide⟩ (by decide)).trans (by simpa [savedReg] using work)
  · intro e; subst first
    exact (eq ⟨12,by decide⟩ (by decide)).trans (by simpa [savedReg] using src rfl)
  · intro bound
    cases first
    · apply (eq ⟨5,by decide⟩ (by decide)).trans
      by_cases one : i = 1
      · subst i; rfl
      · simpa [savedReg,one] using temp (by omega)
    · apply (eq ⟨13,by decide⟩ (by decide)).trans
      by_cases one : i = 1
      · subst i; rfl
      · simpa [savedReg,one] using temp (by omega)

def regsAfter (first : Bool) (n : Nat) (q : BitVec 64) (a : Registers) (r : Fin Reg.count) : Value :=
  if n = 0 then a[r] else
  if !first && r.val == 13 then ⟨64,q+0x490⟩ else
  if n ≥ 2 && r.val == (if first then 13 else 5) then ⟨64,q+0x418⟩ else a[r]

private theorem add_comm (p t : Projective) : p.add t = t.add p := by
  unfold Projective.add
  rw [Fin.mul_comm t.x p.x,Fin.mul_comm t.y p.y,Fin.mul_comm t.z p.z,
    Fin.mul_comm (t.x+t.y) (p.x+p.y), Fin.mul_comm (t.y+t.z) (p.y+p.z),
    Fin.mul_comm (t.x+t.z) (p.x+p.z)]

structure Partial (first : Bool) (n : Nat) (q : BitVec 64) (m : Ram) (p : Projective) : Prop where
  entries : ∀ j < n, ∃ t : Projective, t.valid ∧ t.Stored m (ptr q (entryOff first j)) ∧
    t.value = Curve.tableEntry p.value (j+1)
  next : ∃ t : Projective, t.valid ∧ t.Stored m (if n = 0 then q+baseOffset first else q+464) ∧
    t.value = Curve.tableEntry p.value (n+1)

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1200000 in
theorem buildTable (add : type_of% @addCall) (first : Bool)
    {fr : Activation} {initial a : Registers} {m : Ram} {d : Nat} {p : Projective}
    (entry : CoreEntry fr initial d) (s : State (site first 0) fr a m)
    (args : Inputs first 0 (sp fr) a) (valid : p.valid) (base : p.Stored m (sp fr+baseOffset first))
    (n : Nat) (bound : n ≤ 7) :
    ∃ b mem, Reaches (site first 0) a m (site first ⟨n,by omega⟩) b mem ∧
      State (site first ⟨n,by omega⟩) fr b mem ∧ Inputs first n (sp fr) b ∧
      Partial first n (sp fr) mem p ∧ RamWriteFrame m mem (tableWrites (sp fr) first) ∧
      ∀ j : Fin Reg.count, j.val ∈ Activation.calleeSavedNumbers → b[j] = regsAfter first n (sp fr) a j := by
  let q := sp fr
  have room := entry.room
  have high := entry.high
  change 3800 ≤ fr.rsp.toNat at room
  have qn : q.toNat = fr.rsp.toNat-3256 := BitVec.toNat_sub_of_le (by change 3256 ≤ fr.rsp.toNat; omega)
  have qh : q.toNat+3256 ≤ 2^32 := by omega
  have bn : (q+baseOffset first).toNat = q.toNat+baseOff first := by
    cases first <;> exact ptrNat qh (by decide)
  induction n with
  | zero =>
    exact ⟨a,m,.refl _,s,args,⟨by omega,⟨p,valid,base,rfl⟩⟩,.refl ..,fun _ _ => rfl⟩
  | succ n ih =>
    let i : Fin 7 := ⟨n,by omega⟩
    obtain ⟨b,mem,path,sb,inputs,tab,frame,saved⟩ := ih (by omega)
    obtain ⟨t,tv,st,vt⟩ := tab.next
    have base' : p.Stored mem (q+baseOffset first) := base.of_frame frame (by
      change Outside (tableWrites q first) (q+baseOffset first) 120
      simp only [Outside,tableWrites,List.mem_cons,List.not_mem_nil,or_false,forall_eq_or_imp,forall_eq,bn]
      cases first <;> dsimp [entryOff,baseOff] <;> omega)
    obtain ⟨c,nm,run,next,sum,old,delta,regs⟩ := addStep add first i entry sb inputs base' st
    have ⟨sumValid,sumVal⟩ := Projective.add_correct t p tv valid
    have bulk : RamWriteFrame m nm (tableWrites q first) := frame.trans delta (by
      intro r hr
      simp [stepWrites,copyWrites] at hr
      rcases hr with rfl|rfl|rfl|rfl|rfl
      · exact ⟨_,.head _,Nat.le_refl _,Nat.le_refl _⟩
      · exact ⟨_,.tail _ (.head _),Nat.le_refl _,Nat.le_refl _⟩
      · refine ⟨_,.tail _ (.tail _ (.head _)),?_⟩
        change q.toNat+entryOff first 0 ≤ q.toNat+entryOff first n ∧ q.toNat+entryOff first n+120 ≤ q.toNat+entryOff first 0+960
        simp only [entryOff,Nat.mul_zero,Nat.add_zero]
        omega
      · exact ⟨_,.tail _ (.tail _ (.tail _ (.head _))),Nat.le_refl _,Nat.le_refl _⟩
      · exact ⟨_,.tail _ (.tail _ (.tail _ (.tail _ (.head _)))),Nat.le_refl _,Nat.le_refl _⟩)
    have atoms := next.atoms
    rw [siteFrame] at atoms
    obtain ⟨rsp,df,_⟩ := atoms
    change c[4] = ⟨64,q⟩ at rsp
    change c[22] = ⟨1,0⟩ at df
    refine ⟨c,nm,path.trans run,next,nextInputs inputs (by rw [rsp]; rfl) (by rw [df]; rfl) regs,
      ⟨?_,?_⟩,bulk,?_⟩
    · intro j hj
      by_cases eq : j = n
      · subst j; exact ⟨t,tv,old,vt⟩
      have hj' : j < n := by omega
      obtain ⟨u,uv,stored,vu⟩ := tab.entries j hj'
      refine ⟨u,uv,stored.of_frame delta ?_,vu⟩
      have jb : entryOff first j + 120 ≤ 3088 := by cases first <;> dsimp [entryOff] <;> omega
      have off := ptrNat (q := q) qh (k := entryOff first j) (by omega)
      change Outside (stepWrites q (entryOff first n)) (ptr q (entryOff first j)) 120
      simp [Outside,stepWrites,copyWrites,off,entryOff]
      split <;> omega
    · refine ⟨p.add t,add_comm p t ▸ sumValid,sum,?_⟩
      rw [add_comm p t,sumVal,vt]; rfl
    · intro j hj
      rw [regs j hj]
      have oldReg := saved j hj
      change savedReg first n q b j = regsAfter first (n+1) q a j
      by_cases z : n = 0
      · subst n; cases first <;> simp [savedReg,regsAfter] at oldReg ⊢ <;> rw [oldReg]
      · by_cases one : n = 1
        · subst n; cases first <;> simp [savedReg,regsAfter] at oldReg ⊢ <;> rw [oldReg] <;> split <;> simp_all [q]
        · have two : 2 ≤ n := by omega
          cases first <;> simp [savedReg,regsAfter,z,one,two,show 2 ≤ n+1 by omega] at oldReg ⊢ <;> rw [oldReg]

end K256.Proofs.Generate.Generator.Multiply.Prepare.Table
