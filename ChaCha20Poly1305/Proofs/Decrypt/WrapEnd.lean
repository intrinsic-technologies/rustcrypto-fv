import ChaCha20Poly1305.Proofs.Decrypt.Deliver
import ChaCha20Poly1305.Proofs.Decrypt.MachineResult

namespace ChaCha20Poly1305.Proofs.Decrypt.Wrapper
open Prelude X86 X86.Machine X86.UserProcess X86Proofs ChaCha20Poly1305.Proofs.CFG ChaCha20Poly1305.Proofs.Lift ChaCha20Poly1305.Proofs.Refine
open ChaCha20Poly1305.Proofs.Decrypt.Lifted hiding Label program
open ChaCha20Poly1305.Spec.Program
open Hash Detached

@[refine_layout] def wframe (root : Activation) (p : Packet) (total : BitVec 64) :=
  {root with rsp:=root.rsp-136,rbx:=root.r9,rbp:=p.buf,r12:=root.rsi,r13:=root.rcx,r14:=total,r15:=root.rdx}

@[refine_layout] def savedABI (fr : Activation) : List Atom :=
  [.mem (fr.rsp-48) 64 fr.rbx,.mem (fr.rsp-40) 64 fr.r12,.mem (fr.rsp-32) 64 fr.r13,
   .mem (fr.rsp-24) 64 fr.r14,.mem (fr.rsp-16) 64 fr.r15,.mem (fr.rsp-8) 64 fr.rbp,
   .readable fr.rsp 8,.mem fr.rsp 64 fr.ret,.fact (fr.ret.toNat<2^32),
   .writable (fr.rsp-1008) 1008,.fact (fr.low.toNat+1008≤fr.rsp.toNat),.fact (fr.rsp.toNat%16=8)]

def commonFoot (p : Packet) (total : BitVec 64) : List MemoryRegion := [⟨p.buf.toNat,total.toNat⟩,allocatorStateRegion]
def resultFoot (p : Packet) (total dest : BitVec 64) := commonFoot p total ++ (if p.good then [⟨dest.toNat,p.n.toNat⟩] else [])
def tailFoot (p : Packet) (root : Activation) (total : BitVec 64) : List MemoryRegion :=
  [⟨root.rsp.toNat-1008,928⟩,⟨p.buf.toNat,total.toNat⟩] ++
    (if p.good then [⟨root.r9.toNat,p.n.toNat⟩] else [])

structure Completed (p : Packet) (root : Activation) (total : BitVec 64) (o : Result) : Prop where
  returned : Returned root (resultFoot p total root.r9) o
  status : o.values[0]=⟨64,if p.good then 0 else 1⟩
  output : p.good=true → memLoad o.store root.r9 (8*p.n.toNat)=p.dst

set_option maxHeartbeats 650000
set_option maxRecDepth 7000
set_option linter.constructorNameAsVariable false
attribute [local irreducible] Packet.good Packet.dst memLoad memStore

private theorem skipEmpty {m m' rs} (f : RamWriteFrame m m' rs) :
    RamWriteFrame m m' (rs.filter (fun r => decide (0<r.size))) := by
  refine ⟨fun x hx => f.outside x ⟨hx.1,?_⟩,f.present⟩
  intro r hr
  by_cases e : 0<r.size
  · exact hx.2 r (List.mem_filter.mpr ⟨hr,by simpa using e⟩)
  · omega

theorem leave (p : Packet) (root : Activation) (total : BitVec 64) (m : Ram) (a : lifted.Location)
    (base : RamWriteFrame root.original m (root.region :: commonFoot p total))
    (frame : RamWriteFrame m a.store (tailFoot p root total))
    (abi : Atom.All fnCode a.arguments m (savedABI root)) (floor : root.low.toNat+1008≤root.rsp.toNat)
    (heap : p.buf.toNat+total.toNat≤root.rsp.toNat-1008 ∨ root.rsp.toNat+8≤p.buf.toNat)
    (out : p.good=true → 0<p.n.toNat → root.r9.toNat+p.n.toNat≤root.rsp.toNat-1008 ∨ root.rsp.toNat+8≤root.r9.toNat)
    (lbl : a.label= (if p.good then .l10160d else .l101611))
    (basicR : Atom.All fnCode a.arguments a.store (basic (wframe root p total)))
    (data : p.good=true → memLoad a.store root.r9 (8*p.n.toNat)=p.dst)
    (outLow : p.good=true → 0<p.n.toNat → root.r9.toNat+p.n.toNat≤2^32) : Runs a (Completed p root total) := by
  have low := (show Readable m root.rsp 8 by unpack_atoms abi []; assumption).low
  let ef := {root with original:=a.store,low:=root.rsp-1008}
  have kept : Atom.All fnCode a.arguments a.store (savedABI root) := by
    apply ChaChaRound.keepFrame _ (skipEmpty frame) abi
    intro t ht
    simp only [savedABI,List.mem_cons,List.not_mem_nil,or_false] at ht
    rcases ht with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals try trivial
    all_goals cases hg : p.good
    all_goals try have os := out hg
    all_goals simp [ChaChaRound.pass,Outside,tailFoot,hg,List.mem_filter] <;> bv_omega
  have retE : a.label=(Wrapper.returnFn p.good).entry := by cases h : p.good <;> simpa [h,Wrapper.returnFn,leafSpec,Wrapper.returnCore] using lbl
  have ready : Atom.All fnCode a.arguments a.store ((Wrapper.returnFn p.good).abi ef ++ (Wrapper.returnFn p.good).pre ef) := by
    unpack_atoms kept []
    unpack_atoms basicR []
    join_atoms [ef]
    all_goals first | assumption | bv_omega
  obtain ⟨o,run,ret,atoms,writes⟩ := Wrapper.returnCorrect p.good ef a retE ready (.refl _ _)
  obtain ⟨ao,status,_⟩ := (Atom.all_append _ _).1 atoms
  have re : ef.region=⟨root.rsp.toNat-1008,1008⟩ := by simp [ef,Activation.region]; bv_omega
  have sf : RamWriteFrame a.store o.store [⟨root.rsp.toNat-1008,1008⟩] := re ▸ writes
  refine ⟨o,run,⟨⟨ret,ao,?_⟩,status,?_⟩⟩
  · have init : RegionsWithin (root.region :: commonFoot p total) (root.region :: resultFoot p total root.r9) := by
      intro z hz
      exact ⟨z,match List.mem_cons.mp hz with
        | .inl e => e ▸ .head _
        | .inr h => .tail _ (List.mem_append_left _ h),Nat.le_refl _,Nat.le_refl _⟩
    apply ((widen base init).trans frame _).trans sf
    · simp [RegionsWithin,Activation.region,resultFoot,commonFoot]; omega
    · cases hg : p.good <;> simp [RegionsWithin,Activation.region,resultFoot,commonFoot,tailFoot,hg] <;> omega
  · intro hg
    by_cases pos : 0<p.n.toNat
    · apply (sf.memLoad_eq _).trans (data hg)
      have sl := outLow hg pos
      have os := out hg pos
      simp [Outside]; omega
    · have z : 8*p.n.toNat=0 := by omega
      exact (show ∀ (u v : BitVec (8*p.n.toNat)), u=v by rw [z]; exact fun _ _ => Subsingleton.elim _ _) _ _

end ChaCha20Poly1305.Proofs.Decrypt.Wrapper
