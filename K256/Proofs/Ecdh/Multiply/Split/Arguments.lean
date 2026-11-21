import K256.Proofs.Ecdh.Multiply.Split.Memory

namespace K256.Proofs.Generate.Generator.Multiply.Split.Caller

open K256.Spec.Program Prelude X86.Machine X86.UserProcess X86Proofs K256.Proofs.CFG
  K256.Proofs.Lift K256.Proofs.Refine K256.Proofs.Generate.LIR
  Standards.SECG.DomainParameters.Secp256k1
open K256.Proofs.Generate.Curve

variable {fr : Activation} {a : Registers} {d : Nat} {peer : Projective} {m : Ram}

private theorem Operand.of_slot (k : Site) (e : PeerCoreEntry fr a d peer) {i v : Nat}
    (h : i+32 ≤ 9500) (sep : i+32 ≤ k.dest ∨ k.dest+32 ≤ i)
    (read : Readable m (slot fr i) 32) (words : WordsAt m (slot fr i) 64 (scalarWords v)) :
    Operand k fr m (slot fr i) v := by
  have := k.bounds
  have := e.room
  have := peerSpNat e
  have := peerPushNat e
  have := peerSlotNat e i (by omega)
  have := peerSlotNat e k.dest (by omega)
  exact ⟨words,read,Or.inr (by omega),by omega⟩

private theorem Operand.of_scalar (k : Site) (e : PeerCoreEntry fr a d peer) (f : RamWriteFrame fr.original m [fr.region]) :
    Operand k fr m (fr.rsi+120) d := by
  have := k.bounds
  have := e.room
  have := e.high
  have := peerSpNat e
  have := peerSlotNat e 3576 (by decide)
  have := peerLowNat e
  have addr := peerScalarAddress e
  rw [addr]
  apply Operand.of_slot k e (by decide) (Or.inr (by omega))
  · have source := e.pairRead.of_frame f
    rw [← addr]
    apply source.sub
    all_goals rw [BitVec.toNat_add_of_lt (by have := source.low; change fr.rsi.toNat + 120 < 2^64; omega)]
    all_goals simp only [BitVec.reduceToNat] <;> omega
  · rw [← addr]
    apply WordsAt.of_frame e.scalar f (by decide)
    refine ⟨by rw [addr]; change _ + 32 ≤ 2^64; omega,?_⟩
    intro r hr
    obtain rfl := List.mem_singleton.mp hr
    right
    dsimp only [Activation.region]
    rw [addr]
    omega

private theorem Operand.of_local (k : Site) (e : PeerCoreEntry fr a d peer) (s : StackAccess fr m)
    (words : ScalarsAt fr m (k.before d)) {i v : Nat} (h : (i,v) ∈ k.before d) :
    Operand k fr m (slot fr i) v := by
  obtain ⟨hi,sep⟩ := k.before_apart d h
  exact Operand.of_slot k e (i := i) (by change i+32 ≤ 3256 at hi; omega) sep
    (peerSlotWrite e s (i := i) (n := 32) hi).readable (words (i,v) h)

private theorem Operand.of_parameter (k : Site) (e : PeerCoreEntry fr a d peer) (s : StackAccess fr m)
    (loaded : ∀ z ∈ Extracted.programImage, m[z.1]? = some z.2) {p : BitVec 64} {v : Nat}
    (par : (p,v) ∈ parameters) : Operand k fr m p v := by
  have := k.bounds
  have := e.room
  have := peerSpNat e
  have := peerPushNat e
  have := peerStackBelowNat e (off := 8 + k.window) (by omega)
  have u := parameterAt loaded par
  have sep := u.apart (peerStackBelowWrite e s (off := 8+k.window) (by omega)) (by omega)
  exact ⟨u.words,u.readable,by omega,u.apart (peerSlotWrite e s k.bounds.1) (by decide)⟩

theorem peerOperands (k : Site) (e : PeerCoreEntry fr a d peer) (f : RamWriteFrame fr.original m [fr.region])
    (loaded : ∀ z ∈ Extracted.programImage, m[z.1]? = some z.2)
    (old : ScalarsAt fr m (k.before d)) (p : Registers) :
    Operand k fr m (k.child fr p).rsi (k.x d) ∧ Operand k fr m (k.child fr p).rdx (k.y d) := by
  have s := peerStackAccess e f
  cases k with
  | roundFirst =>
    constructor
    · exact Operand.of_scalar .roundFirst e f
    · exact Operand.of_parameter .roundFirst e s loaded (p := 0x202200) (v := g1) (by decide +kernel)
  | mulFirst =>
    constructor
    · exact Operand.of_local .mulFirst e s old (List.mem_cons_self ..)
    · exact Operand.of_parameter .mulFirst e s loaded (p := 0x202220) (v := minusB1) (by decide +kernel)
  | roundSecond =>
    constructor
    · exact Operand.of_scalar .roundSecond e f
    · exact Operand.of_parameter .roundSecond e s loaded (p := 0x202240) (v := g2) (by decide +kernel)
  | mulSecond =>
    constructor
    · exact Operand.of_local .mulSecond e s old (List.mem_cons_self ..)
    · exact Operand.of_parameter .mulSecond e s loaded (p := 0x202260) (v := minusB2) (by decide +kernel)
  | addSecond =>
    constructor
    · exact Operand.of_local .addSecond e s old (List.mem_cons_of_mem _ (List.mem_cons_self ..))
    · exact Operand.of_local .addSecond e s old (List.mem_cons_self ..)
  | mulLambda =>
    constructor
    · exact Operand.of_local .mulLambda e s old (List.mem_cons_self ..)
    · exact Operand.of_parameter .mulLambda e s loaded (p := 0x202280) (v := domain.n - eigenvalue) (by decide +kernel)
  | addFirst =>
    constructor
    · exact Operand.of_scalar .addFirst e f
    · exact Operand.of_local .addFirst e s old (List.mem_cons_self ..)

end K256.Proofs.Generate.Generator.Multiply.Split.Caller
