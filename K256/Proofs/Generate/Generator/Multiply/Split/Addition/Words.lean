import K256.Proofs.Generate.Generator.Multiply.Split.WideProduct
import K256.Proofs.Common.Invert.LinearCombination.Wide

namespace K256.Proofs.Generate.Generator.Multiply.Split.Addition

open X86Proofs Common.Invert.LinearCombination Standards.SECG.DomainParameters.Secp256k1

abbrev Words := Vector (BitVec 64) 4

def flagWord (b : Bool) : BitVec 64 := if b then 1 else 0

def sum (x y : Words) : Limbs × BitVec 64 :=
  let l := addSpec y[0] x[0]
  let t := adcSpec l.2.CF x[1] 0
  let u := addSpec y[2] x[2]
  let v := addSpec y[3] x[3]
  let s := addSpec t.1 y[1]
  let m := adcSpec s.2.CF u.1 (flagWord t.2.CF)
  let h := adcSpec m.2.CF (flagWord u.2.CF) v.1
  (⟨l.1,s.1,m.1,h.1⟩, (adcSpec h.2.CF (flagWord v.2.CF) 0).1)

def selectWord (s d k : BitVec 64) : BitVec 64 := (-k &&& (s ^^^ d)) ^^^ d

def addWords (x y p : Words) : Words :=
  let s := sum x y
  let d := subRaw s.1 ⟨p[0], p[1], p[2], p[3]⟩
  let k := flagWord (s.2 == 0) &&& -d.2
  #v[selectWord s.1.l0 d.1.l0 k, selectWord s.1.l1 d.1.l1 k,
     selectWord s.1.l2 d.1.l2 k, selectWord s.1.l3 d.1.l3 k]

end K256.Proofs.Generate.Generator.Multiply.Split.Addition
