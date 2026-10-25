/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration
public import RegularityStructures.Abstract.Integration.Realising.Reg
public import RegularityStructures.Abstract.Polynomial.Model.Reg
public import RegularityStructures.Abstract.Model

/-!
# Models realising a kernel for an abstract integration map

[Hai14, Definition 5.9, Remark 5.10]: a model `(Π, Γ)` realises `K` for `I` if
`Π_x I a = ∫ K(·, z) (Π_x a)(dz) - Π_x J(x) a`; rigorously
`(Π_x I a)(ψ) = ∑_n ∫ ψ(y) (Π_x a)(K^α_{n;xy}) dy`. With distributions recorded as `Q`-families,
for the basis vectors `e_i` of the sector `V` of degree `deg i < γ` this reads

  `(Q_t Π_x I e_i)(z) = realReg M N x i t z = ∫ Q_t(z, y) g_{x,i}(y) dy`,

with `K_n = annShell N n` (`RealisesKernel`). The polynomial part of Definition 5.9 (and
Assumption 5.3) is a separate predicate `IsPolyCompatible`: `Π_x X^k = (· - x)^k`, recorded as the
`Q`-family `polyReg`. `IsRealising` is their conjunction.
-/

@[expose] public section

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

namespace Model

/-- `Π_x X^k = (· - x)^k` for the abstract polynomials of `P` [Hai14, Assumption 5.3]: the
regularisations of `Π_x e_{P.emb k}` are those of the polynomial `(· - x)^k`. -/
def IsPolyCompatible (M : Model 𝒯 parabolicSemigroup) {N' : ℕ} (P : PolynomialSector 𝒯 N') :
    Prop :=
  ∀ (x : ParabolicSpace) (k : PolyIndex N') (t : ℝ) (z : ParabolicSpace),
    M.regPi x (Pi.single (P.emb k) 1) t z = polyReg x (Pi.single k 1) t z

end Model

end RegularityStructures

end
