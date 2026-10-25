/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Singular.KGamma.SupPieces
public import RegularityStructures.Abstract.Model
public import RegularityStructures.Abstract.Singular.KGamma.Defs
public import RegularityStructures.Analysis.Heat.Annihilating.Scaled
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup
public import RegularityStructures.Analysis.Semigroup.Pairing.Basic

/-!
# The term of scale `n` in the `X^k` coefficient of `𝒦_γ f`

`shellTerm M h f x k n = ⟨R f − Π_x f(x), D^k K_n(x − ·)⟩ + ∑_{|k| < deg i + 2} f(x)_i ⟨Π_x e_i, D^k K_n(x − ·)⟩`
is the `n`-th term of `k! (𝒦_γ f(x))_{X^k}` (`nCoeffS` plus the `J`-part).  For `x` in the slab
(`w = ‖x‖_P`, `t = 2^n w`, `ηK = α ∧ η + 2`, `|k| < γ + 2`, `|k| ≠ deg i + 2` for the relevant `i`)
we prove `|shellTerm| ≤ C K₀ C_f w^{ηK − |k|} min (t^a) (t^{-b})` for some `a, b > 0` depending only on
`𝒯, γ, η, α, k`: this is the two-regime estimate of [Hai14, Prop. 6.16] (sup part).
-/

@[expose] public noncomputable section

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι}

namespace Model

/-- The `n`-th term of `k! (𝒦_γ f(x))_{X^k}`: the singular shell pairing plus the `J`-terms of
`i` with `|k| < deg i + 2`. -/
def shellTerm (M : Model 𝒯 parabolicSemigroup) (h : ParabolicSpace → ℝ)
    (f : ParabolicSpace → ι → ℝ) (x : ParabolicSpace) (k : Fin 4 →₀ ℕ) (n : ℕ) : ℝ :=
  M.singShellPairing h f x k n +
    ∑ i ∈ Finset.univ.filter (fun i => (multiDeg k : ℝ) < 𝒯.deg i + 2), f x i *
      parabolicSemigroup.pairing (M.regPi x (Pi.single i 1))
        (fun y => lineIter (multiDirs k) (scaledShell h n) (x - y))

end Model

end RegularityStructures

end

