/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.JMapLinear
public import RegularityStructures.Abstract.Model
public import RegularityStructures.Analysis.Kernel.ParabolicSemigroup

/-!
# Hairer's Lemma 5.16: `Γ_{xy}` commutes with `I + J`

[Hai14, Lemma 5.16]: for a model realising `K` for `I` (and compatible with the polynomials),
`Γ_{xy} (I + J(y)) e_i = (I + J(x)) Γ_{xy} e_i`, i.e.

  `M.gammaMap x y (I e_i + jMap M N P y e_i) = I (M.gammaMap x y e_i) + jMap M N P x (M.gammaMap x y e_i)`
  (`gammaMap_integral_add_jMap`).

Proof (Hairer's, in the `Q`-family setting): the difference `D` lies in `T̄` (`IΓ - ΓI ∈ T̄` by the
abstract integration field `comm`, `J` takes values in `T̄`, `Γ` preserves `T̄`), and
`Q_t Π_x D = Q_t K ∗ Π_y e_i - ∑_j (Γ_{xy} e_i)_j Q_t K ∗ Π_x e_j = 0` by `regPi_integral_add_jMap` and
linearity of `kConv`, using `Π_x Γ_{xy} = Π_y`. Since `Π_x` is injective on `T̄`
(`eq_zero_of_regPi_eq_zero`), `D = 0`.

Extra hypotheses beyond the statement of the lemma: the components `e_j`, `deg j < γ`, of
`Γ_{xy} e_i ∈ V` that occur must themselves lie in `V` (`hVb`: `V` is spanned by basis vectors),
since `RealisesKernel` is only recorded on basis vectors; and `hN'` holds for every `j` with
`deg j < γ`.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {𝒯 : RegularityStructure ι} {N' : ℕ}

namespace Model

variable {M : Model 𝒯 parabolicSemigroup}

theorem regPi_finsetSum_smul (x : ParabolicSpace) {J : Type*} (s : Finset J) (c : J → ℝ)
    (τ : J → ι → ℝ) (t : ℝ) (z : ParabolicSpace) :
    M.regPi x (∑ j ∈ s, c j • τ j) t z = ∑ j ∈ s, c j * M.regPi x (τ j) t z := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have := M.regPi_smul x 0 (0 : ι → ℝ) t z
    simpa using this
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, M.regPi_add, M.regPi_smul, ih]

end Model

end RegularityStructures

end
