/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Model

/-!
# The germ of a modelled distribution

For a model `M = (Π, Γ)` and `f ∈ D^γ`, the germ `F_y = Π_y f(y)` ([Hos25, proof of Theorem
4.1]; a coherent germ in the sense of [CZ20, Definition 4.1]) has regularisations
`(Q_t F_y)(z) = (Q_t Π_y f(y))(z)`. The algebraic relation `Π_y = Π_z Γ_{zy}` gives

  `(Q_t (F_y − F_z))(z) = (Q_t Π_z (Γ_{zy} f(y) − f(z)))(z)`,

and the model and `D^γ` bounds give the coherence bound
`|(Q_t (F_y − F_z))(z)| ≤ |ι| C_Π C_f ∑_{a ∈ A} t^{a/ℓ} d(z, y)^{γ−a}`, `A = {deg i < γ}`
(`isCoherent_germ`). For two models, the difference germ `Π¹ f¹ − Π² f²` is coherent with
constant `|ι| (C_{f¹} ‖Π¹ − Π²‖ + ‖Π²‖ |||f¹; f²|||)` (`isCoherent_germ_sub`).

Sources: [Hos25] = arXiv:2310.07396v2, §4, step (1); [CZ20] = arXiv:2005.09287v3.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E]
  {μ : Measure E}

namespace Model

variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ} (M : Model 𝒯 K)

/-- For `τ ∈ T_{<γ}`, `(Q_t Π_x τ)(z) = ∑_{deg j < γ} τ_j (Q_t Π_x e_j)(z)`. -/
theorem regPi_eq_sum_filter {γ : ℝ} {τ : ι → ℝ} (hτ : τ ∈ lowerSubspace 𝒯.deg γ) (x : E)
    (t : ℝ) (z : E) :
    M.regPi x τ t z =
      ∑ j ∈ Finset.univ.filter (fun j => 𝒯.deg j < γ), τ j * M.regPi x (Pi.single j 1) t z := by
  rw [M.regPi_eq_sum, Finset.sum_filter]
  refine Finset.sum_congr rfl fun j _ => ?_
  split_ifs with hj
  · rfl
  · rw [hτ j (not_lt.1 hj), zero_mul]

end Model

end RegularityStructures

end
