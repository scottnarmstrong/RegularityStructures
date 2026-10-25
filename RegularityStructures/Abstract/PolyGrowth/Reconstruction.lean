/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Model

/-!
# The reconstruction theorem for models of polynomial growth

Stationary random models are not globally bounded: `sup_x |(Q_t Π_x e_i)(x)| = ∞`. They satisfy
the weighted bound `|(Q_t Π_x e_i)(x)| ≤ C_Π ρ(x) t^{deg i/ℓ}` for a polynomially moderate weight
`ρ ≥ 1` (`ρ(z) ≤ ρ(y)(1 + d(z, y))^p`), as in [Hos25, Definition 3.2] with weight `w = 1/ρ`.
For such a model and `f ∈ D^γ` (`γ > 0`) the reconstruction `Rf` exists, is unique, and
`|(Q_t (Rf − Π_x f(x)))(x)| ≤ c C_Π C_f ρ(x) t^{γ/ℓ}` (`Model.abs_reconstruct_sub_le_growth`),
with `c` depending only on `𝒯`, `K`, `p` and `γ`. Here only the model is weighted; for
stationary random models the modelled distributions must be weighted too, which is done in
the weighted multilevel Schauder estimate
(`RegularityStructures.Abstract.Integration.Growth`).

Source: [Hos25] = arXiv:2310.07396v2, Definitions 2.1, 3.2 and Theorem 4.1.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E]
  {μ : Measure E}

namespace Model

variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ}

/-- The weighted model bound `|(Q_t Π_x e_i)(x)| ≤ C ρ(x) t^{deg i/ℓ}` for `deg i < γ`,
`0 < t ≤ 1`. -/
def PiBoundGrowth (M : Model 𝒯 K) (γ C : ℝ) (ρ : E → ℝ) : Prop :=
  ∀ i, 𝒯.deg i < γ → ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x,
    |M.regPi x (Pi.single i 1) t x| ≤ C * ρ x * t ^ (𝒯.deg i / K.order)

end Model

end RegularityStructures

end

public section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E]
  {μ : Measure E}

namespace Model

variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ} (M : Model 𝒯 K)

theorem PiBoundOn.piBoundGrowth {γ C : ℝ} (h : M.PiBoundOn γ C univ) :
    M.PiBoundGrowth γ C (fun _ => 1) :=
  fun i hi t ht x => by simpa using h i hi t ht x (mem_univ x)

end Model

end RegularityStructures

end
