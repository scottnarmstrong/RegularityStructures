/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Integration.Growth.Setting
public import RegularityStructures.Abstract.Model

/-!
# Weighted difference bounds of two models

Weighted versions of `Model.PiDiffBoundOn`, `Model.GammaDiffBoundOn`:

* `Model.PiDiffBoundGrowth M₁ M₂ γ C ρ`:
  `|Q_t (Π¹_x − Π²_x) e_i (x)| ≤ C ρ(x) t^{deg i/ℓ}` for `deg i < γ`, `0 < t ≤ 1`;
* `Model.GammaDiffBoundGrowth M₁ M₂ γ C ρ q`:
  `|((Γ¹_{yx} − Γ²_{yx}) e_i)_j| ≤ C ρ(x) (1 + d(y, x))^q d(y, x)^{deg i − deg j}` for
  `deg j < deg i < γ`;
* window forms on `timeWindow8` (`Model.PiDiffBoundGrowth.abs_le_of_window8`,
  `Model.GammaDiffBoundGrowth.abs_le_of_window8`), as for a single model.
-/

@[expose] public section

open MeasureTheory Set

namespace RegularityStructures

namespace Model

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E]
  {μ : Measure E} {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ}

/-- The weighted `Π`-difference bound `|(Q_t (Π¹_x − Π²_x) e_i)(x)| ≤ C ρ(x) t^{deg i/ℓ}`. -/
def PiDiffBoundGrowth (M₁ M₂ : Model 𝒯 K) (γ C : ℝ) (ρ : E → ℝ) : Prop :=
  ∀ i, 𝒯.deg i < γ → ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x,
    |M₁.regPi x (Pi.single i 1) t x - M₂.regPi x (Pi.single i 1) t x| ≤
      C * ρ x * t ^ (𝒯.deg i / K.order)

/-- The weighted `Γ`-difference bound
`|((Γ¹_{yx} − Γ²_{yx}) e_i)_j| ≤ C ρ(x) (1 + d(y, x))^q d(y, x)^{deg i − deg j}`. -/
def GammaDiffBoundGrowth (M₁ M₂ : Model 𝒯 K) (γ C : ℝ) (ρ : E → ℝ) (q : ℝ) : Prop :=
  ∀ i j, 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i → ∀ x y,
    |M₁.gammaMap y x (Pi.single i 1) j - M₂.gammaMap y x (Pi.single i 1) j| ≤
      C * ρ x * (1 + K.scaleDist y x) ^ q * K.scaleDist y x ^ (𝒯.deg i - 𝒯.deg j)

end Model

end RegularityStructures

end

