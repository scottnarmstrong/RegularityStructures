/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Abstract.Model
public import RegularityStructures.Abstract.PolyGrowth.Reconstruction
public import RegularityStructures.Analysis.Semigroup.Weighted.Defs

/-!
# The weighted hypotheses of the multilevel Schauder estimate

For stationary random models only weighted bounds hold. We use polynomially moderate weights
`ρ ≥ 1` (`IsModerateWeight ρ p`: `ρ z ≤ ρ y (1 + d(z, y))^p`) and the bounds

* `Model.PiBoundGrowth γ C ρP`: `|(Q_t Π_x e_i)(x)| ≤ C ρP(x) t^{deg i/ℓ}`;
* `Model.GammaBoundGrowth γ C ρG q`:
  `|(Γ_{yx} e_i)_j| ≤ C ρG(x) (1 + d(y, x))^q d(y, x)^{deg i − deg j}` for `deg j < deg i < γ`.

`Model.GrowthModel` bundles these bounds for a model `M`, with weights `ρP, ρG` moderate with the
same exponent `p`. The assumptions that do not involve the weights (`IsRealising`,
`IsAbstractIntegration`, degree conditions) are kept separate.

Source: [Hos25] = arXiv:2310.07396v2, Definitions 3.2, 3.5; [Hai14] = arXiv:1303.5113v4, §5.
-/

@[expose] public noncomputable section

open MeasureTheory Set

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {E : Type*} [MeasurableSpace E]
  {μ : Measure E}

namespace Model

variable {𝒯 : RegularityStructure ι} {K : RegularisingSemigroup E μ}

/-- The weighted structure-group bound `|(Γ_{yx} e_i)_j| ≤ C ρG(x) (1 + d(y, x))^q d(y, x)^{deg i − deg j}`
for `deg j < deg i < γ`. -/
def GammaBoundGrowth (M : Model 𝒯 K) (γ C : ℝ) (ρ : E → ℝ) (q : ℝ) : Prop :=
  ∀ i j, 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i → ∀ x y,
    |M.gammaMap y x (Pi.single i 1) j| ≤
      C * ρ x * (1 + K.scaleDist y x) ^ q * K.scaleDist y x ^ (𝒯.deg i - 𝒯.deg j)

/-- The standing weighted hypotheses on a model `M`: `γ > 0`, moderate weights `ρP, ρG` with
exponent `p`, and the bounds `PiBoundGrowth`, `GammaBoundGrowth` (with growth exponent `qG ≥ 0`). -/
structure GrowthModel (M : Model 𝒯 K) (γ CPi CGam : ℝ) (ρP ρG : E → ℝ) (p qG : ℝ) : Prop where
  pos : 0 < γ
  moderateP : K.IsModerateWeight ρP p
  moderateG : K.IsModerateWeight ρG p
  nonnegG : 0 ≤ qG
  piBound : M.PiBoundGrowth γ CPi ρP
  gammaBound : M.GammaBoundGrowth γ CGam ρG qG
  piBound_nonneg : 0 ≤ CPi

end Model

end RegularityStructures

end
