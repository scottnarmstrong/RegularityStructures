/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Statements.Defs.IsContinuousRandomModelWithFieldsOn
public import RegularityStructures.Probability.ModelKolmogorovNorm
public import Mathlib.Probability.Notation
public import RegularityStructures.Probability.ModelKolmogorov

/-!
# Moments of model norms from moments of the regularised model

A Kolmogorov criterion for random models, for model norms in the semigroup form of [Hos25]. Let
`Z₁`, `Z₂` be random models of a regularity structure that are continuous on a compact set `S` and
whose regularised fields are continuous on the whole space
(`IsContinuousRandomModelWithFieldsOn`). Suppose that, uniformly in the base points and in
`t ∈ (0, 1]`, the `q`-th moments of the regularised realisations `(Q_t Π_x e_i)(x)` and of the
entries of `Γ_{yx}` obey the scaling bounds with a gain `κ̄ > 0`, and those of the differences
the same bounds with an extra factor `ε^θ`. The components in given sets `Dπ`, `DΓ`, for instance
the polynomial ones, may instead obey the bounds pathwise. Then the `p`-th moments of the local
model norm `‖Zₖ‖_{γ;S}` and of the distance `‖Z₁; Z₂‖_{γ;S}` are bounded by `K C^p` and
`K (C ε^θ)^p`.

This is the analogue of [Hai14, Theorem 10.7], whose proof rests on the bound of
[Hai14, Proposition 3.32]. In the proof of Theorem A it turns the moment bounds for the
regularised trees of the Φ⁴₃ structure into moment bounds for the model norms. These give the
convergence of the BPHZ models, and through it the convergence of the models renormalised with
the constants of the statement.

The proof is `RegularityStructures.kolmogorov_modelNorm`,
in the module `RegularityStructures.Probability.ModelKolmogorov`.

Source: [Hai14, Theorem 10.7, Proposition 3.32]; [Hos25].
-/

public section

namespace RegularityStructures.Phi43

/-- **Kolmogorov criterion for random models.** Given `p ≥ 1` there is a moment order
`q ≥ p`, and for every bound `Cbar` a constant `K ≥ 0`, with the following property. Let `Z₁`, `Z₂`
be random models with `IsContinuousRandomModelWithFieldsOn` on the compact set `S`, and let
`0 ≤ C ≤ Cbar` and `ε ≥ 0`. For components of degree below `γ`, assume the following.
* For `i ∈ Dπ` and `(i, j) ∈ DΓ`, pathwise: `|(Q_t Π_x e_i)(x)| ≤ C t^{|i|/ℓ}` and
  `|(Γ_{yx} e_i)_j| ≤ C d(y, x)^{|i| - |j|}`. The differences of the two models obey the same
  bounds with `C ε^θ` in place of `C`.
* For the other components, in `L^q`: `E|(Q_t Π_x e_i)(x)|^q ≤ (C t^{(|i| + κ̄)/ℓ})^q` and
  `E|(Γ_{yx} e_i)_j|^q ≤ (C d(y, x)^{|i| - |j| + κ̄})^q`. The differences obey the same bounds
  with `C ε^θ` in place of `C`.

These hold uniformly in `x`, `y` and `t ∈ (0, 1]`. Then the norms are measurable,
`E ‖Zₖ‖_{γ;S}^p ≤ K C^p` for `k = 1, 2`, and `E ‖Z₁; Z₂‖_{γ;S}^p ≤ K (C ε^θ)^p`. The order `q`
depends only on the data before it, and `K` may also depend on `Cbar`. -/
theorem Statements.kolmogorov_modelNorm {ι : Type*} [Fintype ι] [DecidableEq ι]
    (𝒯 : RegularityStructures.RegularityStructure ι) (γ κbar θ : ℝ) (hκbar : 0 < κbar)
    (hθ : 0 ≤ θ) (Dπ : Set ι) (DΓ : Set (ι × ι)) (S : Set RegularityStructures.ParabolicSpace)
    (hS : IsCompact S) (p : ℕ) (hp : 1 ≤ p) :
    ∃ q : ℕ, p ≤ q ∧ ∀ Cbar : ℝ, ∃ K : ℝ, 0 ≤ K ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
      [MeasureTheory.IsProbabilityMeasure P]
      (Z₁ Z₂ : Ω → RegularityStructures.Model 𝒯 RegularityStructures.parabolicSemigroup)
      (C ε : ℝ), 0 ≤ C → C ≤ Cbar → 0 ≤ ε →
      RegularityStructures.IsContinuousRandomModelWithFieldsOn Z₁ S →
      RegularityStructures.IsContinuousRandomModelWithFieldsOn Z₂ S →
      (∀ Z ∈ ({Z₁, Z₂} : Set (Ω → RegularityStructures.Model 𝒯
          RegularityStructures.parabolicSemigroup)),
        ∀ i ∈ Dπ, 𝒯.deg i < γ → ∀ ω, ∀ t ∈ Set.Ioc (0 : ℝ) 1,
          ∀ x : RegularityStructures.ParabolicSpace,
          |(Z ω).regPi x (Pi.single i 1) t x| ≤
            C * t ^ (𝒯.deg i / RegularityStructures.parabolicSemigroup.order)) →
      (∀ i ∈ Dπ, 𝒯.deg i < γ → ∀ ω, ∀ t ∈ Set.Ioc (0 : ℝ) 1,
          ∀ x : RegularityStructures.ParabolicSpace,
          |(Z₁ ω).regPi x (Pi.single i 1) t x - (Z₂ ω).regPi x (Pi.single i 1) t x| ≤
            C * ε ^ θ * t ^ (𝒯.deg i / RegularityStructures.parabolicSemigroup.order)) →
      (∀ Z ∈ ({Z₁, Z₂} : Set (Ω → RegularityStructures.Model 𝒯
          RegularityStructures.parabolicSemigroup)),
        ∀ i j, (i, j) ∈ DΓ → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i → ∀ ω,
          ∀ x y : RegularityStructures.ParabolicSpace,
          |(Z ω).gammaMap y x (Pi.single i 1) j| ≤
            C * RegularityStructures.parabolicSemigroup.scaleDist y x ^ (𝒯.deg i - 𝒯.deg j)) →
      (∀ i j, (i, j) ∈ DΓ → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i → ∀ ω,
          ∀ x y : RegularityStructures.ParabolicSpace,
          |(Z₁ ω).gammaMap y x (Pi.single i 1) j - (Z₂ ω).gammaMap y x (Pi.single i 1) j| ≤
            C * ε ^ θ *
              RegularityStructures.parabolicSemigroup.scaleDist y x ^ (𝒯.deg i - 𝒯.deg j)) →
      (∀ Z ∈ ({Z₁, Z₂} : Set (Ω → RegularityStructures.Model 𝒯
          RegularityStructures.parabolicSemigroup)),
        ∀ i, i ∉ Dπ → 𝒯.deg i < γ → ∀ t ∈ Set.Ioc (0 : ℝ) 1,
          ∀ x : RegularityStructures.ParabolicSpace,
          ∫⁻ ω, ‖(Z ω).regPi x (Pi.single i 1) t x‖ₑ ^ q ∂P ≤
            ENNReal.ofReal
              (C * t ^ ((𝒯.deg i + κbar) / RegularityStructures.parabolicSemigroup.order)) ^ q) →
      (∀ i, i ∉ Dπ → 𝒯.deg i < γ → ∀ t ∈ Set.Ioc (0 : ℝ) 1,
          ∀ x : RegularityStructures.ParabolicSpace,
          ∫⁻ ω, ‖(Z₁ ω).regPi x (Pi.single i 1) t x -
              (Z₂ ω).regPi x (Pi.single i 1) t x‖ₑ ^ q ∂P ≤
            ENNReal.ofReal (C * ε ^ θ *
              t ^ ((𝒯.deg i + κbar) / RegularityStructures.parabolicSemigroup.order)) ^ q) →
      (∀ Z ∈ ({Z₁, Z₂} : Set (Ω → RegularityStructures.Model 𝒯
          RegularityStructures.parabolicSemigroup)),
        ∀ i j, (i, j) ∉ DΓ → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i →
          ∀ x y : RegularityStructures.ParabolicSpace,
          ∫⁻ ω, ‖(Z ω).gammaMap y x (Pi.single i 1) j‖ₑ ^ q ∂P ≤
            ENNReal.ofReal (C * RegularityStructures.parabolicSemigroup.scaleDist y x ^
              (𝒯.deg i - 𝒯.deg j + κbar)) ^ q) →
      (∀ i j, (i, j) ∉ DΓ → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i →
          ∀ x y : RegularityStructures.ParabolicSpace,
          ∫⁻ ω, ‖(Z₁ ω).gammaMap y x (Pi.single i 1) j -
              (Z₂ ω).gammaMap y x (Pi.single i 1) j‖ₑ ^ q ∂P ≤
            ENNReal.ofReal (C * ε ^ θ * RegularityStructures.parabolicSemigroup.scaleDist y x ^
              (𝒯.deg i - 𝒯.deg j + κbar)) ^ q) →
      (∀ Z ∈ ({Z₁, Z₂} : Set (Ω → RegularityStructures.Model 𝒯
          RegularityStructures.parabolicSemigroup)),
        AEMeasurable (fun ω => (Z ω).normOn γ S) P ∧
          ∫⁻ ω, (Z ω).normOn γ S ^ p ∂P ≤ ENNReal.ofReal (K * C ^ p)) ∧
      AEMeasurable (fun ω => (Z₁ ω).diffNormOn (Z₂ ω) γ S) P ∧
      ∫⁻ ω, (Z₁ ω).diffNormOn (Z₂ ω) γ S ^ p ∂P ≤ ENNReal.ofReal (K * (C * ε ^ θ) ^ p) :=
  by exact RegularityStructures.kolmogorov_modelNorm 𝒯 γ κbar θ hκbar hθ Dπ DΓ S hS p hp

end RegularityStructures.Phi43

end
