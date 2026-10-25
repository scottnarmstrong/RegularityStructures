/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Statements.Defs.IsContinuousRandomModelWithFieldsOn
public import RegularityStructures.Probability.ModelKolmogorovNorm
public import Mathlib.Probability.Notation

/-!
# The Kolmogorov bound for the model norms as a proposition

The statement of the Kolmogorov bound for the model norms (`Statements.kolmogorov_modelNorm`,
the analogue of [Hai14, Theorem 10.7]) copied verbatim as a closed proposition, universes explicit
(`v` for the index type, `u` for the probability space).
-/

@[expose] public section

universe u v

set_option linter.unusedVariables false

namespace RegularityStructures.Phi43

def KolmogorovModelNormStatement : Prop :=
  ∀ {ι : Type v} [Fintype ι] [DecidableEq ι]
    (𝒯 : RegularityStructures.RegularityStructure ι) (γ κbar θ : ℝ) (hκbar : 0 < κbar)
    (hθ : 0 ≤ θ) (Dπ : Set ι) (DΓ : Set (ι × ι)) (S : Set RegularityStructures.ParabolicSpace)
    (hS : IsCompact S) (p : ℕ) (hp : 1 ≤ p),
  ∃ q : ℕ, p ≤ q ∧ ∀ Cbar : ℝ, ∃ K : ℝ, 0 ≤ K ∧
    ∀ {Ω : Type u} [MeasurableSpace Ω] (P : MeasureTheory.Measure Ω)
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
      ∫⁻ ω, (Z₁ ω).diffNormOn (Z₂ ω) γ S ^ p ∂P ≤ ENNReal.ofReal (K * (C * ε ^ θ) ^ p)

end RegularityStructures.Phi43

end
