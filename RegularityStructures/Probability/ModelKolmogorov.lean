/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Statements.Defs.IsContinuousRandomModelWithFieldsOn
public import RegularityStructures.Probability.ModelKolmogorovNorm
public import Mathlib.Probability.Notation
public import RegularityStructures.Probability.ModelKolmogorovHalvesAssembly
public import RegularityStructures.Probability.ModelKolmogorovPiHalfAssembly
public import RegularityStructures.Probability.ModelKolmogorovGammaSplitCompact
public import RegularityStructures.Probability.ModelKolmogorovGammaDiffInduction

/-!
# Moments of model norms from moments of the regularised model

A Kolmogorov criterion for random models, the analogue of [Hai14, Theorem 10.7] for model norms in
the semigroup form of [Hos25]: `kolmogorov_modelNorm`. The proof of Theorem A uses it with exactly
this statement (`Phi43.Statements.kolmogorov_modelNorm`).

The proof assembles the two sector estimates with `kolmogorov_modelNorm_of_halves`: the `Π` half
is `randomModel_piHalf`; the `Γ` half combines `randomModel_gammaNormOn_moment`
(single models) and `randomModel_gammaDiffNormOn_moment` (differences) at the common moment
order `max q₁ q₂`, lowered to each order by `probability_natMoment_le_of_higher`, with the constant
`max K₁ K₂`.

Source: [Hai14, Theorem 10.7, Proposition 3.32]; [Hos25].
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace RegularityStructures

/-- **Kolmogorov criterion for model norms** [Hai14, Theorem 10.7]: moment bounds for the
regularised realisations and the `Γ` entries give `p`-th moment bounds for the local model norms
and their distance. -/
theorem kolmogorov_modelNorm {ι : Type*} [Fintype ι] [DecidableEq ι]
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
      ∫⁻ ω, (Z₁ ω).diffNormOn (Z₂ ω) γ S ^ p ∂P ≤ ENNReal.ofReal (K * (C * ε ^ θ) ^ p) := by
  obtain ⟨qPi, hpPi, KPi, hKPi, hPi⟩ :=
    randomModel_piHalf 𝒯 γ κbar θ hκbar hθ Dπ DΓ S hS p hp
  obtain ⟨q₁, hq₁, hΓ₁⟩ :=
    randomModel_gammaNormOn_moment 𝒯 γ κbar θ hκbar hθ DΓ S hS p hp
  obtain ⟨q₂, hq₂, hΓ₂⟩ :=
    randomModel_gammaDiffNormOn_moment 𝒯 γ κbar θ hκbar hθ DΓ S hS p hp
  choose K₁ hK₁ hΓ₁ using hΓ₁
  choose K₂ hK₂ hΓ₂ using hΓ₂
  have h1 : 1 ≤ q₁ := hp.trans hq₁
  have h2 : 1 ≤ q₂ := hp.trans hq₂
  refine kolmogorov_modelNorm_of_halves 𝒯 γ κbar θ hκbar hθ Dπ DΓ S hS p qPi (max q₁ q₂)
    KPi (fun Cbar => max (K₁ Cbar) (K₂ Cbar)) hp hpPi (hq₁.trans (le_max_left _ _)) hKPi
    (fun Cbar => (hK₁ Cbar).trans (le_max_left _ _)) hPi ?_
  intro Cbar Ω _ P _ Z₁ Z₂ C ε hC hCbar hε hZ₁ hZ₂ hdet hdiffdet hann hdiffann
  have hmem : ∀ Z ∈ ({Z₁, Z₂} : Set (Ω → Model 𝒯 parabolicSemigroup)),
      IsContinuousRandomModelWithFieldsOn Z S := by
    intro Z hZ
    rcases hZ with rfl | hZ
    · exact hZ₁
    · rw [Set.mem_singleton_iff] at hZ
      subst hZ
      exact hZ₂
  refine ⟨fun Z hZ => ?_, ?_⟩
  · have hZc := hmem Z hZ
    obtain ⟨hm, hle⟩ := hΓ₁ Cbar P Z C hC hCbar hZc (hdet Z hZ)
      (fun i j hij hi hj x y => probability_natMoment_le_of_higher
        (hZc.1.2.1 i j x y).aemeasurable h1 (le_max_left q₁ q₂) _ (hann Z hZ i j hij hi hj x y))
    refine ⟨hm, hle.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (pow_nonneg hC p)
  · obtain ⟨hm, hle⟩ := hΓ₂ Cbar P Z₁ Z₂ C ε hC hCbar hε hZ₁ hZ₂ hdet hdiffdet
      (fun Z hZ i j hij hi hj x y => probability_natMoment_le_of_higher
        ((hmem Z hZ).1.2.1 i j x y).aemeasurable h2 (le_max_right q₁ q₂) _
        (hann Z hZ i j hij hi hj x y))
      (fun i j hij hi hj x y => probability_natMoment_le_of_higher
        ((hZ₁.1.2.1 i j x y).sub (hZ₂.1.2.1 i j x y)).aemeasurable h2 (le_max_right q₁ q₂) _
        (hdiffann i j hij hi hj x y))
    refine ⟨hm, hle.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    exact mul_le_mul_of_nonneg_right (le_max_right _ _)
      (pow_nonneg (mul_nonneg hC (Real.rpow_nonneg hε θ)) p)

end RegularityStructures

end
