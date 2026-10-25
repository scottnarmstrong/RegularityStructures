/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Statements.Defs.IsContinuousRandomModelWithFieldsOn
public import RegularityStructures.Probability.ModelKolmogorovGlobalSourceMoments
public import RegularityStructures.Probability.ModelKolmogorovPiGammaAssembly

/-!
# Assembly of the two sector estimates of the Kolmogorov criterion

This module contains the algebraic implication used after the `Pi` and `Gamma` half-theorems, which
take the source bounds as hypotheses. The half-theorems are passed as ordinary theorem arguments; no
model-norm, pathwise random constant, or conclusion-shaped stochastic premise is introduced. The
source moment order in the final statement is the maximum of the two half-theorem orders, and is
lowered to each half by Lyapunov monotonicity.

This is the final step of the Kolmogorov criterion for models [Hai14, Theorem 10.7].
-/

public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace RegularityStructures

universe u

private theorem lower_source_moment
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {f : Ω → ℝ} {p q : ℕ}
    (hf : AEMeasurable f P) (hp : 1 ≤ p) (hpq : p ≤ q)
    {b : ℝ} (h : ∫⁻ ω, ‖f ω‖ₑ ^ q ∂P ≤
      ENNReal.ofReal b ^ q) :
    ∫⁻ ω, ‖f ω‖ₑ ^ p ∂P ≤ ENNReal.ofReal b ^ p := by
  exact probability_natMoment_le_of_higher hf hp hpq _ h

theorem kolmogorov_modelNorm_of_halves
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (𝒯 : RegularityStructure ι) (γ κbar θ : ℝ)
    (hκbar : 0 < κbar) (hθ : 0 ≤ θ) (Dπ : Set ι)
    (DΓ : Set (ι × ι)) (S : Set ParabolicSpace) (hS : IsCompact S)
    (p qPi qGamma : ℕ) (KPi KGamma : ℝ → ℝ) (hp : 1 ≤ p)
    (hpPi : p ≤ qPi) (hpGamma : p ≤ qGamma)
    (hKPi : ∀ Cbar, 0 ≤ KPi Cbar)
    (hKGamma : ∀ Cbar, 0 ≤ KGamma Cbar)
    (hPiHalf : ∀ (Cbar : ℝ),
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P]
        (Z₁ Z₂ : Ω → Model 𝒯 parabolicSemigroup) (C ε : ℝ),
        0 ≤ C → C ≤ Cbar → 0 ≤ ε →
        IsContinuousRandomModelWithFieldsOn Z₁ S →
        IsContinuousRandomModelWithFieldsOn Z₂ S →
        (∀ Z ∈ ({Z₁, Z₂} : Set (Ω → Model 𝒯 parabolicSemigroup)),
          ∀ i ∈ Dπ, 𝒯.deg i < γ → ∀ ω, ∀ t ∈ Ioc (0 : ℝ) 1,
            ∀ x : ParabolicSpace,
            |(Z ω).regPi x (Pi.single i 1) t x| ≤
              C * t ^ (𝒯.deg i / parabolicSemigroup.order)) →
        (∀ i ∈ Dπ, 𝒯.deg i < γ → ∀ ω, ∀ t ∈ Ioc (0 : ℝ) 1,
          ∀ x : ParabolicSpace,
          |(Z₁ ω).regPi x (Pi.single i 1) t x -
              (Z₂ ω).regPi x (Pi.single i 1) t x| ≤
            C * ε ^ θ * t ^ (𝒯.deg i / parabolicSemigroup.order)) →
        (∀ Z ∈ ({Z₁, Z₂} : Set (Ω → Model 𝒯 parabolicSemigroup)),
          ∀ i j, (i, j) ∈ DΓ → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i → ∀ ω,
            ∀ x y : ParabolicSpace,
            |(Z ω).gammaMap y x (Pi.single i 1) j| ≤
              C * parabolicSemigroup.scaleDist y x ^
                (𝒯.deg i - 𝒯.deg j)) →
        (∀ i j, (i, j) ∈ DΓ → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i → ∀ ω,
          ∀ x y : ParabolicSpace,
          |(Z₁ ω).gammaMap y x (Pi.single i 1) j -
              (Z₂ ω).gammaMap y x (Pi.single i 1) j| ≤
            C * ε ^ θ * parabolicSemigroup.scaleDist y x ^
              (𝒯.deg i - 𝒯.deg j)) →
        (∀ Z ∈ ({Z₁, Z₂} : Set (Ω → Model 𝒯 parabolicSemigroup)),
          ∀ i, i ∉ Dπ → 𝒯.deg i < γ → ∀ t ∈ Ioc (0 : ℝ) 1,
          ∀ x : ParabolicSpace,
          ∫⁻ ω, ‖(Z ω).regPi x (Pi.single i 1) t x‖ₑ ^ qPi ∂P ≤
            ENNReal.ofReal
              (C * t ^ ((𝒯.deg i + κbar) /
                parabolicSemigroup.order)) ^ qPi) →
        (∀ i, i ∉ Dπ → 𝒯.deg i < γ → ∀ t ∈ Ioc (0 : ℝ) 1,
          ∀ x : ParabolicSpace,
          ∫⁻ ω, ‖(Z₁ ω).regPi x (Pi.single i 1) t x -
              (Z₂ ω).regPi x (Pi.single i 1) t x‖ₑ ^ qPi ∂P ≤
            ENNReal.ofReal (C * ε ^ θ *
              t ^ ((𝒯.deg i + κbar) / parabolicSemigroup.order)) ^ qPi) →
        (∀ Z ∈ ({Z₁, Z₂} : Set (Ω → Model 𝒯 parabolicSemigroup)),
          ∀ i j, (i, j) ∉ DΓ → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i →
            ∀ x y : ParabolicSpace,
            ∫⁻ ω, ‖(Z ω).gammaMap y x (Pi.single i 1) j‖ₑ ^ qPi ∂P ≤
              ENNReal.ofReal (C * parabolicSemigroup.scaleDist y x ^
                (𝒯.deg i - 𝒯.deg j + κbar)) ^ qPi) →
        (∀ i j, (i, j) ∉ DΓ → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i →
          ∀ x y : ParabolicSpace,
          ∫⁻ ω, ‖(Z₁ ω).gammaMap y x (Pi.single i 1) j -
              (Z₂ ω).gammaMap y x (Pi.single i 1) j‖ₑ ^ qPi ∂P ≤
            ENNReal.ofReal (C * ε ^ θ * parabolicSemigroup.scaleDist y x ^
              (𝒯.deg i - 𝒯.deg j + κbar)) ^ qPi) →
        (∀ Z ∈ ({Z₁, Z₂} : Set (Ω → Model 𝒯 parabolicSemigroup)),
          AEMeasurable (fun ω => (Z ω).piNormOn γ S) P ∧
            ∫⁻ ω, (Z ω).piNormOn γ S ^ p ∂P ≤
            ENNReal.ofReal (KPi Cbar * C ^ p)) ∧
        AEMeasurable (fun ω => (Z₁ ω).piDiffNormOn (Z₂ ω) γ S) P ∧
        ∫⁻ ω, (Z₁ ω).piDiffNormOn (Z₂ ω) γ S ^ p ∂P ≤
          ENNReal.ofReal (KPi Cbar * (C * ε ^ θ) ^ p))
    (hGammaHalf : ∀ (Cbar : ℝ),
      ∀ {Ω : Type u} [MeasurableSpace Ω] (P : Measure Ω)
        [IsProbabilityMeasure P]
        (Z₁ Z₂ : Ω → Model 𝒯 parabolicSemigroup) (C ε : ℝ),
        0 ≤ C → C ≤ Cbar → 0 ≤ ε →
        IsContinuousRandomModelWithFieldsOn Z₁ S →
        IsContinuousRandomModelWithFieldsOn Z₂ S →
        (∀ Z ∈ ({Z₁, Z₂} : Set (Ω → Model 𝒯 parabolicSemigroup)),
          ∀ i j, (i, j) ∈ DΓ → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i → ∀ ω,
            ∀ x y : ParabolicSpace,
            |(Z ω).gammaMap y x (Pi.single i 1) j| ≤
              C * parabolicSemigroup.scaleDist y x ^
                (𝒯.deg i - 𝒯.deg j)) →
        (∀ i j, (i, j) ∈ DΓ → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i → ∀ ω,
          ∀ x y : ParabolicSpace,
          |(Z₁ ω).gammaMap y x (Pi.single i 1) j -
              (Z₂ ω).gammaMap y x (Pi.single i 1) j| ≤
            C * ε ^ θ * parabolicSemigroup.scaleDist y x ^
              (𝒯.deg i - 𝒯.deg j)) →
        (∀ Z ∈ ({Z₁, Z₂} : Set (Ω → Model 𝒯 parabolicSemigroup)),
          ∀ i j, (i, j) ∉ DΓ → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i →
            ∀ x y : ParabolicSpace,
            ∫⁻ ω, ‖(Z ω).gammaMap y x (Pi.single i 1) j‖ₑ ^ qGamma ∂P ≤
              ENNReal.ofReal (C * parabolicSemigroup.scaleDist y x ^
                (𝒯.deg i - 𝒯.deg j + κbar)) ^ qGamma) →
        (∀ i j, (i, j) ∉ DΓ → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i →
          ∀ x y : ParabolicSpace,
          ∫⁻ ω, ‖(Z₁ ω).gammaMap y x (Pi.single i 1) j -
              (Z₂ ω).gammaMap y x (Pi.single i 1) j‖ₑ ^ qGamma ∂P ≤
            ENNReal.ofReal (C * ε ^ θ * parabolicSemigroup.scaleDist y x ^
              (𝒯.deg i - 𝒯.deg j + κbar)) ^ qGamma) →
        (∀ Z ∈ ({Z₁, Z₂} : Set (Ω → Model 𝒯 parabolicSemigroup)),
          AEMeasurable (fun ω => (Z ω).gammaNormOn γ S) P ∧
            ∫⁻ ω, (Z ω).gammaNormOn γ S ^ p ∂P ≤
              ENNReal.ofReal (KGamma Cbar * C ^ p)) ∧
        AEMeasurable (fun ω => (Z₁ ω).gammaDiffNormOn (Z₂ ω) γ S) P ∧
        ∫⁻ ω, (Z₁ ω).gammaDiffNormOn (Z₂ ω) γ S ^ p ∂P ≤
          ENNReal.ofReal (KGamma Cbar * (C * ε ^ θ) ^ p)) :
    ∃ q : ℕ, p ≤ q ∧ ∀ Cbar : ℝ, ∃ K : ℝ, 0 ≤ K ∧
    ∀ {Ω : Type u} [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (Z₁ Z₂ : Ω → Model 𝒯 parabolicSemigroup) (C ε : ℝ),
      0 ≤ C → C ≤ Cbar → 0 ≤ ε →
      IsContinuousRandomModelWithFieldsOn Z₁ S →
      IsContinuousRandomModelWithFieldsOn Z₂ S →
      (∀ Z ∈ ({Z₁, Z₂} : Set (Ω → Model 𝒯 parabolicSemigroup)),
        ∀ i ∈ Dπ, 𝒯.deg i < γ → ∀ ω, ∀ t ∈ Ioc (0 : ℝ) 1,
          ∀ x : ParabolicSpace,
          |(Z ω).regPi x (Pi.single i 1) t x| ≤
            C * t ^ (𝒯.deg i / parabolicSemigroup.order)) →
      (∀ i ∈ Dπ, 𝒯.deg i < γ → ∀ ω, ∀ t ∈ Ioc (0 : ℝ) 1,
        ∀ x : ParabolicSpace,
        |(Z₁ ω).regPi x (Pi.single i 1) t x -
            (Z₂ ω).regPi x (Pi.single i 1) t x| ≤
          C * ε ^ θ * t ^ (𝒯.deg i / parabolicSemigroup.order)) →
      (∀ Z ∈ ({Z₁, Z₂} : Set (Ω → Model 𝒯 parabolicSemigroup)),
        ∀ i j, (i, j) ∈ DΓ → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i → ∀ ω,
          ∀ x y : ParabolicSpace,
          |(Z ω).gammaMap y x (Pi.single i 1) j| ≤
            C * parabolicSemigroup.scaleDist y x ^ (𝒯.deg i - 𝒯.deg j)) →
      (∀ i j, (i, j) ∈ DΓ → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i → ∀ ω,
        ∀ x y : ParabolicSpace,
        |(Z₁ ω).gammaMap y x (Pi.single i 1) j -
            (Z₂ ω).gammaMap y x (Pi.single i 1) j| ≤
          C * ε ^ θ * parabolicSemigroup.scaleDist y x ^
            (𝒯.deg i - 𝒯.deg j)) →
      (∀ Z ∈ ({Z₁, Z₂} : Set (Ω → Model 𝒯 parabolicSemigroup)),
        ∀ i, i ∉ Dπ → 𝒯.deg i < γ → ∀ t ∈ Ioc (0 : ℝ) 1,
        ∀ x : ParabolicSpace,
        ∫⁻ ω, ‖(Z ω).regPi x (Pi.single i 1) t x‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * t ^ ((𝒯.deg i + κbar) /
            parabolicSemigroup.order)) ^ q) →
      (∀ i, i ∉ Dπ → 𝒯.deg i < γ → ∀ t ∈ Ioc (0 : ℝ) 1,
        ∀ x : ParabolicSpace,
        ∫⁻ ω, ‖(Z₁ ω).regPi x (Pi.single i 1) t x -
            (Z₂ ω).regPi x (Pi.single i 1) t x‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * ε ^ θ * t ^ ((𝒯.deg i + κbar) /
            parabolicSemigroup.order)) ^ q) →
      (∀ Z ∈ ({Z₁, Z₂} : Set (Ω → Model 𝒯 parabolicSemigroup)),
        ∀ i j, (i, j) ∉ DΓ → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i →
          ∀ x y : ParabolicSpace,
          ∫⁻ ω, ‖(Z ω).gammaMap y x (Pi.single i 1) j‖ₑ ^ q ∂P ≤
            ENNReal.ofReal (C * parabolicSemigroup.scaleDist y x ^
              (𝒯.deg i - 𝒯.deg j + κbar)) ^ q) →
      (∀ i j, (i, j) ∉ DΓ → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i →
        ∀ x y : ParabolicSpace,
        ∫⁻ ω, ‖(Z₁ ω).gammaMap y x (Pi.single i 1) j -
            (Z₂ ω).gammaMap y x (Pi.single i 1) j‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C * ε ^ θ * parabolicSemigroup.scaleDist y x ^
            (𝒯.deg i - 𝒯.deg j + κbar)) ^ q) →
      (∀ Z ∈ ({Z₁, Z₂} : Set (Ω → Model 𝒯 parabolicSemigroup)),
        AEMeasurable (fun ω => (Z ω).normOn γ S) P ∧
          ∫⁻ ω, (Z ω).normOn γ S ^ p ∂P ≤
            ENNReal.ofReal (K * C ^ p)) ∧
      AEMeasurable (fun ω => (Z₁ ω).diffNormOn (Z₂ ω) γ S) P ∧
      ∫⁻ ω, (Z₁ ω).diffNormOn (Z₂ ω) γ S ^ p ∂P ≤
        ENNReal.ofReal (K * (C * ε ^ θ) ^ p) := by
  classical
  have _ := hκbar
  have _ := hθ
  have _ := hS
  let q := max qPi qGamma
  refine ⟨q, hpPi.trans (Nat.le_max_left _ _), ?_⟩
  intro Cbar
  let K := (2 : ℝ) ^ ((p : ℝ) - 1) * (KPi Cbar + KGamma Cbar)
  refine ⟨K, ?_, ?_⟩
  · dsimp [K]
    exact mul_nonneg (Real.rpow_nonneg (by norm_num) _)
      (add_nonneg (hKPi Cbar) (hKGamma Cbar))
  · intro Ω _ P _ Z₁ Z₂ C ε hC hCbar hε hZ₁ hZ₂ hPiDet hPiDiffDet hGammaDet
      hGammaDiffDet hPiAnn hPiDiffAnn hGammaAnn hGammaDiffAnn
    have hqPi : 1 ≤ qPi := hp.trans hpPi
    have hqGamma : 1 ≤ qGamma := hp.trans hpGamma
    have hPiAnn' : ∀ Z ∈ ({Z₁, Z₂} : Set (Ω → Model 𝒯 parabolicSemigroup)),
        ∀ i, i ∉ Dπ → 𝒯.deg i < γ → ∀ t ∈ Ioc (0 : ℝ) 1,
          ∀ x : ParabolicSpace,
          ∫⁻ ω, ‖(Z ω).regPi x (Pi.single i 1) t x‖ₑ ^ qPi ∂P ≤
            ENNReal.ofReal (C * t ^ ((𝒯.deg i + κbar) /
              parabolicSemigroup.order)) ^ qPi := by
      intro Z hZ i hi hdi t ht x
      have hZ' : Z = Z₁ ∨ Z = Z₂ := by
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, eq_comm] using hZ
      rcases hZ' with hEq | hEq
      · subst Z
        exact lower_source_moment (p := qPi) (q := q)
          (hZ₁.1.1 i x t ht.1).aemeasurable hqPi (Nat.le_max_left _ _)
          (hPiAnn Z₁ (by simp) i hi hdi t ht x)
      · subst Z
        exact lower_source_moment (p := qPi) (q := q)
          (hZ₂.1.1 i x t ht.1).aemeasurable hqPi (Nat.le_max_left _ _)
          (hPiAnn Z₂ (by simp) i hi hdi t ht x)
    have hPiDiffAnn' : ∀ i, i ∉ Dπ → 𝒯.deg i < γ → ∀ t ∈ Ioc (0 : ℝ) 1,
        ∀ x : ParabolicSpace,
        ∫⁻ ω, ‖(Z₁ ω).regPi x (Pi.single i 1) t x -
            (Z₂ ω).regPi x (Pi.single i 1) t x‖ₑ ^ qPi ∂P ≤
          ENNReal.ofReal (C * ε ^ θ * t ^ ((𝒯.deg i + κbar) /
            parabolicSemigroup.order)) ^ qPi := by
      intro i hi hdi t ht x
      exact lower_source_moment (p := qPi) (q := q)
        ((hZ₁.1.1 i x t ht.1).sub (hZ₂.1.1 i x t ht.1)).aemeasurable hqPi
        (Nat.le_max_left _ _) (hPiDiffAnn i hi hdi t ht x)
    have hGammaAnnPi' :
        ∀ Z ∈ ({Z₁, Z₂} : Set (Ω → Model 𝒯 parabolicSemigroup)),
          ∀ i j, (i, j) ∉ DΓ → 𝒯.deg i < γ →
            𝒯.deg j < 𝒯.deg i → ∀ x y : ParabolicSpace,
            ∫⁻ ω, ‖(Z ω).gammaMap y x (Pi.single i 1) j‖ₑ ^ qPi ∂P ≤
              ENNReal.ofReal (C * parabolicSemigroup.scaleDist y x ^
                (𝒯.deg i - 𝒯.deg j + κbar)) ^ qPi := by
      intro Z hZ i j hij hi hj x y
      have hZ' : Z = Z₁ ∨ Z = Z₂ := by
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, eq_comm] using hZ
      rcases hZ' with hEq | hEq
      · subst Z
        exact lower_source_moment (p := qPi) (q := q)
          (hZ₁.1.2.1 i j x y).aemeasurable hqPi (Nat.le_max_left _ _)
          (hGammaAnn Z₁ (by simp) i j hij hi hj x y)
      · subst Z
        exact lower_source_moment (p := qPi) (q := q)
          (hZ₂.1.2.1 i j x y).aemeasurable hqPi (Nat.le_max_left _ _)
          (hGammaAnn Z₂ (by simp) i j hij hi hj x y)
    have hGammaDiffAnnPi' : ∀ i j, (i, j) ∉ DΓ → 𝒯.deg i < γ →
        𝒯.deg j < 𝒯.deg i → ∀ x y : ParabolicSpace,
        ∫⁻ ω, ‖(Z₁ ω).gammaMap y x (Pi.single i 1) j -
            (Z₂ ω).gammaMap y x (Pi.single i 1) j‖ₑ ^ qPi ∂P ≤
          ENNReal.ofReal (C * ε ^ θ * parabolicSemigroup.scaleDist y x ^
            (𝒯.deg i - 𝒯.deg j + κbar)) ^ qPi := by
      intro i j hij hi hj x y
      exact lower_source_moment (p := qPi) (q := q)
        ((hZ₁.1.2.1 i j x y).sub (hZ₂.1.2.1 i j x y)).aemeasurable hqPi
        (Nat.le_max_left _ _) (hGammaDiffAnn i j hij hi hj x y)
    have hGammaAnn' :
        ∀ Z ∈ ({Z₁, Z₂} : Set (Ω → Model 𝒯 parabolicSemigroup)),
          ∀ i j, (i, j) ∉ DΓ → 𝒯.deg i < γ →
            𝒯.deg j < 𝒯.deg i → ∀ x y : ParabolicSpace,
            ∫⁻ ω, ‖(Z ω).gammaMap y x (Pi.single i 1) j‖ₑ ^ qGamma ∂P ≤
              ENNReal.ofReal (C * parabolicSemigroup.scaleDist y x ^
                (𝒯.deg i - 𝒯.deg j + κbar)) ^ qGamma := by
      intro Z hZ i j hij hi hj x y
      have hZ' : Z = Z₁ ∨ Z = Z₂ := by
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, eq_comm] using hZ
      rcases hZ' with hEq | hEq
      · subst Z
        exact lower_source_moment (p := qGamma) (q := q)
          (hZ₁.1.2.1 i j x y).aemeasurable hqGamma (Nat.le_max_right _ _)
          (hGammaAnn Z₁ (by simp) i j hij hi hj x y)
      · subst Z
        exact lower_source_moment (p := qGamma) (q := q)
          (hZ₂.1.2.1 i j x y).aemeasurable hqGamma (Nat.le_max_right _ _)
          (hGammaAnn Z₂ (by simp) i j hij hi hj x y)
    have hGammaDiffAnn' : ∀ i j, (i, j) ∉ DΓ → 𝒯.deg i < γ →
        𝒯.deg j < 𝒯.deg i → ∀ x y : ParabolicSpace,
        ∫⁻ ω, ‖(Z₁ ω).gammaMap y x (Pi.single i 1) j -
            (Z₂ ω).gammaMap y x (Pi.single i 1) j‖ₑ ^ qGamma ∂P ≤
          ENNReal.ofReal (C * ε ^ θ * parabolicSemigroup.scaleDist y x ^
            (𝒯.deg i - 𝒯.deg j + κbar)) ^ qGamma := by
      intro i j hij hi hj x y
      exact lower_source_moment (p := qGamma) (q := q)
        ((hZ₁.1.2.1 i j x y).sub (hZ₂.1.2.1 i j x y)).aemeasurable hqGamma
        (Nat.le_max_right _ _) (hGammaDiffAnn i j hij hi hj x y)
    have hPi := hPiHalf Cbar P Z₁ Z₂ C ε hC hCbar hε hZ₁ hZ₂ hPiDet
      hPiDiffDet hGammaDet hGammaDiffDet hPiAnn' hPiDiffAnn'
      hGammaAnnPi'
      (fun i j hij hi hj x y => by
        simpa only [Pi.sub_apply] using
          hGammaDiffAnnPi' i j hij hi hj x y)
    have hGamma := hGammaHalf Cbar P Z₁ Z₂ C ε hC hCbar hε hZ₁ hZ₂ hGammaDet
      hGammaDiffDet hGammaAnn' (fun i j hij hi hj x y => by
        simpa only [Pi.sub_apply] using hGammaDiffAnn' i j hij hi hj x y)
    have hcomp := randomModel_normOn_moment_le_of_component_moments
      𝒯 Z₁ Z₂ S γ p hp hZ₁ hZ₂
      (fun Z hZ => (hPi.1 Z hZ).2)
      (fun Z hZ => (hGamma.1 Z hZ).2) hPi.2.2 hGamma.2.2
    refine ⟨?_, hcomp.2.1, ?_⟩
    · intro Z hZ
      refine ⟨(hcomp.1 Z hZ).1, ?_⟩
      calc
        ∫⁻ ω, (Z ω).normOn γ S ^ p ∂P ≤
            (2 : ℝ≥0∞) ^ ((p : ℝ) - 1) *
              (ENNReal.ofReal (KPi Cbar * C ^ p) +
                ENNReal.ofReal (KGamma Cbar * C ^ p)) :=
          (hcomp.1 Z hZ).2
        _ = ENNReal.ofReal (K * C ^ p) := by
          have hpR : 0 ≤ (p : ℝ) - 1 := by
            exact sub_nonneg.mpr (by exact_mod_cast hp)
          have htwo : (2 : ℝ≥0∞) ^ ((p : ℝ) - 1) =
              ENNReal.ofReal ((2 : ℝ) ^ ((p : ℝ) - 1)) := by
            simpa using
              (ENNReal.ofReal_rpow_of_nonneg (x := (2 : ℝ))
                (p := (p : ℝ) - 1) (by norm_num) hpR)
          have hKP : 0 ≤ KPi Cbar * C ^ p :=
            mul_nonneg (hKPi Cbar) (pow_nonneg hC p)
          have hKG : 0 ≤ KGamma Cbar * C ^ p :=
            mul_nonneg (hKGamma Cbar) (pow_nonneg hC p)
          dsimp [K]
          rw [← ENNReal.ofReal_add hKP hKG, htwo]
          rw [← ENNReal.ofReal_mul (by positivity :
            0 ≤ (2 : ℝ) ^ ((p : ℝ) - 1))]
          congr 1
          ring
    · calc
        ∫⁻ ω, (Z₁ ω).diffNormOn (Z₂ ω) γ S ^ p ∂P ≤
            (2 : ℝ≥0∞) ^ ((p : ℝ) - 1) *
              (ENNReal.ofReal (KPi Cbar * (C * ε ^ θ) ^ p) +
                ENNReal.ofReal (KGamma Cbar * (C * ε ^ θ) ^ p)) := hcomp.2.2
        _ = ENNReal.ofReal (K * (C * ε ^ θ) ^ p) := by
          have hpR : 0 ≤ (p : ℝ) - 1 := by
            exact sub_nonneg.mpr (by exact_mod_cast hp)
          have htwo : (2 : ℝ≥0∞) ^ ((p : ℝ) - 1) =
              ENNReal.ofReal ((2 : ℝ) ^ ((p : ℝ) - 1)) := by
            simpa using
              (ENNReal.ofReal_rpow_of_nonneg (x := (2 : ℝ))
                (p := (p : ℝ) - 1) (by norm_num) hpR)
          have hA : 0 ≤ C * ε ^ θ :=
            mul_nonneg hC (Real.rpow_nonneg hε θ)
          dsimp [K]
          rw [← ENNReal.ofReal_add
            (mul_nonneg (hKPi Cbar) (pow_nonneg hA p))
            (mul_nonneg (hKGamma Cbar) (pow_nonneg hA p)), htwo]
          rw [← ENNReal.ofReal_mul (by positivity :
            0 ≤ (2 : ℝ) ^ ((p : ℝ) - 1))]
          congr 1
          ring

end RegularityStructures

end
