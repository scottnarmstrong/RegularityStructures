/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovGammaDiffCompactRescale
public import RegularityStructures.Probability.ModelKolmogorovGammaDiffCompactAssembly
public import RegularityStructures.Probability.ModelKolmogorovGammaDiffCompactSource
public import RegularityStructures.Probability.ModelKolmogorovGammaDiffUnitBox
public import RegularityStructures.Probability.ModelKolmogorovGammaDiffGoodAnnulus
public import RegularityStructures.Probability.ModelKolmogorovGammaDiffBadAnnulus
public import RegularityStructures.Probability.ModelKolmogorovGammaDiffRelativeSource
public import RegularityStructures.Probability.ModelKolmogorovGammaDiffSource
public import RegularityStructures.Statements.Defs.IsContinuousRandomModelWithFieldsOn
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Mathlib.Tactic.Linarith

/-!
# Two-model Gamma finite-sector induction

This module is the difference analogue of the finite-sector Gamma estimate in Hairer [Hai14, Theorem
10.7]. The Chen source is split into the complementary moment channel and the pathwise `DΓ × DΓ`
channel; the latter is summed using its positive intermediate degree gaps.
-/

public section

open MeasureTheory Set
open scoped ENNReal NNReal Topology

namespace RegularityStructures

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝒯 : RegularityStructure ι}

theorem randomModel_gammaDiffNormOn_moment
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (𝒯 : RegularityStructure ι) (γ κbar θ : ℝ)
    (hκbar : 0 < κbar) (hθ : 0 ≤ θ)
    (DΓ : Set (ι × ι)) (S : Set ParabolicSpace)
    (hS : IsCompact S) (p : ℕ) (hp : 1 ≤ p) :
    ∃ q : ℕ, p ≤ q ∧ ∀ Cbar : ℝ, ∃ K : ℝ, 0 ≤ K ∧
    ∀ {Ω : Type*} [MeasurableSpace Ω]
      (P : Measure Ω) [IsProbabilityMeasure P]
      (Z₁ Z₂ : Ω → Model 𝒯 parabolicSemigroup)
      (C ε : ℝ), 0 ≤ C → C ≤ Cbar → 0 ≤ ε →
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
          ∫⁻ ω, ‖(Z ω).gammaMap y x (Pi.single i 1) j‖ₑ ^ q ∂P ≤
            ENNReal.ofReal (C * parabolicSemigroup.scaleDist y x ^
              (𝒯.deg i - 𝒯.deg j + κbar)) ^ q) →
      (∀ i j, (i, j) ∉ DΓ → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i →
          ∀ x y : ParabolicSpace,
          ∫⁻ ω, ‖(Z₁ ω).gammaMap y x (Pi.single i 1) j -
              (Z₂ ω).gammaMap y x (Pi.single i 1) j‖ₑ ^ q ∂P ≤
            ENNReal.ofReal (C * ε ^ θ * parabolicSemigroup.scaleDist y x ^
              (𝒯.deg i - 𝒯.deg j + κbar)) ^ q) →
      AEMeasurable (fun ω => (Z₁ ω).gammaDiffNormOn (Z₂ ω) γ S) P ∧
      ∫⁻ ω, (Z₁ ω).gammaDiffNormOn (Z₂ ω) γ S ^ p ∂P ≤
        ENNReal.ofReal (K * (C * ε ^ θ) ^ p) := by
  obtain ⟨L, hL, T, f, hf, hbox⟩ :=
    gammaDiffCompactSet_normalization hS
  obtain ⟨q, hpq, hUnit⟩ :=
    randomModel_gammaDiffUnitBoxBound 𝒯 γ κbar θ hκbar hθ DΓ T hbox p hp
  refine ⟨q, hpq, ?_⟩
  intro Cbar
  let Aexp : ℝ := 1 + κbar + 2 * ∑ k : ι, |𝒯.deg k|
  let Lpow : ℝ := L ^ Aexp
  have hLpos : 0 < L := by linarith
  have hLone : 1 ≤ L := by linarith
  have hLpow : 0 ≤ Lpow := by
    dsimp [Lpow]
    positivity
  have hAdeg : ∀ i j, 𝒯.deg i - 𝒯.deg j ≤ Aexp := by
    intro i j
    have h := gammaDiffCompactSource_degree_envelope (𝒯 := 𝒯) κbar i j
    dsimp [Aexp]
    linarith
  have hAdegκ : ∀ i j,
      𝒯.deg i - 𝒯.deg j + κbar ≤ Aexp := by
    intro i j
    exact gammaDiffCompactSource_degree_envelope (𝒯 := 𝒯) κbar i j
  let Cbar0 : ℝ := Cbar * Lpow
  obtain ⟨Kunit, hKunit, hUnit⟩ := hUnit Cbar0
  let Kfinal : ℝ := Kunit * Lpow ^ p
  have hKfinal : 0 ≤ Kfinal := by
    dsimp [Kfinal]
    exact mul_nonneg hKunit (pow_nonneg hLpow p)
  refine ⟨Kfinal, hKfinal, ?_⟩
  intro Ω _ P _ Z₁ Z₂ C ε hC hCbar hε hZ₁ hZ₂ hdet hdiff hann hdiffN
  let C0 : ℝ := C * Lpow
  have hC0 : 0 ≤ C0 := by
    dsimp [C0]
    exact mul_nonneg hC hLpow
  have hC0bar : C0 ≤ Cbar0 := by
    dsimp [C0, Cbar0]
    exact mul_le_mul_of_nonneg_right hCbar hLpow
  have hδ : 0 ≤ ε ^ θ := Real.rpow_nonneg hε θ
  let M₁ : Ω → Model 𝒯 parabolicSemigroup := fun ω =>
    gammaDiffCompactPullbackModel (Z₁ ω) L (by linarith)
  let M₂ : Ω → Model 𝒯 parabolicSemigroup := fun ω =>
    gammaDiffCompactPullbackModel (Z₂ ω) L (by linarith)
  have hM₁ : IsContinuousRandomModelWithFieldsOn M₁ T := by
    simpa [M₁] using
      isContinuousRandomModelWithFieldsOn_gammaDiffCompactPullback
        L hLpos f hf Z₁ hZ₁
  have hM₂ : IsContinuousRandomModelWithFieldsOn M₂ T := by
    simpa [M₂] using
      isContinuousRandomModelWithFieldsOn_gammaDiffCompactPullback
        L hLpos f hf Z₂ hZ₂
  have hdet₁ : ∀ i j, (i, j) ∈ DΓ → 𝒯.deg i < γ →
      𝒯.deg j < 𝒯.deg i → ∀ ω x y,
      |(Z₁ ω).gammaMap y x (Pi.single i 1) j| ≤
        C * parabolicSemigroup.scaleDist y x ^ (𝒯.deg i - 𝒯.deg j) := by
    intro i j hij hi hj
    exact hdet Z₁ (Set.mem_insert _ _) i j hij hi hj
  have hdet₂ : ∀ i j, (i, j) ∈ DΓ → 𝒯.deg i < γ →
      𝒯.deg j < 𝒯.deg i → ∀ ω x y,
      |(Z₂ ω).gammaMap y x (Pi.single i 1) j| ≤
        C * parabolicSemigroup.scaleDist y x ^ (𝒯.deg i - 𝒯.deg j) := by
    intro i j hij hi hj
    exact hdet Z₂ (Set.mem_insert_of_mem _ (Set.mem_singleton _)) i j hij hi hj
  have hann₁ : ∀ i j, (i, j) ∉ DΓ → 𝒯.deg i < γ →
      𝒯.deg j < 𝒯.deg i → ∀ x y,
      ∫⁻ ω, ‖(Z₁ ω).gammaMap y x (Pi.single i 1) j‖ₑ ^ q ∂P ≤
        ENNReal.ofReal (C * parabolicSemigroup.scaleDist y x ^
          (𝒯.deg i - 𝒯.deg j + κbar)) ^ q := by
    intro i j hij hi hj
    exact hann Z₁ (Set.mem_insert _ _) i j hij hi hj
  have hann₂ : ∀ i j, (i, j) ∉ DΓ → 𝒯.deg i < γ →
      𝒯.deg j < 𝒯.deg i → ∀ x y,
      ∫⁻ ω, ‖(Z₂ ω).gammaMap y x (Pi.single i 1) j‖ₑ ^ q ∂P ≤
        ENNReal.ofReal (C * parabolicSemigroup.scaleDist y x ^
          (𝒯.deg i - 𝒯.deg j + κbar)) ^ q := by
    intro i j hij hi hj
    exact hann Z₂ (Set.mem_insert_of_mem _ (Set.mem_singleton _)) i j hij hi hj
  have hdet' := gammaDiffCompactSource_det (M := Z₁) L C hLone hC DΓ γ
    hdet₁ Aexp hAdeg
  have hdet'' := gammaDiffCompactSource_det (M := Z₂) L C hLone hC DΓ γ
    hdet₂ Aexp hAdeg
  have hdiff' := gammaDiffCompactSource_diff (M₁ := Z₁) (M₂ := Z₂)
    L C ε θ hLone hC hε DΓ γ hdiff Aexp hAdeg
  have hann' := gammaDiffCompactSource_moment (M := Z₁) L κbar C hLone hC
    DΓ γ q hann₁ Aexp hAdegκ
  have hann'' := gammaDiffCompactSource_moment (M := Z₂) L κbar C hLone hC
    DΓ γ q hann₂ Aexp hAdegκ
  have hdiffN' := gammaDiffCompactSource_diffMoment (M₁ := Z₁) (M₂ := Z₂)
    L κbar C ε θ hLone hC hε DΓ γ q hdiffN Aexp hAdegκ
  have hdetM : ∀ Z ∈ ({M₁, M₂} : Set (Ω → Model 𝒯 parabolicSemigroup)),
      ∀ i j, (i, j) ∈ DΓ → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i → ∀ ω,
        ∀ x y : ParabolicSpace,
        |(Z ω).gammaMap y x (Pi.single i 1) j| ≤
          C0 * parabolicSemigroup.scaleDist y x ^ (𝒯.deg i - 𝒯.deg j) := by
    intro Z hZ i j hij hi hj
    rcases Set.mem_insert_iff.mp hZ with rfl | hZ
    · simpa [M₁, C0, Lpow] using hdet'
        i j hij hi hj
    · have : Z = M₂ := Set.mem_singleton_iff.mp hZ
      subst Z
      simpa [M₂, C0, Lpow] using hdet'' i j hij hi hj
  have hdiffM : ∀ i j, (i, j) ∈ DΓ → 𝒯.deg i < γ →
      𝒯.deg j < 𝒯.deg i → ∀ ω,
      ∀ x y : ParabolicSpace,
      |(M₁ ω).gammaMap y x (Pi.single i 1) j -
          (M₂ ω).gammaMap y x (Pi.single i 1) j| ≤
        C0 * (ε ^ θ) * parabolicSemigroup.scaleDist y x ^
          (𝒯.deg i - 𝒯.deg j) := by
    simpa [M₁, M₂, C0, Lpow] using hdiff'
  have hannM : ∀ Z ∈ ({M₁, M₂} : Set (Ω → Model 𝒯 parabolicSemigroup)),
      ∀ i j, (i, j) ∉ DΓ → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i →
        ∀ x y : ParabolicSpace,
        ∫⁻ ω, ‖(Z ω).gammaMap y x (Pi.single i 1) j‖ₑ ^ q ∂P ≤
          ENNReal.ofReal (C0 * parabolicSemigroup.scaleDist y x ^
            (𝒯.deg i - 𝒯.deg j + κbar)) ^ q := by
    intro Z hZ i j hij hi hj
    rcases Set.mem_insert_iff.mp hZ with rfl | hZ
    · simpa [M₁, C0, Lpow] using hann'
        i j hij hi hj
    · have : Z = M₂ := Set.mem_singleton_iff.mp hZ
      subst Z
      simpa [M₂, C0, Lpow] using hann'' i j hij hi hj
  have hdiffNM : ∀ i j, (i, j) ∉ DΓ → 𝒯.deg i < γ →
      𝒯.deg j < 𝒯.deg i → ∀ x y : ParabolicSpace,
      ∫⁻ ω, ‖(M₁ ω).gammaMap y x (Pi.single i 1) j -
          (M₂ ω).gammaMap y x (Pi.single i 1) j‖ₑ ^ q ∂P ≤
        ENNReal.ofReal (C0 * (ε ^ θ) * parabolicSemigroup.scaleDist y x ^
          (𝒯.deg i - 𝒯.deg j + κbar)) ^ q := by
    simpa [M₁, M₂, C0, Lpow] using hdiffN'
  obtain ⟨B, hBm, hBtop, hBmom, hBpoint⟩ :=
    hUnit (P := P) M₁ M₂ C0 ε hC0 hC0bar hε hM₁ hM₂
      hdetM hdiffM hannM hdiffNM
  have hPull : ∀ᵐ ω ∂P,
      (gammaDiffCompactPullbackModel (Z₁ ω) L (by linarith)).GammaDiffBoundOn
        (gammaDiffCompactPullbackModel (Z₂ ω) L (by linarith)) γ
        (B ω).toNNReal T := by
    simpa [M₁, M₂] using hBpoint
  have hnorm := randomModel_gammaDiffNormOn_moment_le_of_compactPullbackEnvelope
    L hLone f hf Z₁ Z₂ γ p hZ₁ hZ₂ hBm hBtop hBmom hPull
  have hKeq : Kunit * (C0 * (ε ^ θ)) ^ p =
      Kfinal * (C * ε ^ θ) ^ p := by
    dsimp [Kfinal, C0]
    simp only [mul_pow]
    ring
  rw [hKeq] at hnorm
  exact hnorm

end RegularityStructures

end
