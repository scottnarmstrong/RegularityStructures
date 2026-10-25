/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovGammaDiffGoodAnnulus
public import RegularityStructures.Probability.ModelKolmogorovGammaDiffRelativeSource
public import RegularityStructures.Probability.ModelKolmogorovGammaProductNet
import Mathlib.Tactic.Linarith
public import Mathlib.Order.CompletePartialOrder

/-!
# The good Chen channels of the unit-box Gamma difference

The good channels of the split annular increment of `Γ¹ - Γ²` carry the factor `C δ` (`δ = ε^θ`)
homogeneously: the near bounds of
`RegularityStructures.Probability.ModelKolmogorovGammaDiffGoodMoment` satisfy
`bound(C, C̄, δ) ≤ (C δ)^p bound(1, C̄', 1)` for `C̄ ≤ C̄'`. Combined with the uniform scale bounds
(applied at `C = δ = 1`), this gives step moments whose constant is `(C δ)^p` times a constant
independent of `C` and of the probability space, and a global good envelope over all coarse annuli
and fine refinements with the same structure.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal NNReal

namespace RegularityStructures

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝒯 : RegularityStructure ι}

omit [Fintype ι] [DecidableEq ι] in
/-- The shape of the near good bounds: a lead term and a doubled finite sum, each bounded by a
common factor `σ`. -/
theorem gammaDiffNearGoodShape_le {σ A A' c d : ℝ≥0∞} {s : Finset ι}
    {B B' : ι → ℝ≥0∞} (hA : A ≤ σ * A') (hB : ∀ k ∈ s, B k ≤ σ * B' k) :
    d * (A + c * d * ∑ k ∈ s, (B k + B k)) ≤
      σ * (d * (A' + c * d * ∑ k ∈ s, (B' k + B' k))) := by
  calc
    _ ≤ d * (σ * A' + c * d * ∑ k ∈ s, (σ * B' k + σ * B' k)) := by
      gcongr with k hk
      · exact hB k hk
      · exact hB k hk
    _ = _ := by
      simp only [← mul_add, ← Finset.mul_sum]
      ring

private theorem gammaDiffUnitGood_lead_le {C δ a : ℝ} (hC : 0 ≤ C) (hδ : 0 ≤ δ) (p : ℕ) :
    ENNReal.ofReal (C * δ * a) ^ p ≤
      ENNReal.ofReal (C * δ) ^ p * ENNReal.ofReal (1 * 1 * a) ^ p := by
  rw [one_mul, one_mul, ← mul_pow, ← ENNReal.ofReal_mul (mul_nonneg hC hδ)]

private theorem gammaDiffUnitGood_mixed_le {C Cbar Cbar' δ a : ℝ} (hC : 0 ≤ C)
    (hδ : 0 ≤ δ) (hCbar : Cbar ≤ Cbar') (ha : 0 ≤ a) (p : ℕ) :
    ENNReal.ofReal (Cbar * C * δ * a) ^ p ≤
      ENNReal.ofReal (C * δ) ^ p * ENNReal.ofReal (Cbar' * 1 * 1 * a) ^ p := by
  rw [← mul_pow, ← ENNReal.ofReal_mul (mul_nonneg hC hδ)]
  refine pow_le_pow_left₀ (by positivity) (ENNReal.ofReal_le_ofReal ?_) p
  have h : Cbar * (C * δ * a) ≤ Cbar' * (C * δ * a) :=
    mul_le_mul_of_nonneg_right hCbar (mul_nonneg (mul_nonneg hC hδ) ha)
  calc
    Cbar * C * δ * a = Cbar * (C * δ * a) := by ring
    _ ≤ Cbar' * (C * δ * a) := h
    _ = C * δ * (Cbar' * 1 * 1 * a) := by ring

private theorem gammaDiffUnitGood_scaleDist_rpow_mul_nonneg (u v w z : ParabolicSpace)
    (a b : ℝ) :
    0 ≤ parabolicSemigroup.scaleDist u v ^ a * parabolicSemigroup.scaleDist w z ^ b :=
  mul_nonneg (Real.rpow_nonneg (parabolicSemigroup.scaleDist_nonneg _ _) _)
    (Real.rpow_nonneg (parabolicSemigroup.scaleDist_nonneg _ _) _)

/-- The left near good bound is homogeneous in the source factor `C δ`. -/
theorem gammaDiffNearLeftGoodBound_le_source_mul
    (𝒯 : RegularityStructure ι) (D : Set (ι × ι)) (κ C Cbar Cbar' δ : ℝ) (p : ℕ)
    (i j : ι) (x y z : ParabolicSpace) (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hCbar : Cbar ≤ Cbar') :
    gammaDiffNearLeftGoodBound 𝒯 D κ C Cbar δ p i j x y z ≤
      ENNReal.ofReal (C * δ) ^ p *
        gammaDiffNearLeftGoodBound 𝒯 D κ 1 Cbar' 1 p i j x y z := by
  unfold gammaDiffNearLeftGoodBound
  exact gammaDiffNearGoodShape_le (gammaDiffUnitGood_lead_le hC hδ p)
    (fun k _ => gammaDiffUnitGood_mixed_le hC hδ hCbar
      (gammaDiffUnitGood_scaleDist_rpow_mul_nonneg _ _ _ _ _ _) p)

/-- The right near good bound is homogeneous in the source factor `C δ`. -/
theorem gammaDiffNearRightGoodBound_le_source_mul
    (𝒯 : RegularityStructure ι) (D : Set (ι × ι)) (κ C Cbar Cbar' δ : ℝ) (p : ℕ)
    (i j : ι) (x y z : ParabolicSpace) (hC : 0 ≤ C) (hδ : 0 ≤ δ)
    (hCbar : Cbar ≤ Cbar') :
    gammaDiffNearRightGoodBound 𝒯 D κ C Cbar δ p i j x y z ≤
      ENNReal.ofReal (C * δ) ^ p *
        gammaDiffNearRightGoodBound 𝒯 D κ 1 Cbar' 1 p i j x y z := by
  unfold gammaDiffNearRightGoodBound
  exact gammaDiffNearGoodShape_le (gammaDiffUnitGood_lead_le hC hδ p)
    (fun k _ => gammaDiffUnitGood_mixed_le hC hδ hCbar
      (gammaDiffUnitGood_scaleDist_rpow_mul_nonneg _ _ _ _ _ _) p)

omit [IsProbabilityMeasure P] in
theorem gammaDiffSplitLeftGoodTerm_aemeasurable
    (M₁ M₂ : Ω → Model 𝒯 parabolicSemigroup) (D : Set (ι × ι))
    (hm₁ : ∀ x y i j, AEMeasurable
      (fun ω => ((M₁ ω).gammaMap y x (Pi.single i 1) j)) P)
    (hm₂ : ∀ x y i j, AEMeasurable
      (fun ω => ((M₂ ω).gammaMap y x (Pi.single i 1) j)) P)
    (i j : ι) (x y z : ParabolicSpace) :
    AEMeasurable (gammaDiffSplitLeftGoodTerm M₁ M₂ D i j x y z) P := by
  unfold gammaDiffSplitLeftGoodTerm
  exact ((hm₁ _ _ i j).sub (hm₂ _ _ i j)).add
    (Finset.aemeasurable_fun_sum _ fun k _ =>
      (((hm₁ _ _ i k).sub (hm₂ _ _ i k)).mul (hm₁ _ _ k j)).add
        ((hm₂ _ _ i k).mul ((hm₁ _ _ k j).sub (hm₂ _ _ k j))))

omit [IsProbabilityMeasure P] in
theorem gammaDiffSplitRightGoodTerm_aemeasurable
    (M₁ M₂ : Ω → Model 𝒯 parabolicSemigroup) (D : Set (ι × ι))
    (hm₁ : ∀ x y i j, AEMeasurable
      (fun ω => ((M₁ ω).gammaMap y x (Pi.single i 1) j)) P)
    (hm₂ : ∀ x y i j, AEMeasurable
      (fun ω => ((M₂ ω).gammaMap y x (Pi.single i 1) j)) P)
    (i j : ι) (x y z : ParabolicSpace) :
    AEMeasurable (gammaDiffSplitRightGoodTerm M₁ M₂ D i j x y z) P := by
  unfold gammaDiffSplitRightGoodTerm
  exact ((hm₁ _ _ i j).sub (hm₂ _ _ i j)).add
    (Finset.aemeasurable_fun_sum _ fun k _ =>
      (((hm₁ _ _ i k).sub (hm₂ _ _ i k)).mul (hm₁ _ _ k j)).add
        ((hm₂ _ _ i k).mul ((hm₁ _ _ k j).sub (hm₂ _ _ k j))))

omit [IsProbabilityMeasure P] in
theorem gammaDiffGoodLeftAnnulusStepSup_aemeasurable
    (S : Set ParabolicSpace) (M₁ M₂ : Ω → Model 𝒯 parabolicSemigroup)
    (D : Set (ι × ι))
    (hm₁ : ∀ x y i j, AEMeasurable
      (fun ω => ((M₁ ω).gammaMap y x (Pi.single i 1) j)) P)
    (hm₂ : ∀ x y i j, AEMeasurable
      (fun ω => ((M₂ ω).gammaMap y x (Pi.single i 1) j)) P)
    (i j : ι) (N k : ℕ) :
    AEMeasurable (gammaDiffGoodLeftAnnulusStepSup S M₁ M₂ D i j N k) P := by
  unfold gammaDiffGoodLeftAnnulusStepSup
  refine AEMeasurable.iSup fun a => AEMeasurable.iSup fun b => ?_
  split_ifs
  · exact (gammaDiffSplitLeftGoodTerm_aemeasurable M₁ M₂ D hm₁ hm₂ i j _ _ _).enorm
  · exact aemeasurable_const

omit [IsProbabilityMeasure P] in
theorem gammaDiffGoodRightAnnulusStepSup_aemeasurable
    (S : Set ParabolicSpace) (M₁ M₂ : Ω → Model 𝒯 parabolicSemigroup)
    (D : Set (ι × ι))
    (hm₁ : ∀ x y i j, AEMeasurable
      (fun ω => ((M₁ ω).gammaMap y x (Pi.single i 1) j)) P)
    (hm₂ : ∀ x y i j, AEMeasurable
      (fun ω => ((M₂ ω).gammaMap y x (Pi.single i 1) j)) P)
    (i j : ι) (N k : ℕ) :
    AEMeasurable (gammaDiffGoodRightAnnulusStepSup S M₁ M₂ D i j N k) P := by
  unfold gammaDiffGoodRightAnnulusStepSup
  refine AEMeasurable.iSup fun a => AEMeasurable.iSup fun b => ?_
  split_ifs
  · exact (gammaDiffSplitRightGoodTerm_aemeasurable M₁ M₂ D hm₁ hm₂ i j _ _ _).enorm
  · exact aemeasurable_const

private theorem gammaDiffUnitGood_left_geometry
    (S : Set ParabolicSpace)
    (hbox : ∀ x ∈ S, x.1 ∈ Icc (0 : ℝ) 1 ∧
      ∀ j, x.2 j ∈ Icc (0 : ℝ) 1)
    (N l : ℕ) (a b : gammaCell S (N + l + 1))
    (hnear : parabolicNorm
        (hsParabolicCellRepresentative S (N + l) (hsParabolicCellParent S (N + l) a) -
          hsParabolicCellRepresentative S (N + l + 1) b) ≤
        20 / (2 : ℝ) ^ N) :
    parabolicSemigroup.scaleDist (hsParabolicCellRepresentative S (N + l + 1) a)
        (hsParabolicCellRepresentative S (N + l + 1) b) ≤ 24 / (2 : ℝ) ^ N ∧
      parabolicSemigroup.scaleDist
        (hsParabolicCellRepresentative S (N + l) (hsParabolicCellParent S (N + l) a))
        (hsParabolicCellRepresentative S (N + l + 1) a) ≤ 4 / (2 : ℝ) ^ (N + l) := by
  have hparent := hsParabolicCellParent_radius S hbox (N + l) a
  have hparent' : parabolicNorm
      (hsParabolicCellRepresentative S (N + l + 1) a -
        hsParabolicCellRepresentative S (N + l) (hsParabolicCellParent S (N + l) a)) ≤
      4 / (2 : ℝ) ^ (N + l) := by
    rw [parabolicNorm_sub_comm]
    exact hparent
  refine ⟨?_, hparent⟩
  change parabolicNorm (hsParabolicCellRepresentative S (N + l + 1) a -
    (hsParabolicCellRepresentative S (N + l + 1) b : ParabolicSpace)) ≤ _
  have hscale : 4 / (2 : ℝ) ^ (N + l) ≤ 4 / (2 : ℝ) ^ N :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity)
      (pow_le_pow_right₀ (by norm_num) (Nat.le_add_right N l))
  calc
    _ = parabolicNorm
        ((hsParabolicCellRepresentative S (N + l + 1) a -
            hsParabolicCellRepresentative S (N + l) (hsParabolicCellParent S (N + l) a)) +
          (hsParabolicCellRepresentative S (N + l) (hsParabolicCellParent S (N + l) a) -
            hsParabolicCellRepresentative S (N + l + 1) b)) := by
      congr 1
      abel
    _ ≤ 4 / (2 : ℝ) ^ (N + l) + 20 / (2 : ℝ) ^ N :=
      (parabolicNorm_add_le _ _).trans (add_le_add hparent' hnear)
    _ ≤ 4 / (2 : ℝ) ^ N + 20 / (2 : ℝ) ^ N := by linarith
    _ = 24 / (2 : ℝ) ^ N := by ring

private theorem gammaDiffUnitGood_right_geometry
    (S : Set ParabolicSpace)
    (hbox : ∀ x ∈ S, x.1 ∈ Icc (0 : ℝ) 1 ∧
      ∀ j, x.2 j ∈ Icc (0 : ℝ) 1)
    (N l : ℕ) (a b : gammaCell S (N + l + 1))
    (hnear : parabolicNorm
        (hsParabolicCellRepresentative S (N + l) (hsParabolicCellParent S (N + l) a) -
          hsParabolicCellRepresentative S (N + l + 1) b) ≤
        20 / (2 : ℝ) ^ N) :
    parabolicSemigroup.scaleDist
        (hsParabolicCellRepresentative S (N + l) (hsParabolicCellParent S (N + l) a))
        (hsParabolicCellRepresentative S (N + l + 1) b) ≤ 24 / (2 : ℝ) ^ N ∧
      parabolicSemigroup.scaleDist (hsParabolicCellRepresentative S (N + l + 1) b)
        (hsParabolicCellRepresentative S (N + l) (hsParabolicCellParent S (N + l) b)) ≤
        4 / (2 : ℝ) ^ (N + l) := by
  have hparent := hsParabolicCellParent_radius S hbox (N + l) b
  constructor
  · change parabolicNorm (hsParabolicCellRepresentative S (N + l)
      (hsParabolicCellParent S (N + l) a) -
        (hsParabolicCellRepresentative S (N + l + 1) b : ParabolicSpace)) ≤ _
    have h20 : 20 / (2 : ℝ) ^ N ≤ 24 / (2 : ℝ) ^ N :=
      div_le_div_of_nonneg_right (by norm_num) (by positivity)
    exact hnear.trans h20
  · change parabolicNorm (hsParabolicCellRepresentative S (N + l + 1) b -
      (hsParabolicCellRepresentative S (N + l)
        (hsParabolicCellParent S (N + l) b) : ParabolicSpace)) ≤ _
    rw [parabolicNorm_sub_comm]
    exact hparent

/-- **Left good step moment, source-factored.**  The constant is `(C δ)^m` times the uniform
scale constant `L` of the source-free near bound. -/
theorem gammaDiffGoodLeftAnnulusStepSup_moment_source_le
    (S : Set ParabolicSpace)
    (hbox : ∀ x ∈ S, x.1 ∈ Icc (0 : ℝ) 1 ∧
      ∀ j, x.2 j ∈ Icc (0 : ℝ) 1)
    (M₁ M₂ : Ω → Model 𝒯 parabolicSemigroup) (D : Set (ι × ι))
    (γ κ C Cbar Cbar' δ ρ : ℝ) {m q : ℕ} (hm : 1 ≤ m) (hmq : 2 * m ≤ q)
    (hC : 0 ≤ C) (hCbar : C ≤ Cbar) (hCbar' : Cbar ≤ Cbar') (hδ : 0 ≤ δ)
    (hm₁ : ∀ x y i j, AEMeasurable
      (fun ω => ((M₁ ω).gammaMap y x (Pi.single i 1) j)) P)
    (hm₂ : ∀ x y i j, AEMeasurable
      (fun ω => ((M₂ ω).gammaMap y x (Pi.single i 1) j)) P)
    (hdet₁ : ∀ i j, (i, j) ∈ D → 𝒯.deg i < γ →
      𝒯.deg j < 𝒯.deg i → ∀ ω x y,
      |(M₁ ω).gammaMap y x (Pi.single i 1) j| ≤
        C * parabolicSemigroup.scaleDist y x ^ (𝒯.deg i - 𝒯.deg j))
    (hdet₂ : ∀ i j, (i, j) ∈ D → 𝒯.deg i < γ →
      𝒯.deg j < 𝒯.deg i → ∀ ω x y,
      |(M₂ ω).gammaMap y x (Pi.single i 1) j| ≤
        C * parabolicSemigroup.scaleDist y x ^ (𝒯.deg i - 𝒯.deg j))
    (hann₁ : ∀ i j, (i, j) ∉ D → 𝒯.deg i < γ →
      𝒯.deg j < 𝒯.deg i → ∀ x y,
      (∫⁻ ω, ‖(M₁ ω).gammaMap y x (Pi.single i 1) j‖ₑ ^ q ∂P) ≤
        ENNReal.ofReal (C * parabolicSemigroup.scaleDist y x ^
          (𝒯.deg i - 𝒯.deg j + κ)) ^ q)
    (hann₂ : ∀ i j, (i, j) ∉ D → 𝒯.deg i < γ →
      𝒯.deg j < 𝒯.deg i → ∀ x y,
      (∫⁻ ω, ‖(M₂ ω).gammaMap y x (Pi.single i 1) j‖ₑ ^ q ∂P) ≤
        ENNReal.ofReal (C * parabolicSemigroup.scaleDist y x ^
          (𝒯.deg i - 𝒯.deg j + κ)) ^ q)
    (hdiff : ∀ i j, (i, j) ∈ D → 𝒯.deg i < γ →
      𝒯.deg j < 𝒯.deg i → ∀ ω x y,
      |(M₁ ω).gammaMap y x (Pi.single i 1) j -
        (M₂ ω).gammaMap y x (Pi.single i 1) j| ≤
        C * δ * parabolicSemigroup.scaleDist y x ^
          (𝒯.deg i - 𝒯.deg j))
    (hdiffN : ∀ i j, (i, j) ∉ D → 𝒯.deg i < γ →
      𝒯.deg j < 𝒯.deg i → ∀ x y,
      (∫⁻ ω, ‖(M₁ ω).gammaMap y x (Pi.single i 1) j -
        (M₂ ω).gammaMap y x (Pi.single i 1) j‖ₑ ^ q ∂P) ≤
        ENNReal.ofReal (C * δ * parabolicSemigroup.scaleDist y x ^
          (𝒯.deg i - 𝒯.deg j + κ)) ^ q)
    (i j : ι) (hi : 𝒯.deg i < γ) (hj : 𝒯.deg j < 𝒯.deg i)
    (hij : (i, j) ∉ D) (L : ℝ≥0∞)
    (hL : ∀ (N l : ℕ) (x y z : ParabolicSpace),
      parabolicSemigroup.scaleDist y x ≤ 24 / (2 : ℝ) ^ N →
      parabolicSemigroup.scaleDist z y ≤ 4 / (2 : ℝ) ^ (N + l) →
      gammaDiffNearLeftGoodBound 𝒯 D κ 1 Cbar' 1 m i j x y z ≤
        L * dyadicBase N ^ ((m : ℝ) * (𝒯.deg i - 𝒯.deg j + ρ)) *
          dyadicBase l ^ ((m : ℝ) * ρ))
    (N l : ℕ) :
    ∫⁻ ω, gammaDiffGoodLeftAnnulusStepSup S M₁ M₂ D i j N (N + l) ω ^ m ∂P ≤
      (Fintype.card (gammaCell S (N + l + 1)) : ℝ≥0∞) ^ 2 *
        (ENNReal.ofReal (C * δ) ^ m * (L *
          dyadicBase N ^ ((m : ℝ) * (𝒯.deg i - 𝒯.deg j + ρ)) *
          dyadicBase l ^ ((m : ℝ) * ρ))) := by
  set K : ℝ≥0∞ := ENNReal.ofReal (C * δ) ^ m * (L *
    dyadicBase N ^ ((m : ℝ) * (𝒯.deg i - 𝒯.deg j + ρ)) *
    dyadicBase l ^ ((m : ℝ) * ρ)) with hK
  have h := gammaDiffGoodLeftAnnulusStepSup_moment_le S M₁ M₂ D i j N (N + l) m hm
    (fun _ _ => K)
    (fun a b => by
      split_ifs
      · exact (gammaDiffSplitLeftGoodTerm_aemeasurable M₁ M₂ D hm₁ hm₂ i j _ _ _).enorm
      · exact aemeasurable_const)
    (fun a b => by
      have : Nonempty (gammaCell S (N + l + 1)) := ⟨a⟩
      simp only [iSup_const]
      by_cases hnear : parabolicNorm
          (hsParabolicCellRepresentative S (N + l) (hsParabolicCellParent S (N + l) a) -
            hsParabolicCellRepresentative S (N + l + 1) b) ≤ 20 / (2 : ℝ) ^ N
      · simp only [ite_eq_left hnear]
        obtain ⟨hxy, hzy⟩ := gammaDiffUnitGood_left_geometry S hbox N l a b hnear
        calc
          _ ≤ _ := gammaDiffSplitLeftGoodTerm_moment_le M₁ M₂ D γ κ C Cbar δ hm hmq
            hC hCbar hδ hm₁ hm₂ hdet₁ hdet₂ hann₁ hann₂ hdiff hdiffN i j hi hj hij _ _ _
          _ ≤ _ := gammaDiffNearLeftGoodBound_le_source_mul 𝒯 D κ C Cbar Cbar' δ m i j
            _ _ _ hC hδ hCbar'
          _ ≤ K := mul_le_mul_of_nonneg_left (hL N l _ _ _ hxy hzy) (by positivity)
      · simp only [ite_eq_right hnear, zero_pow (by omega : m ≠ 0), lintegral_zero]
        exact bot_le)
  exact h.trans (mul_le_mul_of_nonneg_left (iSup₂_le fun _ _ => le_rfl) (by positivity))

/-- **Right good step moment, source-factored.** -/
theorem gammaDiffGoodRightAnnulusStepSup_moment_source_le
    (S : Set ParabolicSpace)
    (hbox : ∀ x ∈ S, x.1 ∈ Icc (0 : ℝ) 1 ∧
      ∀ j, x.2 j ∈ Icc (0 : ℝ) 1)
    (M₁ M₂ : Ω → Model 𝒯 parabolicSemigroup) (D : Set (ι × ι))
    (γ κ C Cbar Cbar' δ ρ : ℝ) {m q : ℕ} (hm : 1 ≤ m) (hmq : 2 * m ≤ q)
    (hC : 0 ≤ C) (hCbar : C ≤ Cbar) (hCbar' : Cbar ≤ Cbar') (hδ : 0 ≤ δ)
    (hm₁ : ∀ x y i j, AEMeasurable
      (fun ω => ((M₁ ω).gammaMap y x (Pi.single i 1) j)) P)
    (hm₂ : ∀ x y i j, AEMeasurable
      (fun ω => ((M₂ ω).gammaMap y x (Pi.single i 1) j)) P)
    (hdet₁ : ∀ i j, (i, j) ∈ D → 𝒯.deg i < γ →
      𝒯.deg j < 𝒯.deg i → ∀ ω x y,
      |(M₁ ω).gammaMap y x (Pi.single i 1) j| ≤
        C * parabolicSemigroup.scaleDist y x ^ (𝒯.deg i - 𝒯.deg j))
    (hdet₂ : ∀ i j, (i, j) ∈ D → 𝒯.deg i < γ →
      𝒯.deg j < 𝒯.deg i → ∀ ω x y,
      |(M₂ ω).gammaMap y x (Pi.single i 1) j| ≤
        C * parabolicSemigroup.scaleDist y x ^ (𝒯.deg i - 𝒯.deg j))
    (hann₁ : ∀ i j, (i, j) ∉ D → 𝒯.deg i < γ →
      𝒯.deg j < 𝒯.deg i → ∀ x y,
      (∫⁻ ω, ‖(M₁ ω).gammaMap y x (Pi.single i 1) j‖ₑ ^ q ∂P) ≤
        ENNReal.ofReal (C * parabolicSemigroup.scaleDist y x ^
          (𝒯.deg i - 𝒯.deg j + κ)) ^ q)
    (hann₂ : ∀ i j, (i, j) ∉ D → 𝒯.deg i < γ →
      𝒯.deg j < 𝒯.deg i → ∀ x y,
      (∫⁻ ω, ‖(M₂ ω).gammaMap y x (Pi.single i 1) j‖ₑ ^ q ∂P) ≤
        ENNReal.ofReal (C * parabolicSemigroup.scaleDist y x ^
          (𝒯.deg i - 𝒯.deg j + κ)) ^ q)
    (hdiff : ∀ i j, (i, j) ∈ D → 𝒯.deg i < γ →
      𝒯.deg j < 𝒯.deg i → ∀ ω x y,
      |(M₁ ω).gammaMap y x (Pi.single i 1) j -
        (M₂ ω).gammaMap y x (Pi.single i 1) j| ≤
        C * δ * parabolicSemigroup.scaleDist y x ^
          (𝒯.deg i - 𝒯.deg j))
    (hdiffN : ∀ i j, (i, j) ∉ D → 𝒯.deg i < γ →
      𝒯.deg j < 𝒯.deg i → ∀ x y,
      (∫⁻ ω, ‖(M₁ ω).gammaMap y x (Pi.single i 1) j -
        (M₂ ω).gammaMap y x (Pi.single i 1) j‖ₑ ^ q ∂P) ≤
        ENNReal.ofReal (C * δ * parabolicSemigroup.scaleDist y x ^
          (𝒯.deg i - 𝒯.deg j + κ)) ^ q)
    (i j : ι) (hi : 𝒯.deg i < γ) (hj : 𝒯.deg j < 𝒯.deg i)
    (hij : (i, j) ∉ D) (L : ℝ≥0∞)
    (hL : ∀ (N l : ℕ) (x y z : ParabolicSpace),
      parabolicSemigroup.scaleDist x y ≤ 24 / (2 : ℝ) ^ N →
      parabolicSemigroup.scaleDist y z ≤ 4 / (2 : ℝ) ^ (N + l) →
      gammaDiffNearRightGoodBound 𝒯 D κ 1 Cbar' 1 m i j x y z ≤
        L * dyadicBase N ^ ((m : ℝ) * (𝒯.deg i - 𝒯.deg j + ρ)) *
          dyadicBase l ^ ((m : ℝ) * ρ))
    (N l : ℕ) :
    ∫⁻ ω, gammaDiffGoodRightAnnulusStepSup S M₁ M₂ D i j N (N + l) ω ^ m ∂P ≤
      (Fintype.card (gammaCell S (N + l + 1)) : ℝ≥0∞) ^ 2 *
        (ENNReal.ofReal (C * δ) ^ m * (L *
          dyadicBase N ^ ((m : ℝ) * (𝒯.deg i - 𝒯.deg j + ρ)) *
          dyadicBase l ^ ((m : ℝ) * ρ))) := by
  set K : ℝ≥0∞ := ENNReal.ofReal (C * δ) ^ m * (L *
    dyadicBase N ^ ((m : ℝ) * (𝒯.deg i - 𝒯.deg j + ρ)) *
    dyadicBase l ^ ((m : ℝ) * ρ)) with hK
  have h := gammaDiffGoodRightAnnulusStepSup_moment_le S M₁ M₂ D i j N (N + l) m hm
    (fun _ _ => K)
    (fun a b => by
      split_ifs
      · exact (gammaDiffSplitRightGoodTerm_aemeasurable M₁ M₂ D hm₁ hm₂ i j _ _ _).enorm
      · exact aemeasurable_const)
    (fun a b => by
      have : Nonempty (gammaCell S (N + l + 1)) := ⟨a⟩
      simp only [iSup_const]
      by_cases hnear : parabolicNorm
          (hsParabolicCellRepresentative S (N + l) (hsParabolicCellParent S (N + l) a) -
            hsParabolicCellRepresentative S (N + l + 1) b) ≤ 20 / (2 : ℝ) ^ N
      · simp only [ite_eq_left hnear]
        obtain ⟨hxy, hyz⟩ := gammaDiffUnitGood_right_geometry S hbox N l a b hnear
        calc
          _ ≤ _ := gammaDiffSplitRightGoodTerm_moment_le M₁ M₂ D γ κ C Cbar δ hm hmq
            hC hCbar hδ hm₁ hm₂ hdet₁ hdet₂ hann₁ hann₂ hdiff hdiffN i j hi hj hij _ _ _
          _ ≤ _ := gammaDiffNearRightGoodBound_le_source_mul 𝒯 D κ C Cbar Cbar' δ m i j
            _ _ _ hC hδ hCbar'
          _ ≤ K := mul_le_mul_of_nonneg_left (hL N l _ _ _ hxy hyz) (by positivity)
      · simp only [ite_eq_right hnear, zero_pow (by omega : m ≠ 0), lintegral_zero]
        exact bot_le)
  exact h.trans (mul_le_mul_of_nonneg_left (iSup₂_le fun _ _ => le_rfl) (by positivity))

end RegularityStructures

end
