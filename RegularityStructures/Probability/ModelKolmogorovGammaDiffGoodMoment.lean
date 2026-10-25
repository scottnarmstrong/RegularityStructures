/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovGammaDiffAlgebra
public import RegularityStructures.Probability.ModelKolmogorovGammaSplitSource
public import RegularityStructures.Probability.ModelKolmogorovMomentOrder
import Mathlib.MeasureTheory.Integral.MeanInequalities

/-!
# Moment estimates for mixed two-model Gamma channels

The source estimate is applied only to intermediate indices for which at least
one factor is outside `DΓ`.  The other channel is treated pathwise in the
annular induction.  The constants follow Hairer [Hai14, (2.17)] and
Hairer--Steele [HS23, Proposition B.3], arXiv:2301.10081v3.
-/

@[expose] public noncomputable section

open MeasureTheory Set Classical
open scoped ENNReal NNReal

namespace RegularityStructures

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝒯 : RegularityStructure ι}

def gammaDiffNearLeftGoodBound
    (𝒯 : RegularityStructure ι) (D : Set (ι × ι))
    (κ C Cbar δ : ℝ) (p : ℕ) (i j : ι)
    (x y z : ParabolicSpace) : ℝ≥0∞ :=
  (2 : ℝ≥0∞) ^ ((p : ℝ) - 1) *
    (ENNReal.ofReal (C * δ * parabolicSemigroup.scaleDist z y ^
        (𝒯.deg i - 𝒯.deg j + (if (i, j) ∈ D then 0 else κ))) ^ p +
      ((gammaGoodIntermediate 𝒯 D i j).card : ℝ≥0∞) ^ ((p : ℝ) - 1) *
        (2 : ℝ≥0∞) ^ ((p : ℝ) - 1) *
        ∑ k ∈ gammaGoodIntermediate 𝒯 D i j, (
          ENNReal.ofReal (Cbar * C * δ * (
            parabolicSemigroup.scaleDist y x ^
              (𝒯.deg i - 𝒯.deg k + (if (i, k) ∈ D then 0 else κ)) *
            parabolicSemigroup.scaleDist z y ^
              (𝒯.deg k - 𝒯.deg j + (if (k, j) ∈ D then 0 else κ)))) ^ p +
          ENNReal.ofReal (Cbar * C * δ * (
            parabolicSemigroup.scaleDist y x ^
              (𝒯.deg i - 𝒯.deg k + (if (i, k) ∈ D then 0 else κ)) *
            parabolicSemigroup.scaleDist z y ^
              (𝒯.deg k - 𝒯.deg j + (if (k, j) ∈ D then 0 else κ)))) ^ p))

omit [IsProbabilityMeasure P] in
private theorem gammaDiffGood_productMoment
    {f g : Ω → ℝ} (hf : AEMeasurable f P) (hg : AEMeasurable g P)
    (p : ℕ) :
    (∫⁻ ω, ‖f ω * g ω‖ₑ ^ p ∂P) ≤
      (∫⁻ ω, ‖f ω‖ₑ ^ (2 * p) ∂P) ^ (1 / 2 : ℝ) *
        (∫⁻ ω, ‖g ω‖ₑ ^ (2 * p) ∂P) ^ (1 / 2 : ℝ) := by
  have h22 : (2 : ℝ).HolderConjugate 2 :=
    Real.holderConjugate_iff.mpr ⟨by norm_num, by norm_num⟩
  have h := ENNReal.lintegral_mul_le_Lp_mul_Lq P h22
    (hf.enorm.pow_const p) (hg.enorm.pow_const p)
  simpa only [Pi.mul_apply, enorm_mul, mul_pow, ENNReal.rpow_ofNat,
    ← pow_mul, Nat.mul_comm] using h

private theorem gammaDiffGood_deterministicMoment
    {f : Ω → ℝ} {B : ℝ} (h : ∀ ω, |f ω| ≤ B) (p : ℕ) :
    (∫⁻ ω, ‖f ω‖ₑ ^ p ∂P) ≤ ENNReal.ofReal B ^ p := by
  have he (ω : Ω) : ‖f ω‖ₑ ≤ ENNReal.ofReal B := by
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (h ω)
  simpa only [lintegral_const, measure_univ, mul_one] using
    lintegral_mono (μ := P) (fun ω => ENNReal.pow_le_pow_left (he ω) (n := p))

omit [Fintype ι] [DecidableEq ι] [IsProbabilityMeasure P] in
private theorem gammaDiffGood_sumMoment
    (s : Finset ι) (f : ι → Ω → ℝ)
    (hf : ∀ k ∈ s, AEMeasurable (f k) P) {p : ℕ} (hp : 1 ≤ p) :
    (∫⁻ ω, ‖∑ k ∈ s, f k ω‖ₑ ^ p ∂P) ≤
      (s.card : ℝ≥0∞) ^ ((p : ℝ) - 1) *
        ∑ k ∈ s, ∫⁻ ω, ‖f k ω‖ₑ ^ p ∂P := by
  have hpoint (ω : Ω) : ‖∑ k ∈ s, f k ω‖ₑ ^ p ≤
      (s.card : ℝ≥0∞) ^ ((p : ℝ) - 1) *
        ∑ k ∈ s, ‖f k ω‖ₑ ^ p := by
    refine (ENNReal.pow_le_pow_left (enorm_sum_le s _)).trans ?_
    simpa only [ENNReal.rpow_natCast] using
      ENNReal.rpow_sum_le_const_mul_sum_rpow s (fun k => ‖f k ω‖ₑ)
        (show (1 : ℝ) ≤ p by exact_mod_cast hp)
  refine (lintegral_mono hpoint).trans_eq ?_
  rw [lintegral_const_mul'' _ (Finset.aemeasurable_fun_sum s
    (fun k hk => (hf k hk).enorm.pow_const p)),
    lintegral_finsetSum' s (fun k hk => (hf k hk).enorm.pow_const p)]

omit [IsProbabilityMeasure P] in
private theorem gammaDiffGood_addMoment
    {f g : Ω → ℝ} (hf : AEMeasurable f P) (hg : AEMeasurable g P)
    {p : ℕ} (hp : 1 ≤ p) :
    (∫⁻ ω, ‖f ω + g ω‖ₑ ^ p ∂P) ≤
      (2 : ℝ≥0∞) ^ ((p : ℝ) - 1) *
        ((∫⁻ ω, ‖f ω‖ₑ ^ p ∂P) + ∫⁻ ω, ‖g ω‖ₑ ^ p ∂P) := by
  have hpoint (ω : Ω) : ‖f ω + g ω‖ₑ ^ p ≤
      (2 : ℝ≥0∞) ^ ((p : ℝ) - 1) *
        (‖f ω‖ₑ ^ p + ‖g ω‖ₑ ^ p) :=
    (ENNReal.pow_le_pow_left (enorm_add_le _ _)).trans (by
      simpa only [ENNReal.rpow_natCast] using
        ENNReal.rpow_add_le_mul_rpow_add_rpow (‖f ω‖ₑ) (‖g ω‖ₑ)
          (show (1 : ℝ) ≤ p by exact_mod_cast hp))
  refine (lintegral_mono hpoint).trans_eq ?_
  rw [lintegral_const_mul''
      (f := fun ω => ‖f ω‖ₑ ^ p + ‖g ω‖ₑ ^ p) _
      ((hf.enorm.pow_const p).add (hg.enorm.pow_const p)),
    lintegral_add_left' (f := fun ω => ‖f ω‖ₑ ^ p) (hf.enorm.pow_const p)]

private theorem gammaDiffCoordinateMoment
    (M : Ω → Model 𝒯 parabolicSemigroup) (D : Set (ι × ι))
    (γ κ C : ℝ) {q r : ℕ} (hr : 1 ≤ r) (hrq : r ≤ q)
    (hm : ∀ x y i j, AEMeasurable
      (fun ω => ((M ω).gammaMap y x (Pi.single i 1) j)) P)
    (hdet : ∀ i j, (i, j) ∈ D → 𝒯.deg i < γ →
      𝒯.deg j < 𝒯.deg i → ∀ ω x y,
      |(M ω).gammaMap y x (Pi.single i 1) j| ≤
        C * parabolicSemigroup.scaleDist y x ^ (𝒯.deg i - 𝒯.deg j))
    (hann : ∀ i j, (i, j) ∉ D → 𝒯.deg i < γ →
      𝒯.deg j < 𝒯.deg i → ∀ x y,
      (∫⁻ ω, ‖(M ω).gammaMap y x (Pi.single i 1) j‖ₑ ^ q ∂P) ≤
        ENNReal.ofReal (C * parabolicSemigroup.scaleDist y x ^
          (𝒯.deg i - 𝒯.deg j + κ)) ^ q)
    {a b : ParabolicSpace} {k l : ι}
    (hk : 𝒯.deg k < γ) (hl : 𝒯.deg l < 𝒯.deg k) :
    (∫⁻ ω, ‖(M ω).gammaMap b a (Pi.single k 1) l‖ₑ ^ r ∂P) ≤
      ENNReal.ofReal (C * parabolicSemigroup.scaleDist b a ^
        (𝒯.deg k - 𝒯.deg l + (if (k, l) ∈ D then 0 else κ))) ^ r := by
  by_cases hD : (k, l) ∈ D
  · simpa [hD] using (gammaDiffGood_deterministicMoment (P := P)
      (f := fun ω => (M ω).gammaMap b a (Pi.single k 1) l)
      (B := C * parabolicSemigroup.scaleDist b a ^
        (𝒯.deg k - 𝒯.deg l))
      (fun ω => hdet k l hD hk hl ω a b) r)
  · simpa [hD] using
      (randomModel_gamma_coordinate_moment_le_global_source M D γ κ C hr hrq
        hm hdet hann a b hk hl)

theorem gammaDiffCoordinateDifferenceMoment
    (M₁ M₂ : Ω → Model 𝒯 parabolicSemigroup) (D : Set (ι × ι))
    (γ κ C δ : ℝ) {q r : ℕ} (hr : 1 ≤ r) (hrq : r ≤ q)
    (hm : ∀ x y i j, AEMeasurable
      (fun ω => ((M₁ ω).gammaMap y x (Pi.single i 1) j -
        (M₂ ω).gammaMap y x (Pi.single i 1) j)) P)
    (hdet : ∀ i j, (i, j) ∈ D → 𝒯.deg i < γ →
      𝒯.deg j < 𝒯.deg i → ∀ ω x y,
      |(M₁ ω).gammaMap y x (Pi.single i 1) j -
        (M₂ ω).gammaMap y x (Pi.single i 1) j| ≤
        C * δ * parabolicSemigroup.scaleDist y x ^
          (𝒯.deg i - 𝒯.deg j))
    (hann : ∀ i j, (i, j) ∉ D → 𝒯.deg i < γ →
      𝒯.deg j < 𝒯.deg i → ∀ x y,
      (∫⁻ ω, ‖(M₁ ω).gammaMap y x (Pi.single i 1) j -
        (M₂ ω).gammaMap y x (Pi.single i 1) j‖ₑ ^ q ∂P) ≤
        ENNReal.ofReal (C * δ * parabolicSemigroup.scaleDist y x ^
          (𝒯.deg i - 𝒯.deg j + κ)) ^ q)
    {a b : ParabolicSpace} {k l : ι}
    (hk : 𝒯.deg k < γ) (hl : 𝒯.deg l < 𝒯.deg k) :
    (∫⁻ ω, ‖(M₁ ω).gammaMap b a (Pi.single k 1) l -
      (M₂ ω).gammaMap b a (Pi.single k 1) l‖ₑ ^ r ∂P) ≤
      ENNReal.ofReal (C * δ * parabolicSemigroup.scaleDist b a ^
        (𝒯.deg k - 𝒯.deg l + (if (k, l) ∈ D then 0 else κ))) ^ r := by
  by_cases hD : (k, l) ∈ D
  · simpa [hD] using (gammaDiffGood_deterministicMoment (P := P)
      (f := fun ω => (M₁ ω).gammaMap b a (Pi.single k 1) l -
        (M₂ ω).gammaMap b a (Pi.single k 1) l)
      (B := C * δ * parabolicSemigroup.scaleDist b a ^
        (𝒯.deg k - 𝒯.deg l))
      (fun ω => hdet k l hD hk hl ω a b) r)
  · simpa [hD, Real.rpow_one] using
      (randomModel_gamma_diff_coordinate_moment_le_global_source
        M₁ M₂ D γ κ C δ 1 hr hrq hm
        (fun c d hD hc hd ω u v => by
          simpa [Real.rpow_one] using hdet c d hD hc hd ω u v)
        (fun c d hD hc hd u v => by
          simpa [Real.rpow_one] using hann c d hD hc hd u v)
        a b hk hl)

omit [IsProbabilityMeasure P] in
private theorem gammaDiffGood_mixedProductBound
    {f g : Ω → ℝ} {p : ℕ} {C Cbar a b : ℝ}
    (hf : AEMeasurable f P) (hg : AEMeasurable g P)
    (hC : 0 ≤ C) (hCbar : C ≤ Cbar) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hfa : (∫⁻ ω, ‖f ω‖ₑ ^ (2 * p) ∂P) ≤
      ENNReal.ofReal (C * a) ^ (2 * p))
    (hgb : (∫⁻ ω, ‖g ω‖ₑ ^ (2 * p) ∂P) ≤
      ENNReal.ofReal (C * b) ^ (2 * p)) :
    (∫⁻ ω, ‖f ω * g ω‖ₑ ^ p ∂P) ≤
      ENNReal.ofReal (Cbar * C * a * b) ^ p := by
  have hp' := gammaDiffGood_productMoment hf hg p
  have hpow1 := ENNReal.rpow_le_rpow hfa (by norm_num : (0 : ℝ) ≤ 1 / 2)
  have hpow2 := ENNReal.rpow_le_rpow hgb (by norm_num : (0 : ℝ) ≤ 1 / 2)
  calc
    _ ≤ (∫⁻ ω, ‖f ω‖ₑ ^ (2 * p) ∂P) ^ (1 / 2 : ℝ) *
        (∫⁻ ω, ‖g ω‖ₑ ^ (2 * p) ∂P) ^ (1 / 2 : ℝ) := hp'
    _ ≤ (ENNReal.ofReal (C * a) ^ (2 * p)) ^ (1 / 2 : ℝ) *
        (ENNReal.ofReal (C * b) ^ (2 * p)) ^ (1 / 2 : ℝ) :=
      mul_le_mul' hpow1 hpow2
    _ ≤ _ := ennreal_two_source_product_le_of_upperBound hC hCbar ha hb

omit [Fintype ι] [DecidableEq ι] [IsProbabilityMeasure P] in
private theorem gammaDiffGood_sumPairMoment
    (s : Finset ι) (U V : ι → Ω → ℝ) (B : ι → ℝ≥0∞)
    {p : ℕ} (hp : 1 ≤ p)
    (hUm : ∀ k ∈ s, AEMeasurable (U k) P)
    (hVm : ∀ k ∈ s, AEMeasurable (V k) P)
    (hU : ∀ k ∈ s, (∫⁻ ω, ‖U k ω‖ₑ ^ p ∂P) ≤ B k ^ p)
    (hV : ∀ k ∈ s, (∫⁻ ω, ‖V k ω‖ₑ ^ p ∂P) ≤ B k ^ p) :
    (∫⁻ ω, ‖∑ k ∈ s, (U k ω + V k ω)‖ₑ ^ p ∂P) ≤
      (2 : ℝ≥0∞) ^ ((p : ℝ) - 1) *
        ((s.card : ℝ≥0∞) ^ ((p : ℝ) - 1) *
          ∑ k ∈ s, B k ^ p +
          (s.card : ℝ≥0∞) ^ ((p : ℝ) - 1) *
          ∑ k ∈ s, B k ^ p) := by
  have hsumU := gammaDiffGood_sumMoment s U hUm hp
  have hsumV := gammaDiffGood_sumMoment s V hVm hp
  have hsumT :
      (∫⁻ ω, ‖∑ k ∈ s, (U k ω + V k ω)‖ₑ ^ p ∂P) ≤
        (2 : ℝ≥0∞) ^ ((p : ℝ) - 1) *
          ((∫⁻ ω, ‖∑ k ∈ s, U k ω‖ₑ ^ p ∂P) +
            ∫⁻ ω, ‖∑ k ∈ s, V k ω‖ₑ ^ p ∂P) := by
    simpa only [Finset.sum_add_distrib] using
      (gammaDiffGood_addMoment
        (Finset.aemeasurable_fun_sum s (fun k hk => hUm k hk))
        (Finset.aemeasurable_fun_sum s (fun k hk => hVm k hk)) hp)
  exact hsumT.trans <| by
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    apply add_le_add
    · exact hsumU.trans (mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum hU) zero_le)
    · exact hsumV.trans (mul_le_mul_of_nonneg_left
        (Finset.sum_le_sum hV) zero_le)

omit [IsProbabilityMeasure P] in
private theorem gammaDiffSplitLeftGoodTerm_moment_core
    (M₁ M₂ : Ω → Model 𝒯 parabolicSemigroup) (D : Set (ι × ι))
    (κ C Cbar δ : ℝ) (i j : ι) {p : ℕ} (hp : 1 ≤ p)
    (x y z : ParabolicSpace) (T : Ω → ℝ)
    (S : ℝ≥0∞)
    (hdecomp : ∀ ω,
      gammaDiffSplitLeftGoodTerm M₁ M₂ D i j x y z ω =
        ((M₁ ω).gammaMap z y (Pi.single i 1) j -
          (M₂ ω).gammaMap z y (Pi.single i 1) j) + T ω)
    (hlead : (∫⁻ ω, ‖(M₁ ω).gammaMap z y (Pi.single i 1) j -
      (M₂ ω).gammaMap z y (Pi.single i 1) j‖ₑ ^ p ∂P) ≤
      ENNReal.ofReal (C * δ * parabolicSemigroup.scaleDist z y ^
        (𝒯.deg i - 𝒯.deg j + κ)) ^ p)
    (hleadm : AEMeasurable
      (fun ω => (M₁ ω).gammaMap z y (Pi.single i 1) j -
        (M₂ ω).gammaMap z y (Pi.single i 1) j) P)
    (hTm : AEMeasurable T P)
    (hsum : (∫⁻ ω, ‖T ω‖ₑ ^ p ∂P) ≤ S)
    (hbound :
      (2 : ℝ≥0∞) ^ ((p : ℝ) - 1) *
        (ENNReal.ofReal (C * δ * parabolicSemigroup.scaleDist z y ^
          (𝒯.deg i - 𝒯.deg j + κ)) ^ p + S) ≤
        gammaDiffNearLeftGoodBound 𝒯 D κ C Cbar δ p i j x y z) :
    (∫⁻ ω, ‖gammaDiffSplitLeftGoodTerm M₁ M₂ D i j x y z ω‖ₑ ^ p ∂P) ≤
      gammaDiffNearLeftGoodBound 𝒯 D κ C Cbar δ p i j x y z := by
  have hbase :
      (∫⁻ ω, ‖(M₁ ω).gammaMap z y (Pi.single i 1) j -
        (M₂ ω).gammaMap z y (Pi.single i 1) j + T ω‖ₑ ^ p ∂P) ≤
      (2 : ℝ≥0∞) ^ ((p : ℝ) - 1) *
        (ENNReal.ofReal (C * δ * parabolicSemigroup.scaleDist z y ^
          (𝒯.deg i - 𝒯.deg j + κ)) ^ p + S) := by
    refine (gammaDiffGood_addMoment hleadm hTm hp).trans ?_
    refine mul_le_mul_of_nonneg_left (add_le_add hlead hsum) (by positivity)
  have heq :
      (∫⁻ ω, ‖gammaDiffSplitLeftGoodTerm M₁ M₂ D i j x y z ω‖ₑ ^ p ∂P) =
        (∫⁻ ω, ‖(M₁ ω).gammaMap z y (Pi.single i 1) j -
          (M₂ ω).gammaMap z y (Pi.single i 1) j + T ω‖ₑ ^ p ∂P) := by
    apply lintegral_congr
    intro ω
    rw [hdecomp ω]
  rw [heq]
  exact hbase.trans hbound

theorem gammaDiffSplitLeftGoodTerm_moment_le
    (M₁ M₂ : Ω → Model 𝒯 parabolicSemigroup) (D : Set (ι × ι))
    (γ κ C Cbar δ : ℝ) {p q : ℕ} (hp : 1 ≤ p) (hpq : 2 * p ≤ q)
    (hC : 0 ≤ C) (hCbar : C ≤ Cbar) (hδ : 0 ≤ δ)
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
    (hij : (i, j) ∉ D) (x y z : ParabolicSpace) :
    (∫⁻ ω, ‖gammaDiffSplitLeftGoodTerm M₁ M₂ D i j x y z ω‖ₑ ^ p ∂P) ≤
      gammaDiffNearLeftGoodBound 𝒯 D κ C Cbar δ p i j x y z := by
  classical
  let s := gammaGoodIntermediate 𝒯 D i j
  let B : ι → ℝ≥0∞ := fun k =>
    ENNReal.ofReal (Cbar * C * δ *
      (parabolicSemigroup.scaleDist y x ^
        (𝒯.deg i - 𝒯.deg k + (if (i, k) ∈ D then 0 else κ)) *
       parabolicSemigroup.scaleDist z y ^
        (𝒯.deg k - 𝒯.deg j + (if (k, j) ∈ D then 0 else κ))))
  let U : ι → Ω → ℝ := fun k ω =>
    ((M₁ ω).gammaMap y x (Pi.single i 1) k -
      (M₂ ω).gammaMap y x (Pi.single i 1) k) *
      (M₁ ω).gammaMap z y (Pi.single k 1) j
  let V : ι → Ω → ℝ := fun k ω =>
    (M₂ ω).gammaMap y x (Pi.single i 1) k *
      ((M₁ ω).gammaMap z y (Pi.single k 1) j -
        (M₂ ω).gammaMap z y (Pi.single k 1) j)
  let T : ι → Ω → ℝ := fun k ω => U k ω + V k ω
  have hlead : (∫⁻ ω, ‖(M₁ ω).gammaMap z y (Pi.single i 1) j -
      (M₂ ω).gammaMap z y (Pi.single i 1) j‖ₑ ^ p ∂P) ≤
      ENNReal.ofReal (C * δ * parabolicSemigroup.scaleDist z y ^
        (𝒯.deg i - 𝒯.deg j + κ)) ^ p := by
    simpa [hij, mul_assoc, mul_left_comm, mul_comm, Real.rpow_one] using
      (randomModel_gamma_diff_coordinate_moment_le_global_source
        M₁ M₂ D γ κ C δ 1 hp (by omega : p ≤ q)
        (fun a b k l => (hm₁ a b k l).sub (hm₂ a b k l))
        (fun a b hD ha hb ω u v => by
          simpa [Real.rpow_one] using hdiff a b hD ha hb ω u v)
        (fun a b hD ha hb u v => by
          simpa [Real.rpow_one] using hdiffN a b hD ha hb u v) y z hi hj)
  have hprod (k : ι) (hk : k ∈ s) :
      (∫⁻ ω, ‖U k ω‖ₑ ^ p ∂P) ≤
        B k ^ p := by
    have hmem := Finset.mem_filter.mp (Finset.mem_filter.mp hk).1
    have hki := hmem.2.2
    have hjk := hmem.2.1
    have h1 := gammaDiffCoordinateDifferenceMoment (P := P) M₁ M₂ D γ κ C δ
      (q := q) (r := 2 * p) (by omega) hpq
      (fun a b c d => (hm₁ a b c d).sub (hm₂ a b c d)) hdiff hdiffN
      (a := x) (b := y) (k := i) (l := k) hi hki
    have h2 := gammaDiffCoordinateMoment (P := P) M₁ D γ κ C
      (q := q) (r := 2 * p) (by omega) hpq hm₁ hdet₁ hann₁
      (a := y) (b := z) (k := k) (l := j) (lt_trans hki hi) hjk
    dsimp [U]
    have hcore := gammaDiffGood_mixedProductBound (P := P)
      (a := δ * parabolicSemigroup.scaleDist y x ^
        (𝒯.deg i - 𝒯.deg k + (if (i, k) ∈ D then 0 else κ)))
      (b := parabolicSemigroup.scaleDist z y ^
        (𝒯.deg k - 𝒯.deg j + (if (k, j) ∈ D then 0 else κ)))
      ((hm₁ x y i k).sub (hm₂ x y i k)) (hm₁ y z k j) hC hCbar
      (mul_nonneg hδ (Real.rpow_nonneg
        (parabolicSemigroup.scaleDist_nonneg _ _) _))
      (Real.rpow_nonneg (parabolicSemigroup.scaleDist_nonneg _ _) _)
      (by simpa [Pi.sub_apply, mul_assoc] using h1) h2
    simpa [B, mul_assoc, mul_left_comm, mul_comm] using hcore
  have hprod' (k : ι) (hk : k ∈ s) :
      (∫⁻ ω, ‖V k ω‖ₑ ^ p ∂P) ≤
        B k ^ p := by
    have hmem := Finset.mem_filter.mp (Finset.mem_filter.mp hk).1
    have hki := hmem.2.2
    have hjk := hmem.2.1
    have h1 := gammaDiffCoordinateMoment (P := P) M₂ D γ κ C
      (q := q) (r := 2 * p) (by omega) hpq hm₂ hdet₂ hann₂
      (a := x) (b := y) (k := i) (l := k) hi hki
    have h2 := gammaDiffCoordinateDifferenceMoment (P := P) M₁ M₂ D γ κ C δ
      (q := q) (r := 2 * p) (by omega) hpq
      (fun a b c d => (hm₁ a b c d).sub (hm₂ a b c d)) hdiff hdiffN
      (a := y) (b := z) (k := k) (l := j) (lt_trans hki hi) hjk
    dsimp [V]
    have hcore := gammaDiffGood_mixedProductBound (P := P)
      (a := parabolicSemigroup.scaleDist y x ^
        (𝒯.deg i - 𝒯.deg k + (if (i, k) ∈ D then 0 else κ)))
      (b := δ * parabolicSemigroup.scaleDist z y ^
        (𝒯.deg k - 𝒯.deg j + (if (k, j) ∈ D then 0 else κ)))
      (hm₂ x y i k) ((hm₁ y z k j).sub (hm₂ y z k j)) hC hCbar
      (Real.rpow_nonneg (parabolicSemigroup.scaleDist_nonneg _ _) _)
      (mul_nonneg hδ (Real.rpow_nonneg
        (parabolicSemigroup.scaleDist_nonneg _ _) _))
      h1 (by simpa [Pi.sub_apply, mul_assoc] using h2)
    simpa [B, mul_assoc, mul_left_comm, mul_comm] using hcore
  have hUm (k : ι) : AEMeasurable (U k) P :=
    ((hm₁ x y i k).sub (hm₂ x y i k)).mul (hm₁ y z k j)
  have hVm (k : ι) : AEMeasurable (V k) P :=
    (hm₂ x y i k).mul ((hm₁ y z k j).sub (hm₂ y z k j))
  have hTm (k : ι) : AEMeasurable (T k) P := (hUm k).add (hVm k)
  have hsumT : (∫⁻ ω, ‖∑ k ∈ s, T k ω‖ₑ ^ p ∂P) ≤
      (2 : ℝ≥0∞) ^ ((p : ℝ) - 1) *
        ((s.card : ℝ≥0∞) ^ ((p : ℝ) - 1) *
          ∑ k ∈ s, B k ^ p +
          (s.card : ℝ≥0∞) ^ ((p : ℝ) - 1) *
          ∑ k ∈ s, B k ^ p) := by
    simpa [T] using
      (gammaDiffGood_sumPairMoment (P := P) s U V B hp
        (fun k hk => hUm k) (fun k hk => hVm k) hprod hprod')
  have hleadm : AEMeasurable
      (fun ω => (M₁ ω).gammaMap z y (Pi.single i 1) j -
        (M₂ ω).gammaMap z y (Pi.single i 1) j) P :=
    (hm₁ y z i j).sub (hm₂ y z i j)
  let Tsum : Ω → ℝ := fun ω => ∑ k ∈ s, T k ω
  have hsumTm : AEMeasurable Tsum P :=
    Finset.aemeasurable_fun_sum s (fun k hk => hTm k)
  have hdecomp : ∀ ω,
      gammaDiffSplitLeftGoodTerm M₁ M₂ D i j x y z ω =
        ((M₁ ω).gammaMap z y (Pi.single i 1) j -
          (M₂ ω).gammaMap z y (Pi.single i 1) j) + Tsum ω := by
    intro ω
    simp [Tsum, gammaDiffSplitLeftGoodTerm, T, U, V, s]
  have hbound :
      (2 : ℝ≥0∞) ^ ((p : ℝ) - 1) *
        (ENNReal.ofReal (C * δ * parabolicSemigroup.scaleDist z y ^
          (𝒯.deg i - 𝒯.deg j + κ)) ^ p +
          ∫⁻ ω, ‖Tsum ω‖ₑ ^ p ∂P) ≤
        gammaDiffNearLeftGoodBound 𝒯 D κ C Cbar δ p i j x y z := by
    have hlead_le :
        ENNReal.ofReal (C * δ * parabolicSemigroup.scaleDist z y ^
          (𝒯.deg i - 𝒯.deg j + κ)) ^ p ≤
          ENNReal.ofReal (C * δ * parabolicSemigroup.scaleDist z y ^
            (𝒯.deg i - 𝒯.deg j + κ)) ^ p := le_rfl
    have hstep := mul_le_mul_of_nonneg_left
      (add_le_add hlead_le hsumT) (by positivity :
        (0 : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ ((p : ℝ) - 1))
    unfold gammaDiffNearLeftGoodBound
    convert hstep using 1
    simp only [B, s, ite_eq_right hij, Finset.sum_add_distrib, mul_add]
    ac_rfl
  exact gammaDiffSplitLeftGoodTerm_moment_core (P := P) M₁ M₂ D κ C Cbar δ
    i j hp x y z Tsum (∫⁻ ω, ‖Tsum ω‖ₑ ^ p ∂P) hdecomp hlead hleadm
    hsumTm le_rfl hbound

omit [IsProbabilityMeasure P] in
private theorem gammaDiffGoodTerm_moment_core
    {F A T : Ω → ℝ} {p : ℕ} (hp : 1 ≤ p) (target L S : ℝ≥0∞)
    (hdecomp : ∀ ω, F ω = A ω + T ω)
    (hAm : AEMeasurable A P) (hTm : AEMeasurable T P)
    (hlead : (∫⁻ ω, ‖A ω‖ₑ ^ p ∂P) ≤ L)
    (hsum : (∫⁻ ω, ‖T ω‖ₑ ^ p ∂P) ≤ S)
    (hbound : (2 : ℝ≥0∞) ^ ((p : ℝ) - 1) * (L + S) ≤ target) :
    (∫⁻ ω, ‖F ω‖ₑ ^ p ∂P) ≤ target := by
  have hbase : (∫⁻ ω, ‖A ω + T ω‖ₑ ^ p ∂P) ≤
      (2 : ℝ≥0∞) ^ ((p : ℝ) - 1) * (L + S) := by
    refine (gammaDiffGood_addMoment hAm hTm hp).trans ?_
    exact mul_le_mul_of_nonneg_left (add_le_add hlead hsum) (by positivity)
  have heq : (∫⁻ ω, ‖F ω‖ₑ ^ p ∂P) =
      (∫⁻ ω, ‖A ω + T ω‖ₑ ^ p ∂P) := by
    apply lintegral_congr
    intro ω
    rw [hdecomp ω]
  exact heq ▸ hbase.trans hbound

def gammaDiffNearRightGoodBound
    (𝒯 : RegularityStructure ι) (D : Set (ι × ι))
    (κ C Cbar δ : ℝ) (p : ℕ) (i j : ι)
    (x y z : ParabolicSpace) : ℝ≥0∞ :=
  (2 : ℝ≥0∞) ^ ((p : ℝ) - 1) *
    (ENNReal.ofReal (C * δ * parabolicSemigroup.scaleDist y z ^
        (𝒯.deg i - 𝒯.deg j + (if (i, j) ∈ D then 0 else κ))) ^ p +
      ((gammaGoodIntermediate 𝒯 D i j).card : ℝ≥0∞) ^ ((p : ℝ) - 1) *
        (2 : ℝ≥0∞) ^ ((p : ℝ) - 1) *
        ∑ k ∈ gammaGoodIntermediate 𝒯 D i j, (
          ENNReal.ofReal (Cbar * C * δ * (
            parabolicSemigroup.scaleDist y z ^
              (𝒯.deg i - 𝒯.deg k + (if (i, k) ∈ D then 0 else κ)) *
            parabolicSemigroup.scaleDist x y ^
              (𝒯.deg k - 𝒯.deg j + (if (k, j) ∈ D then 0 else κ)))) ^ p +
          ENNReal.ofReal (Cbar * C * δ * (
            parabolicSemigroup.scaleDist y z ^
              (𝒯.deg i - 𝒯.deg k + (if (i, k) ∈ D then 0 else κ)) *
            parabolicSemigroup.scaleDist x y ^
              (𝒯.deg k - 𝒯.deg j + (if (k, j) ∈ D then 0 else κ)))) ^ p))

theorem gammaDiffSplitRightGoodTerm_moment_le
    (M₁ M₂ : Ω → Model 𝒯 parabolicSemigroup) (D : Set (ι × ι))
    (γ κ C Cbar δ : ℝ) {p q : ℕ} (hp : 1 ≤ p) (hpq : 2 * p ≤ q)
    (hC : 0 ≤ C) (hCbar : C ≤ Cbar) (hδ : 0 ≤ δ)
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
    (hij : (i, j) ∉ D) (x y z : ParabolicSpace) :
    (∫⁻ ω, ‖gammaDiffSplitRightGoodTerm M₁ M₂ D i j x y z ω‖ₑ ^ p ∂P) ≤
      gammaDiffNearRightGoodBound 𝒯 D κ C Cbar δ p i j x y z := by
  classical
  let s := gammaGoodIntermediate 𝒯 D i j
  let B : ι → ℝ≥0∞ := fun k =>
    ENNReal.ofReal (Cbar * C * δ *
      (parabolicSemigroup.scaleDist y z ^
        (𝒯.deg i - 𝒯.deg k + (if (i, k) ∈ D then 0 else κ)) *
       parabolicSemigroup.scaleDist x y ^
        (𝒯.deg k - 𝒯.deg j + (if (k, j) ∈ D then 0 else κ))))
  let U : ι → Ω → ℝ := fun k ω =>
    ((M₁ ω).gammaMap y z (Pi.single i 1) k -
      (M₂ ω).gammaMap y z (Pi.single i 1) k) *
      (M₁ ω).gammaMap x y (Pi.single k 1) j
  let V : ι → Ω → ℝ := fun k ω =>
    (M₂ ω).gammaMap y z (Pi.single i 1) k *
      ((M₁ ω).gammaMap x y (Pi.single k 1) j -
        (M₂ ω).gammaMap x y (Pi.single k 1) j)
  let T : ι → Ω → ℝ := fun k ω => U k ω + V k ω
  have hlead : (∫⁻ ω, ‖(M₁ ω).gammaMap y z (Pi.single i 1) j -
      (M₂ ω).gammaMap y z (Pi.single i 1) j‖ₑ ^ p ∂P) ≤
      ENNReal.ofReal (C * δ * parabolicSemigroup.scaleDist y z ^
        (𝒯.deg i - 𝒯.deg j + κ)) ^ p := by
    simpa [hij, mul_assoc, mul_left_comm, mul_comm, Real.rpow_one] using
      (randomModel_gamma_diff_coordinate_moment_le_global_source M₁ M₂ D γ κ C δ 1 hp
        (by omega : p ≤ q) (fun a b k l => (hm₁ a b k l).sub (hm₂ a b k l))
        (fun a b hD ha hb ω u v => by
          simpa [Real.rpow_one] using hdiff a b hD ha hb ω u v)
        (fun a b hD ha hb u v => by
          simpa [Real.rpow_one] using hdiffN a b hD ha hb u v) z y hi hj)
  have hprod (k : ι) (hk : k ∈ s) :
      (∫⁻ ω, ‖U k ω‖ₑ ^ p ∂P) ≤ B k ^ p := by
    have hmem := Finset.mem_filter.mp (Finset.mem_filter.mp hk).1
    have hki := hmem.2.2
    have hjk := hmem.2.1
    have h1 := gammaDiffCoordinateDifferenceMoment (P := P) M₁ M₂ D γ κ C δ
      (q := q) (r := 2 * p) (by omega) hpq
      (fun a b c d => (hm₁ a b c d).sub (hm₂ a b c d)) hdiff hdiffN
      (a := z) (b := y) (k := i) (l := k) hi hki
    have h2 := gammaDiffCoordinateMoment (P := P) M₁ D γ κ C
      (q := q) (r := 2 * p) (by omega) hpq hm₁ hdet₁ hann₁
      (a := y) (b := x) (k := k) (l := j) (lt_trans hki hi) hjk
    dsimp [U]
    have hcore := gammaDiffGood_mixedProductBound (P := P)
      (a := δ * parabolicSemigroup.scaleDist y z ^
        (𝒯.deg i - 𝒯.deg k + (if (i, k) ∈ D then 0 else κ)))
      (b := parabolicSemigroup.scaleDist x y ^
        (𝒯.deg k - 𝒯.deg j + (if (k, j) ∈ D then 0 else κ)))
      ((hm₁ z y i k).sub (hm₂ z y i k)) (hm₁ y x k j) hC hCbar
      (mul_nonneg hδ (Real.rpow_nonneg
        (parabolicSemigroup.scaleDist_nonneg _ _) _))
      (Real.rpow_nonneg (parabolicSemigroup.scaleDist_nonneg _ _) _)
      (by simpa [Pi.sub_apply, mul_assoc] using h1) h2
    simpa [B, mul_assoc, mul_left_comm, mul_comm] using hcore
  have hprod' (k : ι) (hk : k ∈ s) :
      (∫⁻ ω, ‖V k ω‖ₑ ^ p ∂P) ≤ B k ^ p := by
    have hmem := Finset.mem_filter.mp (Finset.mem_filter.mp hk).1
    have hki := hmem.2.2
    have hjk := hmem.2.1
    have h1 := gammaDiffCoordinateMoment (P := P) M₂ D γ κ C
      (q := q) (r := 2 * p) (by omega) hpq hm₂ hdet₂ hann₂
      (a := z) (b := y) (k := i) (l := k) hi hki
    have h2 := gammaDiffCoordinateDifferenceMoment (P := P) M₁ M₂ D γ κ C δ
      (q := q) (r := 2 * p) (by omega) hpq
      (fun a b c d => (hm₁ a b c d).sub (hm₂ a b c d)) hdiff hdiffN
      (a := y) (b := x) (k := k) (l := j) (lt_trans hki hi) hjk
    dsimp [V]
    have hcore := gammaDiffGood_mixedProductBound (P := P)
      (a := parabolicSemigroup.scaleDist y z ^
        (𝒯.deg i - 𝒯.deg k + (if (i, k) ∈ D then 0 else κ)))
      (b := δ * parabolicSemigroup.scaleDist x y ^
        (𝒯.deg k - 𝒯.deg j + (if (k, j) ∈ D then 0 else κ)))
      (hm₂ z y i k) ((hm₁ y x k j).sub (hm₂ y x k j)) hC hCbar
      (Real.rpow_nonneg (parabolicSemigroup.scaleDist_nonneg _ _) _)
      (mul_nonneg hδ (Real.rpow_nonneg
        (parabolicSemigroup.scaleDist_nonneg _ _) _))
      h1 (by simpa [Pi.sub_apply, mul_assoc] using h2)
    simpa [B, mul_assoc, mul_left_comm, mul_comm] using hcore
  have hUm (k : ι) : AEMeasurable (U k) P :=
    ((hm₁ z y i k).sub (hm₂ z y i k)).mul (hm₁ y x k j)
  have hVm (k : ι) : AEMeasurable (V k) P :=
    (hm₂ z y i k).mul ((hm₁ y x k j).sub (hm₂ y x k j))
  have hTm (k : ι) : AEMeasurable (T k) P := (hUm k).add (hVm k)
  have hsumT : (∫⁻ ω, ‖∑ k ∈ s, T k ω‖ₑ ^ p ∂P) ≤
      (2 : ℝ≥0∞) ^ ((p : ℝ) - 1) *
        ((s.card : ℝ≥0∞) ^ ((p : ℝ) - 1) * ∑ k ∈ s, B k ^ p +
          (s.card : ℝ≥0∞) ^ ((p : ℝ) - 1) * ∑ k ∈ s, B k ^ p) := by
    simpa [T] using
      (gammaDiffGood_sumPairMoment (P := P) s U V B hp
        (fun k hk => hUm k) (fun k hk => hVm k) hprod hprod')
  let Tsum : Ω → ℝ := fun ω => ∑ k ∈ s, T k ω
  have hsumTm : AEMeasurable Tsum P :=
    Finset.aemeasurable_fun_sum s (fun k hk => hTm k)
  have hAm : AEMeasurable
      (fun ω => (M₁ ω).gammaMap y z (Pi.single i 1) j -
        (M₂ ω).gammaMap y z (Pi.single i 1) j) P :=
    (hm₁ z y i j).sub (hm₂ z y i j)
  have hdecomp : ∀ ω,
      gammaDiffSplitRightGoodTerm M₁ M₂ D i j x y z ω =
        ((M₁ ω).gammaMap y z (Pi.single i 1) j -
          (M₂ ω).gammaMap y z (Pi.single i 1) j) + Tsum ω := by
    intro ω
    simp [Tsum, gammaDiffSplitRightGoodTerm, T, U, V, s]
  have hbound :
      (2 : ℝ≥0∞) ^ ((p : ℝ) - 1) *
        (ENNReal.ofReal (C * δ * parabolicSemigroup.scaleDist y z ^
          (𝒯.deg i - 𝒯.deg j + κ)) ^ p +
          ∫⁻ ω, ‖Tsum ω‖ₑ ^ p ∂P) ≤
        gammaDiffNearRightGoodBound 𝒯 D κ C Cbar δ p i j x y z := by
    have hlead_le :
        ENNReal.ofReal (C * δ * parabolicSemigroup.scaleDist y z ^
          (𝒯.deg i - 𝒯.deg j + κ)) ^ p ≤
          ENNReal.ofReal (C * δ * parabolicSemigroup.scaleDist y z ^
            (𝒯.deg i - 𝒯.deg j + κ)) ^ p := le_rfl
    have hstep := mul_le_mul_of_nonneg_left
      (add_le_add hlead_le hsumT) (by positivity :
        (0 : ℝ≥0∞) ≤ (2 : ℝ≥0∞) ^ ((p : ℝ) - 1))
    unfold gammaDiffNearRightGoodBound
    convert hstep using 1
    simp only [B, s, ite_eq_right hij, Finset.sum_add_distrib, mul_add]
    ac_rfl
  exact gammaDiffGoodTerm_moment_core (P := P) hp
    (gammaDiffNearRightGoodBound 𝒯 D κ C Cbar δ p i j x y z)
    (ENNReal.ofReal (C * δ * parabolicSemigroup.scaleDist y z ^
      (𝒯.deg i - 𝒯.deg j + κ)) ^ p)
    (∫⁻ ω, ‖Tsum ω‖ₑ ^ p ∂P) hdecomp hAm hsumTm hlead le_rfl hbound

end RegularityStructures

end
