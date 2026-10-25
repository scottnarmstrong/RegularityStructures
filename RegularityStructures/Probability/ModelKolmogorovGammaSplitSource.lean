/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovGammaSplit
public import RegularityStructures.Probability.ModelKolmogorovSourceScaling
import Mathlib.MeasureTheory.Integral.MeanInequalities
import Mathlib.Analysis.MeanInequalitiesPow
public import Mathlib.Order.CompletePartialOrder

/-!
# Moment bounds for the non-deterministic Chen channels

The good channel is the leading coordinate together with the intermediate
products for which at least one factor is outside `DΓ`.  This module records
its finite-net source envelope.  The complementary two-deterministic-factor
channel is handled pathwise in the annular completion.
-/

@[expose] public noncomputable section

open MeasureTheory Set Classical
open scoped ENNReal NNReal

namespace RegularityStructures

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι]
  [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
  {𝒯 : RegularityStructure ι}

def gammaSplitLeftGoodStepSupAnnulus
    (S : Set ParabolicSpace)
    (M : Ω → Model 𝒯 parabolicSemigroup) (D : Set (ι × ι))
    (i j : ι) (N k : ℕ) (ω : Ω) : ℝ≥0∞ :=
  ⨆ a : gammaCell S (k + 1), ⨆ b : gammaCell S (k + 1),
    if parabolicNorm
        (hsParabolicCellRepresentative S k (hsParabolicCellParent S k a) -
          hsParabolicCellRepresentative S (k + 1) b) ≤ 20 / (2 : ℝ) ^ N then
      ‖gammaSplitLeftGoodTerm (M ω) D i j
          (hsParabolicCellRepresentative S (k + 1) b)
          (hsParabolicCellRepresentative S (k + 1) a)
          (hsParabolicCellRepresentative S k
            (hsParabolicCellParent S k a))‖ₑ
    else 0

def gammaSplitRightGoodStepSupAnnulus
    (S : Set ParabolicSpace)
    (M : Ω → Model 𝒯 parabolicSemigroup) (D : Set (ι × ι))
    (i j : ι) (N k : ℕ) (ω : Ω) : ℝ≥0∞ :=
  ⨆ a : gammaCell S (k + 1), ⨆ b : gammaCell S (k + 1),
    if parabolicNorm
        (hsParabolicCellRepresentative S k (hsParabolicCellParent S k a) -
          hsParabolicCellRepresentative S (k + 1) b) ≤ 20 / (2 : ℝ) ^ N then
      ‖gammaSplitRightGoodTerm (M ω) D i j
          (hsParabolicCellRepresentative S k
            (hsParabolicCellParent S k a))
          (hsParabolicCellRepresentative S k
            (hsParabolicCellParent S k b))
          (hsParabolicCellRepresentative S (k + 1) b)‖ₑ
    else 0

def gammaSplitNearLeftGoodBound
    (𝒯 : RegularityStructure ι) (D : Set (ι × ι))
    (κ C Cbar : ℝ) (p : ℕ) (i j : ι)
    (x y z : ParabolicSpace) : ℝ≥0∞ :=
  (2 : ℝ≥0∞) ^ ((p : ℝ) - 1) *
    (ENNReal.ofReal (C * parabolicSemigroup.scaleDist z y ^
        (𝒯.deg i - 𝒯.deg j + κ)) ^ p +
      ((gammaGoodIntermediate 𝒯 D i j).card : ℝ≥0∞) ^ ((p : ℝ) - 1) *
        ∑ k ∈ gammaGoodIntermediate 𝒯 D i j,
          ENNReal.ofReal (Cbar * C *
            parabolicSemigroup.scaleDist y x ^
              (𝒯.deg i - 𝒯.deg k +
                (if (i, k) ∈ D then 0 else κ)) *
            parabolicSemigroup.scaleDist z y ^
              (𝒯.deg k - 𝒯.deg j +
                (if (k, j) ∈ D then 0 else κ))) ^ p)

def gammaSplitNearRightGoodBound
    (𝒯 : RegularityStructure ι) (D : Set (ι × ι))
    (κ C Cbar : ℝ) (p : ℕ) (i j : ι)
    (x y z : ParabolicSpace) : ℝ≥0∞ :=
  (2 : ℝ≥0∞) ^ ((p : ℝ) - 1) *
    (ENNReal.ofReal (C * parabolicSemigroup.scaleDist y z ^
        (𝒯.deg i - 𝒯.deg j + κ)) ^ p +
      ((gammaGoodIntermediate 𝒯 D i j).card : ℝ≥0∞) ^ ((p : ℝ) - 1) *
        ∑ k ∈ gammaGoodIntermediate 𝒯 D i j,
          ENNReal.ofReal (Cbar * C *
            parabolicSemigroup.scaleDist y z ^
              (𝒯.deg i - 𝒯.deg k +
                (if (i, k) ∈ D then 0 else κ)) *
            parabolicSemigroup.scaleDist x y ^
              (𝒯.deg k - 𝒯.deg j +
                (if (k, j) ∈ D then 0 else κ))) ^ p)

omit [IsProbabilityMeasure P] in
private theorem gammaSplit_productMoment
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

omit [Fintype ι] [DecidableEq ι] [IsProbabilityMeasure P] in
private theorem gammaSplit_sumMoment
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
theorem gammaSplit_addMoment_le
    {f g : Ω → ℝ} (hf : AEMeasurable f P) (hg : AEMeasurable g P)
    {p : ℕ} (hp : 1 ≤ p) :
    (∫⁻ ω, ‖f ω + g ω‖ₑ ^ p ∂P) ≤
      (2 : ℝ≥0∞) ^ ((p : ℝ) - 1) *
        ((∫⁻ ω, ‖f ω‖ₑ ^ p ∂P) +
          ∫⁻ ω, ‖g ω‖ₑ ^ p ∂P) := by
  have hpoint (ω : Ω) : ‖f ω + g ω‖ₑ ^ p ≤
      (2 : ℝ≥0∞) ^ ((p : ℝ) - 1) *
        (‖f ω‖ₑ ^ p + ‖g ω‖ₑ ^ p) :=
    (ENNReal.pow_le_pow_left (enorm_add_le _ _)).trans (by
      simpa only [ENNReal.rpow_natCast] using
        ENNReal.rpow_add_le_mul_rpow_add_rpow (‖f ω‖ₑ) (‖g ω‖ₑ)
          (show (1 : ℝ) ≤ p by exact_mod_cast hp))
  refine (lintegral_mono hpoint).trans ?_
  rw [lintegral_const_mul'' (f := fun ω => ‖f ω‖ₑ ^ p + ‖g ω‖ₑ ^ p) _
    ((hf.enorm.pow_const p).add (hg.enorm.pow_const p)),
    lintegral_add_left' (f := fun ω => ‖f ω‖ₑ ^ p) (hf.enorm.pow_const p)]

theorem gammaSplitLeftGoodTerm_moment_le
    (M : Ω → Model 𝒯 parabolicSemigroup) (D : Set (ι × ι))
    (γ κ C Cbar : ℝ) {p q : ℕ} (hp : 1 ≤ p) (hpq : 2 * p ≤ q)
    (hC : 0 ≤ C) (hCbar : C ≤ Cbar)
    (hm : ∀ x y i j, AEMeasurable
      (fun ω => (M ω).gammaMap y x (Pi.single i 1) j) P)
    (hdet : ∀ i j, (i, j) ∈ D → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i →
      ∀ ω x y, |(M ω).gammaMap y x (Pi.single i 1) j| ≤
        C * parabolicSemigroup.scaleDist y x ^ (𝒯.deg i - 𝒯.deg j))
    (hann : ∀ i j, (i, j) ∉ D → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i → ∀ x y,
      (∫⁻ ω, ‖(M ω).gammaMap y x (Pi.single i 1) j‖ₑ ^ q ∂P) ≤
        ENNReal.ofReal (C * parabolicSemigroup.scaleDist y x ^
          (𝒯.deg i - 𝒯.deg j + κ)) ^ q)
    (i j : ι) (hi : 𝒯.deg i < γ) (hj : 𝒯.deg j < 𝒯.deg i)
    (hij : (i, j) ∉ D) (x y z : ParabolicSpace) :
    (∫⁻ ω, ‖gammaSplitLeftGoodTerm (M ω) D i j x y z‖ₑ ^ p ∂P) ≤
      gammaSplitNearLeftGoodBound 𝒯 D κ C Cbar p i j x y z := by
  let s := gammaGoodIntermediate 𝒯 D i j
  let T : ι → Ω → ℝ := fun k ω =>
    (M ω).gammaMap y x (Pi.single i 1) k *
      (M ω).gammaMap z y (Pi.single k 1) j
  have hlead := randomModel_gamma_coordinate_moment_le_global_source
    M D γ κ C hp (by omega : p ≤ q) hm hdet hann y z hi hj
  have hprod (k : ι) (hk : k ∈ s) :
      (∫⁻ ω, ‖T k ω‖ₑ ^ p ∂P) ≤
        ENNReal.ofReal (Cbar * C *
          parabolicSemigroup.scaleDist y x ^
            (𝒯.deg i - 𝒯.deg k + (if (i, k) ∈ D then 0 else κ)) *
          parabolicSemigroup.scaleDist z y ^
            (𝒯.deg k - 𝒯.deg j + (if (k, j) ∈ D then 0 else κ))) ^ p := by
    have hinter := Finset.mem_filter.mp (Finset.mem_filter.mp hk).1
    have hki : 𝒯.deg k < 𝒯.deg i := hinter.2.2
    have hjk : 𝒯.deg j < 𝒯.deg k := hinter.2.1
    have h1 := randomModel_gamma_coordinate_moment_le_global_source
      M D γ κ C (p := 2 * p) (q := q) (by omega) hpq hm hdet hann x y hi hki
    have h2 := randomModel_gamma_coordinate_moment_le_global_source
      M D γ κ C (p := 2 * p) (q := q) (by omega) hpq hm hdet hann y z
      (lt_trans hki hi) hjk
    have hprod := gammaSplit_productMoment (P := P)
      (hm x y i k) (hm y z k j) p
    dsimp [T]
    calc
      _ ≤ (∫⁻ ω, ‖(M ω).gammaMap y x (Pi.single i 1) k‖ₑ ^ (2 * p) ∂P) ^
          (1 / 2 : ℝ) *
          (∫⁻ ω, ‖(M ω).gammaMap z y (Pi.single k 1) j‖ₑ ^ (2 * p) ∂P) ^
            (1 / 2 : ℝ) := hprod
      _ ≤ (ENNReal.ofReal (C * parabolicSemigroup.scaleDist y x ^
            (𝒯.deg i - 𝒯.deg k + (if (i, k) ∈ D then 0 else κ))) ^ (2 * p)) ^
          (1 / 2 : ℝ) *
          (ENNReal.ofReal (C * parabolicSemigroup.scaleDist z y ^
            (𝒯.deg k - 𝒯.deg j + (if (k, j) ∈ D then 0 else κ))) ^ (2 * p)) ^
            (1 / 2 : ℝ) := by
        gcongr
      _ ≤ _ := ennreal_two_source_product_le_of_upperBound hC hCbar
        (Real.rpow_nonneg (parabolicSemigroup.scaleDist_nonneg _ _) _)
        (Real.rpow_nonneg (parabolicSemigroup.scaleDist_nonneg _ _) _)
  have hsum := gammaSplit_sumMoment s T
    (fun k hk => (hm x y i k).mul (hm y z k j)) hp
  have hsum' : (∫⁻ ω, ‖∑ k ∈ s, T k ω‖ₑ ^ p ∂P) ≤
      ((s.card : ℝ≥0∞) ^ ((p : ℝ) - 1)) *
        ∑ k ∈ s, ENNReal.ofReal (Cbar * C *
          parabolicSemigroup.scaleDist y x ^
            (𝒯.deg i - 𝒯.deg k + (if (i, k) ∈ D then 0 else κ)) *
          parabolicSemigroup.scaleDist z y ^
            (𝒯.deg k - 𝒯.deg j + (if (k, j) ∈ D then 0 else κ))) ^ p := by
    exact hsum.trans
      (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hprod) zero_le)
  have hlead' : (∫⁻ ω, ‖(M ω).gammaMap z y (Pi.single i 1) j‖ₑ ^ p ∂P) ≤
      ENNReal.ofReal (C * parabolicSemigroup.scaleDist z y ^
        (𝒯.deg i - 𝒯.deg j + κ)) ^ p := by
    simpa [hij] using hlead
  have hleadmeas : AEMeasurable
      (fun ω => (M ω).gammaMap z y (Pi.single i 1) j) P := hm y z i j
  have hsummeas : AEMeasurable (fun ω => ∑ k ∈ s, T k ω) P :=
    Finset.aemeasurable_fun_sum s (fun k hk => (hm x y i k).mul (hm y z k j))
  calc
    _ = (∫⁻ ω, ‖(M ω).gammaMap z y (Pi.single i 1) j +
        ∑ k ∈ s, T k ω‖ₑ ^ p ∂P) := by
      rfl
    _ ≤ (2 : ℝ≥0∞) ^ ((p : ℝ) - 1) *
        ((∫⁻ ω, ‖(M ω).gammaMap z y (Pi.single i 1) j‖ₑ ^ p ∂P) +
          ∫⁻ ω, ‖∑ k ∈ s, T k ω‖ₑ ^ p ∂P) :=
      gammaSplit_addMoment_le hleadmeas hsummeas hp
    _ ≤ (2 : ℝ≥0∞) ^ ((p : ℝ) - 1) *
        (ENNReal.ofReal (C * parabolicSemigroup.scaleDist z y ^
          (𝒯.deg i - 𝒯.deg j + κ)) ^ p +
          ∫⁻ ω, ‖∑ k ∈ s, T k ω‖ₑ ^ p ∂P) :=
      by gcongr
    _ ≤ gammaSplitNearLeftGoodBound 𝒯 D κ C Cbar p i j x y z := by
      simpa [gammaSplitNearLeftGoodBound, s] using
        (mul_le_mul_of_nonneg_left (add_le_add le_rfl hsum') zero_le)

theorem gammaSplitRightGoodTerm_moment_le
    (M : Ω → Model 𝒯 parabolicSemigroup) (D : Set (ι × ι))
    (γ κ C Cbar : ℝ) {p q : ℕ} (hp : 1 ≤ p) (hpq : 2 * p ≤ q)
    (hC : 0 ≤ C) (hCbar : C ≤ Cbar)
    (hm : ∀ x y i j, AEMeasurable
      (fun ω => (M ω).gammaMap y x (Pi.single i 1) j) P)
    (hdet : ∀ i j, (i, j) ∈ D → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i →
      ∀ ω x y, |(M ω).gammaMap y x (Pi.single i 1) j| ≤
        C * parabolicSemigroup.scaleDist y x ^ (𝒯.deg i - 𝒯.deg j))
    (hann : ∀ i j, (i, j) ∉ D → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i → ∀ x y,
      (∫⁻ ω, ‖(M ω).gammaMap y x (Pi.single i 1) j‖ₑ ^ q ∂P) ≤
        ENNReal.ofReal (C * parabolicSemigroup.scaleDist y x ^
          (𝒯.deg i - 𝒯.deg j + κ)) ^ q)
    (i j : ι) (hi : 𝒯.deg i < γ) (hj : 𝒯.deg j < 𝒯.deg i)
    (hij : (i, j) ∉ D) (x y z : ParabolicSpace) :
    (∫⁻ ω, ‖gammaSplitRightGoodTerm (M ω) D i j x y z‖ₑ ^ p ∂P) ≤
      gammaSplitNearRightGoodBound 𝒯 D κ C Cbar p i j x y z := by
  let s := gammaGoodIntermediate 𝒯 D i j
  let T : ι → Ω → ℝ := fun k ω =>
    (M ω).gammaMap y z (Pi.single i 1) k *
      (M ω).gammaMap x y (Pi.single k 1) j
  have hlead := randomModel_gamma_coordinate_moment_le_global_source
    M D γ κ C hp (by omega : p ≤ q) hm hdet hann z y hi hj
  have hprod (k : ι) (hk : k ∈ s) :
      (∫⁻ ω, ‖T k ω‖ₑ ^ p ∂P) ≤
        ENNReal.ofReal (Cbar * C *
          parabolicSemigroup.scaleDist y z ^
            (𝒯.deg i - 𝒯.deg k + (if (i, k) ∈ D then 0 else κ)) *
          parabolicSemigroup.scaleDist x y ^
            (𝒯.deg k - 𝒯.deg j + (if (k, j) ∈ D then 0 else κ))) ^ p := by
    have hinter := Finset.mem_filter.mp (Finset.mem_filter.mp hk).1
    have hki : 𝒯.deg k < 𝒯.deg i := hinter.2.2
    have hjk : 𝒯.deg j < 𝒯.deg k := hinter.2.1
    have h1 := randomModel_gamma_coordinate_moment_le_global_source
      M D γ κ C (p := 2 * p) (q := q) (by omega) hpq hm hdet hann z y hi hki
    have h2 := randomModel_gamma_coordinate_moment_le_global_source
      M D γ κ C (p := 2 * p) (q := q) (by omega) hpq hm hdet hann y x
      (lt_trans hki hi) hjk
    have hprod := gammaSplit_productMoment (P := P)
      (hm z y i k) (hm y x k j) p
    dsimp [T]
    calc
      _ ≤ (∫⁻ ω, ‖(M ω).gammaMap y z (Pi.single i 1) k‖ₑ ^ (2 * p) ∂P) ^
          (1 / 2 : ℝ) *
          (∫⁻ ω, ‖(M ω).gammaMap x y (Pi.single k 1) j‖ₑ ^ (2 * p) ∂P) ^
            (1 / 2 : ℝ) := hprod
      _ ≤ (ENNReal.ofReal (C * parabolicSemigroup.scaleDist y z ^
            (𝒯.deg i - 𝒯.deg k + (if (i, k) ∈ D then 0 else κ))) ^ (2 * p)) ^
          (1 / 2 : ℝ) *
          (ENNReal.ofReal (C * parabolicSemigroup.scaleDist x y ^
            (𝒯.deg k - 𝒯.deg j + (if (k, j) ∈ D then 0 else κ))) ^ (2 * p)) ^
            (1 / 2 : ℝ) := by
        gcongr
      _ ≤ _ := ennreal_two_source_product_le_of_upperBound hC hCbar
        (Real.rpow_nonneg (parabolicSemigroup.scaleDist_nonneg _ _) _)
        (Real.rpow_nonneg (parabolicSemigroup.scaleDist_nonneg _ _) _)
  have hsum := gammaSplit_sumMoment s T
    (fun k hk => (hm z y i k).mul (hm y x k j)) hp
  have hsum' : (∫⁻ ω, ‖∑ k ∈ s, T k ω‖ₑ ^ p ∂P) ≤
      ((s.card : ℝ≥0∞) ^ ((p : ℝ) - 1)) *
        ∑ k ∈ s, ENNReal.ofReal (Cbar * C *
          parabolicSemigroup.scaleDist y z ^
            (𝒯.deg i - 𝒯.deg k + (if (i, k) ∈ D then 0 else κ)) *
          parabolicSemigroup.scaleDist x y ^
            (𝒯.deg k - 𝒯.deg j + (if (k, j) ∈ D then 0 else κ))) ^ p := by
    exact hsum.trans
      (mul_le_mul_of_nonneg_left (Finset.sum_le_sum hprod) zero_le)
  have hlead' : (∫⁻ ω, ‖(M ω).gammaMap y z (Pi.single i 1) j‖ₑ ^ p ∂P) ≤
      ENNReal.ofReal (C * parabolicSemigroup.scaleDist y z ^
        (𝒯.deg i - 𝒯.deg j + κ)) ^ p := by
    simpa [hij] using hlead
  have hleadmeas : AEMeasurable
      (fun ω => (M ω).gammaMap y z (Pi.single i 1) j) P := hm z y i j
  have hsummeas : AEMeasurable (fun ω => ∑ k ∈ s, T k ω) P :=
    Finset.aemeasurable_fun_sum s (fun k hk => (hm z y i k).mul (hm y x k j))
  calc
    _ = (∫⁻ ω, ‖(M ω).gammaMap y z (Pi.single i 1) j +
        ∑ k ∈ s, T k ω‖ₑ ^ p ∂P) := by
      rfl
    _ ≤ (2 : ℝ≥0∞) ^ ((p : ℝ) - 1) *
        ((∫⁻ ω, ‖(M ω).gammaMap y z (Pi.single i 1) j‖ₑ ^ p ∂P) +
          ∫⁻ ω, ‖∑ k ∈ s, T k ω‖ₑ ^ p ∂P) :=
      gammaSplit_addMoment_le hleadmeas hsummeas hp
    _ ≤ (2 : ℝ≥0∞) ^ ((p : ℝ) - 1) *
        (ENNReal.ofReal (C * parabolicSemigroup.scaleDist y z ^
          (𝒯.deg i - 𝒯.deg j + κ)) ^ p +
          ∫⁻ ω, ‖∑ k ∈ s, T k ω‖ₑ ^ p ∂P) := by
      gcongr
    _ ≤ gammaSplitNearRightGoodBound 𝒯 D κ C Cbar p i j x y z := by
      simpa [gammaSplitNearRightGoodBound, s] using
        (mul_le_mul_of_nonneg_left (add_le_add le_rfl hsum') zero_le)

omit [MeasurableSpace Ω] in
theorem gammaSplitLeftBadTerm_enorm_le_of_DGamma
    (M : Ω → Model 𝒯 parabolicSemigroup) (D : Set (ι × ι))
    (γ C : ℝ)
    (hdet : ∀ i j, (i, j) ∈ D → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i →
      ∀ ω x y, |(M ω).gammaMap y x (Pi.single i 1) j| ≤
        C * parabolicSemigroup.scaleDist y x ^ (𝒯.deg i - 𝒯.deg j))
    (i j : ι) (hi : 𝒯.deg i < γ) (_hj : 𝒯.deg j < 𝒯.deg i)
    (x y z : ParabolicSpace) (ω : Ω) :
    ‖gammaSplitLeftBadTerm (M ω) D i j x y z‖ₑ ≤
      ∑ k ∈ gammaBadIntermediate 𝒯 D i j,
        ENNReal.ofReal (C * parabolicSemigroup.scaleDist y x ^
          (𝒯.deg i - 𝒯.deg k)) *
        ENNReal.ofReal (C * parabolicSemigroup.scaleDist z y ^
          (𝒯.deg k - 𝒯.deg j)) := by
  classical
  unfold gammaSplitLeftBadTerm
  refine (enorm_sum_le _ _).trans (Finset.sum_le_sum ?_)
  intro k hk
  have hmem := Finset.mem_filter.mp (Finset.mem_filter.mp hk).1
  have hki : 𝒯.deg k < 𝒯.deg i := hmem.2.2
  have hjk : 𝒯.deg j < 𝒯.deg k := hmem.2.1
  have h1 := hdet i k (Finset.mem_filter.mp hk).2.1 hi hki ω x y
  have h2 := hdet k j (Finset.mem_filter.mp hk).2.2 (lt_trans hki hi) hjk ω y z
  rw [enorm_mul, Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
  exact mul_le_mul
    (ENNReal.ofReal_le_ofReal h1) (ENNReal.ofReal_le_ofReal h2)
    (by positivity) (by positivity)

omit [MeasurableSpace Ω] in
theorem gammaSplitRightBadTerm_enorm_le_of_DGamma
    (M : Ω → Model 𝒯 parabolicSemigroup) (D : Set (ι × ι))
    (γ C : ℝ)
    (hdet : ∀ i j, (i, j) ∈ D → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i →
      ∀ ω x y, |(M ω).gammaMap y x (Pi.single i 1) j| ≤
        C * parabolicSemigroup.scaleDist y x ^ (𝒯.deg i - 𝒯.deg j))
    (i j : ι) (hi : 𝒯.deg i < γ) (_hj : 𝒯.deg j < 𝒯.deg i)
    (x y z : ParabolicSpace) (ω : Ω) :
    ‖gammaSplitRightBadTerm (M ω) D i j x y z‖ₑ ≤
      ∑ k ∈ gammaBadIntermediate 𝒯 D i j,
        ENNReal.ofReal (C * parabolicSemigroup.scaleDist y z ^
          (𝒯.deg i - 𝒯.deg k)) *
        ENNReal.ofReal (C * parabolicSemigroup.scaleDist x y ^
          (𝒯.deg k - 𝒯.deg j)) := by
  classical
  unfold gammaSplitRightBadTerm
  refine (enorm_sum_le _ _).trans (Finset.sum_le_sum ?_)
  intro k hk
  have hmem := Finset.mem_filter.mp (Finset.mem_filter.mp hk).1
  have hki : 𝒯.deg k < 𝒯.deg i := hmem.2.2
  have hjk : 𝒯.deg j < 𝒯.deg k := hmem.2.1
  have h1 := hdet i k (Finset.mem_filter.mp hk).2.1 hi hki ω z y
  have h2 := hdet k j (Finset.mem_filter.mp hk).2.2 (lt_trans hki hi) hjk ω y x
  rw [enorm_mul, Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs]
  exact mul_le_mul
    (ENNReal.ofReal_le_ofReal h1) (ENNReal.ofReal_le_ofReal h2)
    (by positivity) (by positivity)

omit [IsProbabilityMeasure P] in
theorem gammaSplitLeftGoodStepSupAnnulus_aemeasurable
    (S : Set ParabolicSpace)
    (M : Ω → Model 𝒯 parabolicSemigroup) (D : Set (ι × ι))
    (i j : ι) (N k : ℕ)
    (hm : ∀ x y a b, AEMeasurable
      (fun ω => (M ω).gammaMap x y (Pi.single a 1) b) P) :
    AEMeasurable (gammaSplitLeftGoodStepSupAnnulus S M D i j N k) P := by
  unfold gammaSplitLeftGoodStepSupAnnulus
  apply AEMeasurable.iSup
  intro a
  apply AEMeasurable.iSup
  intro b
  split_ifs
  · unfold gammaSplitLeftGoodTerm
    apply AEMeasurable.enorm
    apply AEMeasurable.add
    · exact hm _ _ i j
    · apply Finset.aemeasurable_fun_sum
      intro l hl
      exact (hm _ _ i l).mul (hm _ _ l j)
  · exact aemeasurable_const

omit [IsProbabilityMeasure P] in
theorem gammaSplitRightGoodStepSupAnnulus_aemeasurable
    (S : Set ParabolicSpace)
    (M : Ω → Model 𝒯 parabolicSemigroup) (D : Set (ι × ι))
    (i j : ι) (N k : ℕ)
    (hm : ∀ x y a b, AEMeasurable
      (fun ω => (M ω).gammaMap x y (Pi.single a 1) b) P) :
    AEMeasurable (gammaSplitRightGoodStepSupAnnulus S M D i j N k) P := by
  unfold gammaSplitRightGoodStepSupAnnulus
  apply AEMeasurable.iSup
  intro a
  apply AEMeasurable.iSup
  intro b
  split_ifs
  · unfold gammaSplitRightGoodTerm
    apply AEMeasurable.enorm
    apply AEMeasurable.add
    · exact hm _ _ i j
    · apply Finset.aemeasurable_fun_sum
      intro l hl
      exact (hm _ _ i l).mul (hm _ _ l j)
  · exact aemeasurable_const

end RegularityStructures

end
