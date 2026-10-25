/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Probability.ModelKolmogorovPiHalfCellWeightADet
public import RegularityStructures.Probability.ModelKolmogorovPiHalfMomentTools

/-!
# The random remainder of the cell weight: pointwise moments of the summands

`PiHalfMomentHypsA` bundles the four hypotheses of `kolmogorov_modelNorm_of_halves` for one random
model (deterministic and annealed bounds for the diagonal `Π` and for `Γ`). For an index `j` with at
least one random factor, `piHalf_term_pointwise_moment` bounds the `p`-th moment of the summand
`‖(Γ_{w x₀} e_k)_j‖ ‖Q_s Π_w e_j(w)‖` at a fixed `w` by `(max 1 C * C * s^β_j * d(x₀, w)^α_j)^p`,
where `α_j/4 + β_j ≥ (deg k + κbar)/4`.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The four moment hypotheses of `hPiHalf` for one random model `Z`. -/
structure PiHalfMomentHypsA (𝒯 : RegularityStructure ι) (γ κbar : ℝ) (Dπ : Set ι)
    (DΓ : Set (ι × ι)) (q : ℕ) {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : Ω → Model 𝒯 parabolicSemigroup) (C : ℝ) : Prop where
  piDet : ∀ i ∈ Dπ, 𝒯.deg i < γ → ∀ ω, ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x : ParabolicSpace,
    |(Z ω).regPi x (Pi.single i 1) t x| ≤ C * t ^ (𝒯.deg i / parabolicSemigroup.order)
  gammaDet : ∀ i j, (i, j) ∈ DΓ → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i → ∀ ω,
    ∀ x y : ParabolicSpace, |(Z ω).gammaMap y x (Pi.single i 1) j| ≤
      C * parabolicSemigroup.scaleDist y x ^ (𝒯.deg i - 𝒯.deg j)
  piAnn : ∀ i, i ∉ Dπ → 𝒯.deg i < γ → ∀ t ∈ Ioc (0 : ℝ) 1, ∀ x : ParabolicSpace,
    ∫⁻ ω, ‖(Z ω).regPi x (Pi.single i 1) t x‖ₑ ^ q ∂P ≤
      ENNReal.ofReal (C * t ^ ((𝒯.deg i + κbar) / parabolicSemigroup.order)) ^ q
  gammaAnn : ∀ i j, (i, j) ∉ DΓ → 𝒯.deg i < γ → 𝒯.deg j < 𝒯.deg i →
    ∀ x y : ParabolicSpace, ∫⁻ ω, ‖(Z ω).gammaMap y x (Pi.single i 1) j‖ₑ ^ q ∂P ≤
      ENNReal.ofReal (C * parabolicSemigroup.scaleDist y x ^
        (𝒯.deg i - 𝒯.deg j + κbar)) ^ q

open scoped Classical in
/-- The `d(w, x₀)`-exponent of the summand `j`: `deg k - deg j`, plus `κbar` if `Γ` is random. -/
def piHalfRandAlphaA (𝒯 : RegularityStructure ι) (κbar : ℝ) (DΓ : Set (ι × ι)) (k j : ι) : ℝ :=
  (𝒯.deg k - 𝒯.deg j) + if 𝒯.deg j = 𝒯.deg k ∨ (k, j) ∈ DΓ then 0 else κbar

open scoped Classical in
/-- The `s`-exponent of the summand `j`: `(deg j + κbar)/4` if `Π` is random, else `deg j / 4`. -/
def piHalfRandBetaA (𝒯 : RegularityStructure ι) (κbar : ℝ) (Dπ : Set ι) (j : ι) : ℝ :=
  (𝒯.deg j + if j ∈ Dπ then 0 else κbar) / 4

end RegularityStructures

end

public section

open MeasureTheory Set
open scoped ENNReal

namespace RegularityStructures

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A uniformly bounded factor times a factor with a `p`-th moment bound. -/
theorem piHalf_lintegral_mul_pow_le_of_bound
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {a b : Ω → ℝ≥0∞} {A B : ℝ} {p : ℕ}
    (hA : ∀ ω, a ω ≤ ENNReal.ofReal A)
    (hb : ∫⁻ ω, b ω ^ p ∂P ≤ ENNReal.ofReal B ^ p) (hA0 : 0 ≤ A) :
    ∫⁻ ω, (a ω * b ω) ^ p ∂P ≤ ENNReal.ofReal (A * B) ^ p := by
  calc ∫⁻ ω, (a ω * b ω) ^ p ∂P ≤ ∫⁻ ω, ENNReal.ofReal A ^ p * b ω ^ p ∂P :=
        lintegral_mono fun ω => by
          rw [mul_pow]
          exact mul_le_mul_of_nonneg_right (pow_le_pow_left' (hA ω) p) zero_le
    _ = ENNReal.ofReal A ^ p * ∫⁻ ω, b ω ^ p ∂P :=
        lintegral_const_mul' _ _ (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)
    _ ≤ ENNReal.ofReal A ^ p * ENNReal.ofReal B ^ p := mul_le_mul_of_nonneg_left hb zero_le
    _ = ENNReal.ofReal (A * B) ^ p := by
        rw [← mul_pow, ← ENNReal.ofReal_mul hA0]

theorem piHalf_ofReal_pow_le {x y : ℝ} (h : x ≤ y) (p : ℕ) :
    ENNReal.ofReal x ^ p ≤ ENNReal.ofReal y ^ p :=
  pow_le_pow_left' (ENNReal.ofReal_le_ofReal h) p

/-- The scalar bookkeeping behind the three cases: `A * B ≤ max 1 C * C * s^β * d^α`. -/
theorem piHalf_case_const_le {C a b : ℝ} (hC : 0 ≤ C) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    C * b * (C * a) ≤ max 1 C * C * b * a ∧ max 1 C * a * (C * b) ≤ max 1 C * C * b * a := by
  have hm : C ≤ max 1 C := le_max_right _ _
  have hab : 0 ≤ C * a * b := by positivity
  constructor
  · nlinarith [mul_nonneg hab (sub_nonneg.2 hm)]
  · nlinarith [mul_nonneg hab (sub_nonneg.2 hm)]

/-- The pointwise moment of one summand with at least one random factor. -/
theorem piHalf_term_pointwise_moment {𝒯 : RegularityStructure ι} {γ κbar C : ℝ}
    {Dπ : Set ι} {DΓ : Set (ι × ι)} {q : ℕ} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {Z : Ω → Model 𝒯 parabolicSemigroup}
    (hH : PiHalfMomentHypsA 𝒯 γ κbar Dπ DΓ q P Z C) (hC : 0 ≤ C) {k : ι}
    (hkγ : 𝒯.deg k < γ) {p : ℕ} (hp : 1 ≤ p) (hpq : 2 * p ≤ q) {s : ℝ}
    (hs : s ∈ Ioc (0 : ℝ) 1) (x₀ w : ParabolicSpace)
    (hmPi : ∀ j, Measurable fun ω => (Z ω).regPi w (Pi.single j 1) s w)
    (hmGam : ∀ j, Measurable fun ω => (Z ω).gammaMap w x₀ (Pi.single k 1) j)
    {j : ι} (hjk : 𝒯.deg j ≤ 𝒯.deg k)
    (hj : ¬ (j ∈ Dπ ∧ (𝒯.deg j = 𝒯.deg k ∨ (k, j) ∈ DΓ))) :
    ∫⁻ ω, piHalfCellTermA 𝒯 s x₀ k (Z ω) j w ^ p ∂P ≤
      ENNReal.ofReal (max 1 C * C * s ^ piHalfRandBetaA 𝒯 κbar Dπ j *
        parabolicNorm (x₀ - w) ^ piHalfRandAlphaA 𝒯 κbar DΓ k j) ^ p := by
  classical
  have hord : parabolicSemigroup.order = 4 := rfl
  have hs0 : 0 < s := hs.1
  have hjγ : 𝒯.deg j < γ := lt_of_le_of_lt hjk hkγ
  have hd0 : 0 ≤ parabolicNorm (x₀ - w) := parabolicNorm_nonneg _
  have hsd : parabolicSemigroup.scaleDist w x₀ = parabolicNorm (x₀ - w) :=
    piHalf_scaleDist_eq w x₀
  have hmΓ := (hmGam j).aestronglyMeasurable (μ := P)
  have hmPiw := (hmPi j).aestronglyMeasurable (μ := P)
  have hpq1 : p ≤ q := by omega
  have hpos : ∀ a : ℝ, 0 ≤ parabolicNorm (x₀ - w) ^ a := fun a => Real.rpow_nonneg hd0 a
  have hsb : ∀ a : ℝ, 0 ≤ s ^ a := fun a => Real.rpow_nonneg hs0.le a
  by_cases hP : j ∈ Dπ
  · have hG : ¬ (𝒯.deg j = 𝒯.deg k ∨ (k, j) ∈ DΓ) := fun h => hj ⟨hP, h⟩
    have hjlt : 𝒯.deg j < 𝒯.deg k :=
      lt_of_le_of_ne hjk fun h => hG (Or.inl h)
    have hnot : (k, j) ∉ DΓ := fun h => hG (Or.inr h)
    have hα : piHalfRandAlphaA 𝒯 κbar DΓ k j = (𝒯.deg k - 𝒯.deg j) + κbar := by
      simp [piHalfRandAlphaA, hG]
    have hβ : piHalfRandBetaA 𝒯 κbar Dπ j = 𝒯.deg j / 4 := by
      simp [piHalfRandBetaA, hP]
    rw [hα, hβ]
    have hΓq := hH.gammaAnn k j hnot hkγ hjlt x₀ w
    rw [hsd] at hΓq
    have hΓp := piHalf_lintegral_pow_le_of_le hmΓ hp hpq1 hΓq
    have hPiB : ∀ ω, ‖(Z ω).regPi w (Pi.single j 1) s w‖ₑ ≤ ENNReal.ofReal (C * s ^ (𝒯.deg j / 4)) := by
      intro ω
      rw [Real.enorm_eq_ofReal_abs]
      refine ENNReal.ofReal_le_ofReal ?_
      have := hH.piDet j hP hjγ ω s hs w
      rwa [hord] at this
    have h := piHalf_lintegral_mul_pow_le_of_bound (P := P)
      (a := fun ω => ‖(Z ω).regPi w (Pi.single j 1) s w‖ₑ)
      (b := fun ω => ‖(Z ω).gammaMap w x₀ (Pi.single k 1) j‖ₑ) hPiB hΓp
      (mul_nonneg hC (hsb _))
    calc ∫⁻ ω, piHalfCellTermA 𝒯 s x₀ k (Z ω) j w ^ p ∂P
        = ∫⁻ ω, (‖(Z ω).regPi w (Pi.single j 1) s w‖ₑ *
            ‖(Z ω).gammaMap w x₀ (Pi.single k 1) j‖ₑ) ^ p ∂P := by
          refine lintegral_congr fun ω => ?_
          simp only [piHalfCellTermA, mul_comm]
      _ ≤ _ := h
      _ ≤ _ := piHalf_ofReal_pow_le
          (le_trans (piHalf_case_const_le hC (hpos _) (hsb (𝒯.deg j / 4))).1
            (le_of_eq (by ring))) p
  · by_cases hG : 𝒯.deg j = 𝒯.deg k ∨ (k, j) ∈ DΓ
    · -- `Γ` deterministic, `Π` random
      have hα : piHalfRandAlphaA 𝒯 κbar DΓ k j = 𝒯.deg k - 𝒯.deg j := by
        simp [piHalfRandAlphaA, hG]
      have hβ : piHalfRandBetaA 𝒯 κbar Dπ j = (𝒯.deg j + κbar) / 4 := by
        simp [piHalfRandBetaA, hP]
      rw [hα, hβ]
      have hPiq := hH.piAnn j hP hjγ s hs w
      rw [hord] at hPiq
      have hPip := piHalf_lintegral_pow_le_of_le hmPiw hp hpq1 hPiq
      have hΓ : ∀ ω, ‖(Z ω).gammaMap w x₀ (Pi.single k 1) j‖ₑ ≤
          ENNReal.ofReal (max 1 C * parabolicNorm (x₀ - w) ^ (𝒯.deg k - 𝒯.deg j)) := fun ω =>
        piHalf_gamma_enorm_le_of_det hkγ (Z ω)
          (fun i j' h1 h2 h3 x y => hH.gammaDet i j' h1 h2 h3 ω x y) hjk hG x₀ w
      have h := piHalf_lintegral_mul_pow_le_of_bound (P := P)
        (a := fun ω => ‖(Z ω).gammaMap w x₀ (Pi.single k 1) j‖ₑ)
        (b := fun ω => ‖(Z ω).regPi w (Pi.single j 1) s w‖ₑ) hΓ hPip
        (mul_nonneg (le_trans zero_le_one (le_max_left _ _)) (hpos _))
      refine h.trans (piHalf_ofReal_pow_le ?_ p)
      exact le_trans (piHalf_case_const_le hC (hpos _) (hsb ((𝒯.deg j + κbar) / 4))).2
        (le_of_eq (by ring))
    · -- both random
      have hjlt : 𝒯.deg j < 𝒯.deg k :=
        lt_of_le_of_ne hjk fun h => hG (Or.inl h)
      have hnot : (k, j) ∉ DΓ := fun h => hG (Or.inr h)
      have hα : piHalfRandAlphaA 𝒯 κbar DΓ k j = (𝒯.deg k - 𝒯.deg j) + κbar := by
        simp [piHalfRandAlphaA, hG]
      have hβ : piHalfRandBetaA 𝒯 κbar Dπ j = (𝒯.deg j + κbar) / 4 := by
        simp [piHalfRandBetaA, hP]
      rw [hα, hβ]
      have hΓq := hH.gammaAnn k j hnot hkγ hjlt x₀ w
      rw [hsd] at hΓq
      have hPiq := hH.piAnn j hP hjγ s hs w
      rw [hord] at hPiq
      have hGa2 := piHalf_lintegral_pow_le_of_le hmΓ (by omega : 1 ≤ 2 * p) hpq hΓq
      have hPi2 := piHalf_lintegral_pow_le_of_le hmPiw (by omega : 1 ≤ 2 * p) hpq hPiq
      have h := piHalf_lintegral_mul_pow_le (P := P)
        (a := fun ω => ‖(Z ω).gammaMap w x₀ (Pi.single k 1) j‖ₑ)
        (b := fun ω => ‖(Z ω).regPi w (Pi.single j 1) s w‖ₑ) (hmGam j).enorm.aemeasurable
        (hmPi j).enorm.aemeasurable hGa2 hPi2
      calc ∫⁻ ω, piHalfCellTermA 𝒯 s x₀ k (Z ω) j w ^ p ∂P ≤ _ := h
        _ = ENNReal.ofReal (C * parabolicNorm (x₀ - w) ^ (𝒯.deg k - 𝒯.deg j + κbar) *
            (C * s ^ ((𝒯.deg j + κbar) / 4))) ^ p := by
          rw [← mul_pow, ← ENNReal.ofReal_mul (mul_nonneg hC (hpos _))]
        _ ≤ _ := piHalf_ofReal_pow_le
            (le_trans (le_of_eq (by ring))
              (piHalf_case_const_le hC (hpos _) (hsb ((𝒯.deg j + κbar) / 4))).1) p

end RegularityStructures

end
