/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.StochasticHeatConvergenceNoiseTranslation
public import Phi43.RegularisedNoise.SmoothVersion.WindowLpTransport
public import Phi43.RegularisedNoise.SmoothVersion.PolynomialGrowth
public import Phi43.RegularisedNoise.SmoothVersion.GaussianVariance
import Mathlib.Analysis.Normed.Ring.InfiniteSum

/-!
# One random bound for all translated Fourier windows

The first Borel--Cantelli lemma is applied on the product of the integer time
index and the real/imaginary four-dimensional frequency lattice. The variance
of a translated physical Fourier mode is bounded by the volume of the SAME
fixed window. Thus one random constant controls all windows with the explicit
time weight `1 + n²`. This is a growth ingredient for
the convergence of the noise potentials (`phi43Noise_cauchy`) [Hai14, Proposition 9.5].
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped ENNReal

namespace RegularityStructures.Phi43

def stochasticHeatShiftedWindowMode (a b : ℝ) (n : ℤ)
    (i : Sum WindowFrequency WindowFrequency) (w : SpaceTime) : ℝ :=
  smoothVersionWindowPhysicalMode a b i (w - ((n : ℝ), 0))

def stochasticHeatShiftedModeWeight (n : ℤ)
    (i : Sum WindowFrequency WindowFrequency) : ℝ :=
  (1 + (n : ℝ) ^ 2) * smoothVersionFrequencyNormSq (i.elim id id) ^ 3

private theorem physicalMode_abs_le (a b : ℝ)
    (i : Sum WindowFrequency WindowFrequency) (w : SpaceTime) :
    |smoothVersionWindowPhysicalMode a b i w| ≤ 1 := by
  cases i with
  | inl k =>
    change |(windowInterval a b).indicator (windowFourierRealModeShift a b k) w| ≤ 1
    by_cases hw : w ∈ windowInterval a b
    · rw [indicator_of_mem hw]
      exact (Complex.abs_re_le_norm _).trans_eq (norm_windowFourierModeShift k w)
    · rw [indicator_of_notMem hw, abs_zero]
      exact zero_le_one
  | inr k =>
    change |(windowInterval a b).indicator (windowFourierImagModeShift a b k) w| ≤ 1
    by_cases hw : w ∈ windowInterval a b
    · rw [indicator_of_mem hw]
      exact (Complex.abs_im_le_norm _).trans_eq (norm_windowFourierModeShift k w)
    · rw [indicator_of_notMem hw, abs_zero]
      exact zero_le_one

theorem memLp_stochasticHeatShiftedWindowMode {a b : ℝ} (hab : a < b)
    (n : ℤ) (i : Sum WindowFrequency WindowFrequency) :
    MemLp (stochasticHeatShiftedWindowMode a b n i) 2 := by
  have he : MemLp (smoothVersionWindowPhysicalMode a b i) 2 := by
    cases i with
    | inl k => exact memLp_windowFourierRealTestMode hab k
    | inr k => exact memLp_windowFourierImagTestMode hab k
  exact he.comp_measurePreserving
    (by simpa only [sub_eq_add_neg] using
      (measurePreserving_add_right (volume : Measure SpaceTime) (-((n : ℝ), 0))))

private theorem physicalMode_integral_sq_le {a b : ℝ} (hab : a < b)
    (i : Sum WindowFrequency WindowFrequency) :
    ∫ w, smoothVersionWindowPhysicalMode a b i w * smoothVersionWindowPhysicalMode a b i w ≤
      ((volume : Measure SpaceTime) (windowInterval a b)).toReal := by
  have he' : MemLp (smoothVersionWindowPhysicalMode a b i) 2 := by
    cases i with
    | inl k => exact memLp_windowFourierRealTestMode hab k
    | inr k => exact memLp_windowFourierImagTestMode hab k
  have hs : MeasurableSet (windowInterval a b) := measurableSet_Ioc.prod MeasurableSet.univ
  have hfin : (volume : Measure SpaceTime) (windowInterval a b) ≠ ⊤ :=
    (lt_of_le_of_lt (measure_mono (Set.prod_mono Ioc_subset_Icc_self subset_rfl))
      ((isCompact_Icc.prod (isCompact_univ : IsCompact (univ : Set Torus3))).measure_lt_top)).ne
  have hi : Integrable ((windowInterval a b).indicator (fun _ : SpaceTime => (1 : ℝ))) :=
    (integrableOn_const (μ := (volume : Measure SpaceTime)) hfin).integrable_indicator hs
  calc
    _ ≤ ∫ w, (windowInterval a b).indicator (fun _ : SpaceTime => (1 : ℝ)) w := by
      apply integral_mono_ae (he'.integrable_mul he') hi
      filter_upwards [] with w
      change smoothVersionWindowPhysicalMode a b i w * smoothVersionWindowPhysicalMode a b i w ≤
        (windowInterval a b).indicator (fun _ : SpaceTime => (1 : ℝ)) w
      by_cases hw : w ∈ windowInterval a b
      · rw [indicator_of_mem hw]
        simpa only [pow_two] using (sq_le_one_iff_abs_le_one _).2 (physicalMode_abs_le a b i w)
      · cases i <;> simp only [smoothVersionWindowPhysicalMode, windowFourierRealTestMode,
          windowFourierImagTestMode, indicator_of_notMem hw, mul_zero, le_refl]
    _ = _ := by
      change (∫ w, (windowInterval a b).indicator (1 : SpaceTime → ℝ) w) = _
      exact integral_indicator_one hs

theorem stochasticHeatShiftedModeWeight_pos (n : ℤ)
    (i : Sum WindowFrequency WindowFrequency) : 0 < stochasticHeatShiftedModeWeight n i := by
  unfold stochasticHeatShiftedModeWeight smoothVersionFrequencyNormSq
  positivity

private theorem summable_shiftedModeWeight_inverse_sq :
    Summable (fun ni : ℤ × Sum WindowFrequency WindowFrequency =>
      (stochasticHeatShiftedModeWeight ni.1 ni.2)⁻¹ ^ 2) := by
  have ht : Summable (fun n : ℤ => ((1 + (n : ℝ) ^ 2) ^ 2)⁻¹) := by
    have h := (summable_smoothVersion_inv_one_add_normSq_pow (d := 1) (r := 2)
      (by norm_num)).comp_injective
        (show Function.Injective (fun n : ℤ => fun _ : Fin 1 => n) from
          fun n m h => congrFun h 0)
    apply h.congr
    intro n
    simp only [Function.comp_apply, Fin.sum_univ_one]
  have hf : Summable (fun i : Sum WindowFrequency WindowFrequency =>
      (smoothVersionFrequencyNormSq (i.elim id id) ^ 6)⁻¹) := by
    have h := summable_smoothVersion_inv_one_add_normSq_pow (d := 4) (r := 6) (by norm_num)
    refine Summable.sum _ ?_ ?_
    · change Summable (fun k : WindowFrequency => (smoothVersionFrequencyNormSq k ^ 6)⁻¹)
      exact h
    · change Summable (fun k : WindowFrequency => (smoothVersionFrequencyNormSq k ^ 6)⁻¹)
      exact h
  apply (ht.mul_of_nonneg hf (fun _ => by positivity) (fun _ => by positivity)).congr
  intro ni
  simp only [stochasticHeatShiftedModeWeight, mul_inv_rev, mul_pow, inv_pow, ← pow_mul]
  ring

theorem whiteNoise_ae_shifted_modes_bound {Ω : Type*} [MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P] {W : (SpaceTime → ℝ) → Ω → ℝ}
    (hW : IsWhiteNoise P W) {a b : ℝ} (hab : a < b) :
    ∀ᵐ ω ∂P, ∃ C : ℝ, 0 ≤ C ∧ ∀ (n : ℤ) (i : Sum WindowFrequency WindowFrequency),
      |W (stochasticHeatShiftedWindowMode a b n i) ω| ≤ C * stochasticHeatShiftedModeWeight n i := by
  let V := ((volume : Measure SpaceTime) (windowInterval a b)).toReal
  have hv : ∀ ni : ℤ × Sum WindowFrequency WindowFrequency,
      ∫ w, stochasticHeatShiftedWindowMode a b ni.1 ni.2 w *
        stochasticHeatShiftedWindowMode a b ni.1 ni.2 w ≤ V := by
    intro ni
    have heq : (∫ w, stochasticHeatShiftedWindowMode a b ni.1 ni.2 w *
        stochasticHeatShiftedWindowMode a b ni.1 ni.2 w) =
        ∫ w, smoothVersionWindowPhysicalMode a b ni.2 w *
          smoothVersionWindowPhysicalMode a b ni.2 w := by
      simpa only [stochasticHeatShiftedWindowMode, sub_eq_add_neg] using
        integral_add_right_eq_self (fun w => smoothVersionWindowPhysicalMode a b ni.2 w *
          smoothVersionWindowPhysicalMode a b ni.2 w) (-((ni.1 : ℝ), 0))
    rw [heq]
    exact physicalMode_integral_sq_le hab ni.2
  have he := whiteNoise_ae_eventually_bound_of_integral_sq_le hW
    (fun ni : ℤ × Sum WindowFrequency WindowFrequency =>
      memLp_stochasticHeatShiftedWindowMode hab ni.1 ni.2) hv
    (fun ni : ℤ × Sum WindowFrequency WindowFrequency => stochasticHeatShiftedModeWeight ni.1 ni.2)
    (fun ni : ℤ × Sum WindowFrequency WindowFrequency => stochasticHeatShiftedModeWeight_pos ni.1 ni.2)
    ((summable_shiftedModeWeight_inverse_sq.mul_right V).tsum_ofReal_ne_top)
  have hall := ae_exists_mul_bound_of_ae_eventually_le
    (fun ni : ℤ × Sum WindowFrequency WindowFrequency =>
      stochasticHeatShiftedModeWeight_pos ni.1 ni.2) he
  filter_upwards [hall] with ω hω
  obtain ⟨C, hC, hbound⟩ := hω
  exact ⟨C, hC, fun n i => hbound (n, i)⟩

end RegularityStructures.Phi43

end
