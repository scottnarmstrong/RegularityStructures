/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.RegularisedNoise.SmoothVersion.WindowLpTransport
public import Phi43.RegularisedNoise.SmoothVersion.Approximation
public import Phi43.RegularisedNoise.SmoothVersion.PolynomialGrowth
public import Phi43.RegularisedNoise.SmoothVersion.GaussianVariance
public import Phi43.ClassicalSolution.PeriodiseSupport
public import Phi43.RegularisedNoise.Combined

/-!
# The smooth modification for a periodised mollifier

This module assembles the finite-window Fourier certificates into the exact W2 statement.  The
countable window patching is the formal counterpart of the local construction in Hairer (2014),
Theorem 1.15 and Definition 2.4.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open scoped BigOperators ComplexConjugate ENNReal Topology

namespace RegularityStructures.Phi43

private theorem smoothVersion_window_measure_ne_top {a b : ℝ} (_hab : a < b) :
    (volume : Measure SpaceTime) (windowInterval a b) ≠ (⊤ : ENNReal) := by
  have hcompact : IsCompact (Icc a b ×ˢ (Set.univ : Set Torus3)) :=
    isCompact_Icc.prod isCompact_univ
  have hfinite : (volume : Measure SpaceTime)
      (Icc a b ×ˢ (Set.univ : Set Torus3)) < (⊤ : ENNReal) :=
    hcompact.measure_lt_top
  apply (lt_of_le_of_lt (measure_mono (μ := (volume : Measure SpaceTime)) ?_) hfinite).ne
  exact Set.prod_mono Ioc_subset_Icc_self subset_rfl

private theorem smoothVersion_windowPhysicalMode_abs_le {a b : ℝ} (_hab : a < b)
    (i : Sum WindowFrequency WindowFrequency) (w : SpaceTime) :
    |smoothVersionWindowPhysicalMode a b i w| ≤ 1 := by
  cases i with
  | inl k =>
      simp only [smoothVersionWindowPhysicalMode]
      unfold windowFourierRealTestMode
      by_cases hw : w ∈ windowInterval a b
      · rw [Set.indicator_of_mem hw]
        unfold windowFourierRealModeShift
        exact (Complex.abs_re_le_norm (windowFourierModeShift a b k w)).trans_eq
          (norm_windowFourierModeShift k w)
      · simp [hw]
  | inr k =>
      simp only [smoothVersionWindowPhysicalMode]
      unfold windowFourierImagTestMode
      by_cases hw : w ∈ windowInterval a b
      · rw [Set.indicator_of_mem hw]
        unfold windowFourierImagModeShift
        exact (Complex.abs_im_le_norm (windowFourierModeShift a b k w)).trans_eq
          (norm_windowFourierModeShift k w)
      · simp [hw]

private theorem smoothVersion_windowPhysicalMode_integral_sq_le {a b : ℝ} (hab : a < b)
    (i : Sum WindowFrequency WindowFrequency) :
    ∫ w, smoothVersionWindowPhysicalMode a b i w *
      smoothVersionWindowPhysicalMode a b i w ≤
        ENNReal.toReal ((volume : Measure SpaceTime) (windowInterval a b)) := by
  have hmeas : MeasurableSet (windowInterval a b) :=
    measurableSet_Ioc.prod MeasurableSet.univ
  have hupper : Integrable ((windowInterval a b).indicator
      (fun _ : SpaceTime => (1 : ℝ))) := by
    exact (integrableOn_const (μ := (volume : Measure SpaceTime))
      (smoothVersion_window_measure_ne_top hab)).integrable_indicator hmeas
  have hlower : Integrable (fun w => smoothVersionWindowPhysicalMode a b i w *
      smoothVersionWindowPhysicalMode a b i w) := by
    cases i with
    | inl k =>
        exact (memLp_windowFourierRealTestMode hab k).integrable_mul
          (memLp_windowFourierRealTestMode hab k)
    | inr k =>
        exact (memLp_windowFourierImagTestMode hab k).integrable_mul
          (memLp_windowFourierImagTestMode hab k)
  have hmono : ∫ w, smoothVersionWindowPhysicalMode a b i w *
      smoothVersionWindowPhysicalMode a b i w ≤
        ∫ w, (windowInterval a b).indicator (fun _ : SpaceTime => (1 : ℝ)) w := by
    apply integral_mono_ae hlower hupper
    filter_upwards [] with w
    by_cases hw : w ∈ windowInterval a b
    · cases i with
      | inl k =>
          simp only [smoothVersionWindowPhysicalMode]
          rw [Set.indicator_of_mem hw]
          have h := smoothVersion_windowPhysicalMode_abs_le hab (Sum.inl k) w
          have hsq := (sq_le_one_iff_abs_le_one _).2 h
          simpa only [pow_two, smoothVersionWindowPhysicalMode] using hsq
      | inr k =>
          simp only [smoothVersionWindowPhysicalMode]
          rw [Set.indicator_of_mem hw]
          have h := smoothVersion_windowPhysicalMode_abs_le hab (Sum.inr k) w
          have hsq := (sq_le_one_iff_abs_le_one _).2 h
          simpa only [pow_two, smoothVersionWindowPhysicalMode] using hsq
    · cases i <;>
        simp [smoothVersionWindowPhysicalMode, windowFourierRealTestMode,
          windowFourierImagTestMode, hw]
  change (∫ w, smoothVersionWindowPhysicalMode a b i w *
      smoothVersionWindowPhysicalMode a b i w) ≤
      ∫ w, (windowInterval a b).indicator (1 : SpaceTime → ℝ) w at hmono
  rw [integral_indicator_one hmeas] at hmono
  simpa [Measure.real] using hmono

private theorem smoothVersion_window_fourier_weighted_summable
    {Phi : SpaceTime → ℝ} (hPhi : IsSmoothOnSpaceTime Phi)
    {R N : ℝ} (hR : ∀ q : SpaceTime, R < |q.1| → Phi q = 0)
    (hR0 : 0 ≤ R) (hN : 0 < N) {a b : ℝ}
    (ha : a = -N - R - 1) (hb : b = N + R + 1) (p : ℕ)
    (z : SpaceTime) :
    Summable (fun i : Sum WindowFrequency WindowFrequency =>
      smoothVersionFrequencyNormSq (match i with
        | Sum.inl k => k
        | Sum.inr k => k) ^ p *
        |smoothVersionWindowSeriesTerm Phi a b i z|) := by
  obtain ⟨C, hC0, hC⟩ := smoothVersion_windowCoefficientAmplitude_decay
    hPhi hR hR0 hN a b ha hb (6 + 2 * p)
  have hweighted := summable_smoothVersion_fourier_weighted_of_coordinate_decay p
    ⟨‖smoothVersionWindowCoefficientAmplitude Phi a b 0‖,
      norm_nonneg _, le_rfl⟩
    ⟨C, hC0, fun i k hki => hC i k hki⟩
  have hnorm : ∀ k : WindowFrequency,
      ‖smoothVersionWindowCoefficientFormula Phi a b k z‖ =
        ‖smoothVersionWindowCoefficientAmplitude Phi a b k‖ := by
    intro k
    have h : smoothVersionWindowCoefficientFormula Phi a b k z =
        smoothVersionWindowCoefficientAmplitude Phi a b k •
          conj (globalWindowFourierMode (b - a) k z) := by
      unfold smoothVersionWindowCoefficientFormula smoothVersionWindowCoefficientAmplitude
      simp [Algebra.smul_def]
      ring
    rw [h, norm_smul, Complex.norm_conj]
    unfold globalWindowFourierMode
    simp only [norm_mul, fourier_apply, Circle.norm_coe, norm_prod]
    simp
  have hreal : Summable (fun k : WindowFrequency =>
      smoothVersionFrequencyNormSq k ^ p *
        |(smoothVersionWindowCoefficientFormula Phi a b k z).re|) := by
    apply hweighted.of_norm_bounded
    intro k
    have hS : 0 ≤ smoothVersionFrequencyNormSq k := by
      dsimp [smoothVersionFrequencyNormSq]
      positivity
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hS p), abs_abs]
    exact (mul_le_mul_of_nonneg_left (Complex.abs_re_le_norm _) (pow_nonneg hS p)).trans_eq
      (by rw [hnorm k])
  have himag : Summable (fun k : WindowFrequency =>
      smoothVersionFrequencyNormSq k ^ p *
        |-(smoothVersionWindowCoefficientFormula Phi a b k z).im|) := by
    apply hweighted.of_norm_bounded
    intro k
    have hS : 0 ≤ smoothVersionFrequencyNormSq k := by
      dsimp [smoothVersionFrequencyNormSq]
      positivity
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (pow_nonneg hS p), abs_neg, abs_abs]
    exact (mul_le_mul_of_nonneg_left (Complex.abs_im_le_norm _) (pow_nonneg hS p)).trans_eq
      (by rw [hnorm k])
  refine Summable.sum (fun i : Sum WindowFrequency WindowFrequency =>
      smoothVersionFrequencyNormSq (match i with
        | Sum.inl k => k
        | Sum.inr k => k) ^ p *
        |smoothVersionWindowSeriesTerm Phi a b i z|) ?_ ?_
  · exact hreal.congr (fun k => by rfl)
  · exact himag.congr (fun k => by simp [smoothVersionWindowSeriesTerm])

theorem regularisedNoise_exists_unique {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (W : (SpaceTime → ℝ) → Ω → ℝ) (hW : IsWhiteNoise P W)
    (rho : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier rho) {eps : ℝ}
    (hε : eps ∈ Ioc (0 : ℝ) 1) :
    (∃ xi, IsRegularisedNoise P W rho eps xi) ∧
      (∀ xi xi', IsRegularisedNoise P W rho eps xi →
        IsRegularisedNoise P W rho eps xi' → ∀ᵐ ω ∂P, xi ω = xi' ω) ∧
      ∀ xi, IsRegularisedNoise P W rho eps xi →
        Measurable fun p : Ω × SpaceTime => xi p.1 p.2 := by
  have hPhi : IsSmoothOnSpaceTime (periodise rho eps) :=
    isSmoothOnSpaceTime_periodise rho hρ hε.1
  obtain ⟨R₀, hR₀⟩ := timeSupport_periodise rho hρ hε.1
  let R : ℝ := max R₀ 0
  have hRnonneg : 0 ≤ R := by
    exact le_max_right _ _
  have hR : ∀ z : SpaceTime, R < |z.1| → periodise rho eps z = 0 := by
    intro z hz
    exact hR₀ z (lt_of_le_of_lt (le_max_left _ _) hz)
  let N : ℕ → ℝ := fun n => (n : ℝ) + 1
  let a : ℕ → ℝ := fun n => -N n - R - 1
  let b : ℕ → ℝ := fun n => N n + R + 1
  let U : ℕ → Set SpaceTime := fun n => {z | |z.1| < (n : ℝ)}
  let e : ℕ → Sum WindowFrequency WindowFrequency → SpaceTime → ℝ :=
    fun n i => smoothVersionWindowPhysicalMode (a n) (b n) i
  let f : ℕ → Sum WindowFrequency WindowFrequency → SpaceTime → ℝ :=
    fun n i z => smoothVersionWindowSeriesTerm (periodise rho eps) (a n) (b n) i z
  let X : ℕ → Sum WindowFrequency WindowFrequency → Ω → ℝ :=
    fun n i w => W (e n i) w
  let Y : SpaceTime → Ω → ℝ :=
    fun z w => W (fun q => periodise rho eps (z - q)) w
  let B : Sum WindowFrequency WindowFrequency → ℝ := fun i =>
    smoothVersionFrequencyNormSq (match i with
      | Sum.inl k => k
      | Sum.inr k => k) ^ 3
  have hab : ∀ n, a n < b n := by
    intro n
    dsimp [a, b, N]
    nlinarith [hRnonneg]
  have hN : ∀ n, 0 < N n := by
    intro n
    dsimp [N]
    positivity
  have he : ∀ n i, MemLp (e n i) 2 (volume : Measure SpaceTime) := by
    intro n i
    cases i with
    | inl k => exact memLp_windowFourierRealTestMode (hab n) k
    | inr k => exact memLp_windowFourierImagTestMode (hab n) k
  have hXmeas : ∀ n i, Measurable (X n i) := by
    intro n i
    exact hW.1 (e n i) (he n i)
  have hBpos : ∀ i, 0 < B i := by
    intro i
    cases i <;> dsimp [B, smoothVersionFrequencyNormSq]
    all_goals positivity
  have hbase : Summable (fun k : WindowFrequency =>
      (smoothVersionFrequencyNormSq k ^ 6)⁻¹) := by
    simpa [smoothVersionFrequencyNormSq] using
      (summable_smoothVersion_inv_one_add_normSq_pow (d := 4) (r := 6) (by norm_num))
  have hBsum : Summable (fun i : Sum WindowFrequency WindowFrequency =>
      (B i)⁻¹ ^ 2) := by
    refine Summable.sum (fun i : Sum WindowFrequency WindowFrequency => (B i)⁻¹ ^ 2) ?_ ?_
    · apply hbase.congr
      intro k
      dsimp [B]
      rw [inv_pow, ← pow_mul]
    · apply hbase.congr
      intro k
      dsimp [B]
      rw [inv_pow, ← pow_mul]
  let V : ℕ → ℝ := fun n => ENNReal.toReal
    ((volume : Measure SpaceTime) (windowInterval (a n) (b n)))
  have hVnonneg : ∀ n, 0 ≤ V n := by
    intro n
    dsimp [V]
    exact ENNReal.toReal_nonneg
  have hvariance : ∀ n i, ∫ z, e n i z * e n i z ≤ V n := by
    intro n i
    simpa [e, V] using (smoothVersion_windowPhysicalMode_integral_sq_le (hab n) i)
  have hBsumV : ∀ n, (∑' i, ENNReal.ofReal ((B i)⁻¹ ^ 2 * V n)) ≠ (⊤ : ENNReal) := by
    intro n
    have hs : Summable (fun i : Sum WindowFrequency WindowFrequency =>
        (B i)⁻¹ ^ 2 * V n) := by
      simpa [mul_comm] using hBsum.mul_left (V n)
    exact hs.tsum_ofReal_ne_top
  let Gₙ : ℕ → Set Ω := fun n => ⋃ m : ℕ, ⋂ i,
    {w | |X n i w| ≤ (m : ℝ) * B i}
  have hGₙ_meas : ∀ n, MeasurableSet (Gₙ n) := by
    intro n
    apply MeasurableSet.iUnion
    intro m
    apply MeasurableSet.iInter
    intro i
    simpa [B, Real.norm_eq_abs] using
      measurableSet_le (hXmeas n i).norm (measurable_const.mul measurable_const)
  have hGₙ_ae : ∀ n, ∀ᵐ w ∂P, w ∈ Gₙ n := by
    intro n
    have hgrowth₀ := whiteNoise_ae_eventually_bound_of_integral_sq_le hW
      (he n) (hvariance n) B hBpos (hBsumV n)
    have hgrowth := ae_exists_mul_bound_of_ae_eventually_le hBpos hgrowth₀
    filter_upwards [hgrowth] with w hw
    rcases hw with ⟨C, hC, hbound⟩
    obtain ⟨m, hm⟩ := exists_nat_ge C
    refine Set.mem_iUnion.mpr ⟨m, ?_⟩
    refine Set.mem_iInter.mpr fun i => ?_
    exact (hbound i).trans (mul_le_mul_of_nonneg_right hm (le_of_lt (hBpos i)))
  let G : Set Ω := ⋂ n, Gₙ n
  have hG : MeasurableSet G := by
    apply MeasurableSet.iInter
    intro n
    exact hGₙ_meas n
  have hGae : ∀ᵐ w ∂P, w ∈ G := by
    have hAll : ∀ᵐ w ∂P, ∀ n, w ∈ Gₙ n := ae_all_iff.2 fun n => hGₙ_ae n
    simpa [G] using hAll
  have hU_open : ∀ n, IsOpen (U n) := by
    intro n
    dsimp [U]
    exact isOpen_lt (by fun_prop) (by fun_prop)
  have hU_cover : ⋃ n, U n = Set.univ := by
    apply Set.eq_univ_of_forall
    intro z
    obtain ⟨n, hn⟩ := exists_nat_gt |z.1|
    exact Set.mem_iUnion.mpr ⟨n, hn⟩
  have hX : ∀ n i, Measurable (X n i) := hXmeas
  have hSmooth : ∀ n w, w ∈ G → IsSmoothOnSpaceTime
      (fun z => ∑' i, X n i w * f n i z) := by
    intro n w hw
    have hwn : w ∈ Gₙ n := Set.mem_iInter.mp hw n
    rcases Set.mem_iUnion.mp hwn with ⟨m, hm⟩
    have hbound : ∀ i, |X n i w| ≤ (m : ℝ) *
        smoothVersionFrequencyNormSq (match i with
          | Sum.inl k => k
          | Sum.inr k => k) ^ 3 := by
      intro i
      simpa [B] using (Set.mem_iInter.mp hm i)
    have hsm := isSmoothOnSpaceTime_tsum_smoothVersionWindowSeries_of_polynomial_growth
      (Phi := periodise rho eps) hPhi hR hRnonneg (hN n)
      (a := a n) (b := b n) (by simp [a]) (by simp [b])
      (by dsimp [a, b]; nlinarith [hN n, hRnonneg]) (X := fun i => X n i w)
      (p := 3) (C₀ := (m : ℝ)) (by exact_mod_cast (Nat.zero_le m)) hbound
    simpa [X, f, e] using hsm
  have hEq : ∀ n z, z ∈ U n →
      (fun w => ∑' i, X n i w * f n i z) =ᵐ[P] Y z := by
    intro n z hzn
    have hz : |z.1| < N n := by
      dsimp [U, N] at hzn ⊢
      exact lt_trans hzn (by norm_num)
    obtain ⟨s, hscover, hsmono, hK, hLp⟩ :=
      smoothVersion_windowPhysicalKernel_tendsto_Lp (Phi := periodise rho eps)
        (R := R) (N := N n) (z := z) (a := a n) (b := b n)
        hPhi hR hRnonneg hz rfl rfl
    have hh : MemLp (fun q => periodise rho eps (z - q)) 2
        (volume : Measure SpaceTime) :=
      memLp_translate_of_isSmoothOnSpaceTime_of_timeSupport hPhi hR z
    have hnoise : MemLp (fun w => Y z w) 2 P := by
      exact (hW.2 1 (fun _ => fun q => periodise rho eps (z - q))
        (fun _ => hh)).memLp_two_apply 0
    have hpartial : ∀ r, MemLp (fun w => ∑ i ∈ s r,
        f n i z * W (e n i) w) 2 P := by
      intro r
      apply memLp_finsetSum
      intro i hi
      exact ((hW.2 1 (fun _ => e n i) (fun _ => he n i)).memLp_two_apply 0).const_mul _
    have hK₀ : ∀ r, MemLp (∑ i ∈ s r,
        smoothVersionWindowSeriesTerm (periodise rho eps) (a n) (b n) i z •
          smoothVersionWindowPhysicalMode (a n) (b n) i) 2
        (volume : Measure SpaceTime) := by
      intro r
      refine (memLp_congr_ae (μ := (volume : Measure SpaceTime)) ?_).2 (hK r)
      filter_upwards [] with w
      simp [Pi.smul_apply, smul_eq_mul]
    have hK' : ∀ r, MemLp (∑ i ∈ s r, f n i z • e n i) 2
        (volume : Measure SpaceTime) := by
      intro r
      refine (memLp_congr_ae (μ := (volume : Measure SpaceTime)) ?_).2 (hK₀ r)
      filter_upwards [] with w
      simp [f, e, Pi.smul_apply, smul_eq_mul]
    have hto₀ : ∀ r,
        (hK₀ r).toLp (∑ i ∈ s r,
          smoothVersionWindowSeriesTerm (periodise rho eps) (a n) (b n) i z •
            smoothVersionWindowPhysicalMode (a n) (b n) i) =
          (hK r).toLp (fun w => ∑ i ∈ s r,
            smoothVersionWindowSeriesTerm (periodise rho eps) (a n) (b n) i z •
              smoothVersionWindowPhysicalMode (a n) (b n) i w) := by
      intro r
      apply MemLp.toLp_congr
      filter_upwards [] with w
      simp [Pi.smul_apply, smul_eq_mul]
    have hLp₀ : Filter.Tendsto
        (fun r => (hK₀ r).toLp (∑ i ∈ s r,
          smoothVersionWindowSeriesTerm (periodise rho eps) (a n) (b n) i z •
            smoothVersionWindowPhysicalMode (a n) (b n) i)) Filter.atTop
        (𝓝 ((hh).toLp (fun q => periodise rho eps (z - q)))) := by
      apply hLp.congr'
      filter_upwards [] with r
      exact (hto₀ r).symm
    have hto : ∀ r,
        (hK' r).toLp (∑ i ∈ s r, f n i z • e n i) =
          (hK₀ r).toLp (∑ i ∈ s r,
            smoothVersionWindowSeriesTerm (periodise rho eps) (a n) (b n) i z •
              smoothVersionWindowPhysicalMode (a n) (b n) i) := by
      intro r
      apply MemLp.toLp_congr
      filter_upwards [] with w
      simp [f, e, Pi.smul_apply, smul_eq_mul]
    have hLp' : Filter.Tendsto
        (fun r => (hK' r).toLp (∑ i ∈ s r, f n i z • e n i)) Filter.atTop
        (𝓝 ((hh).toLp (fun q => periodise rho eps (z - q)))) := by
      apply hLp₀.congr'
      filter_upwards [] with r
      exact (hto r).symm
    have hrandomLp := tendsto_whiteNoise_toLp_of_tendsto_kernel_toLp
      (K := fun r => ∑ i ∈ s r, f n i z • e n i) hW hh hK' hLp'
    have hseries : ∀ᵐ w ∂P, Filter.Tendsto (fun r => ∑ i ∈ s r,
        f n i z * W (e n i) w) Filter.atTop
          (𝓝 (∑' i, f n i z * W (e n i) w)) := by
      filter_upwards [hGae] with w hw
      have hwn : w ∈ Gₙ n := Set.mem_iInter.mp hw n
      rcases Set.mem_iUnion.mp hwn with ⟨m, hm⟩
      have hbound : ∀ i, |W (e n i) w| ≤ (m : ℝ) * B i := by
        intro i
        simpa [X] using (Set.mem_iInter.mp hm i)
      have hwgt := smoothVersion_window_fourier_weighted_summable
        (Phi := periodise rho eps) (R := R) (N := N n) (a := a n) (b := b n)
        hPhi hR hRnonneg (hN n) rfl rfl 3 z
      have hwgt' : Summable (fun i : Sum WindowFrequency WindowFrequency =>
          (m : ℝ) *
            (smoothVersionFrequencyNormSq (match i with
              | Sum.inl k => k
              | Sum.inr k => k) ^ 3 *
              abs (smoothVersionWindowSeriesTerm (periodise rho eps) (a n) (b n) i z))) := by
        exact hwgt.mul_left (m : ℝ)
      have hsum : Summable (fun i => f n i z * W (e n i) w) := by
        apply hwgt'.of_norm_bounded
        intro i
        calc
          ‖f n i z * W (e n i) w‖ =
              |W (e n i) w| * |f n i z| := by
                rw [Real.norm_eq_abs, abs_mul, mul_comm]
          _ ≤ ((m : ℝ) * B i) * |f n i z| := by
                exact mul_le_mul_of_nonneg_right (hbound i) (abs_nonneg _)
          _ = (m : ℝ) *
              (smoothVersionFrequencyNormSq (match i with
                | Sum.inl k => k
                | Sum.inr k => k) ^ 3 * |f n i z|) := by
                simp [B, f]
                ring
      exact (hsum.hasSum.comp
        (Filter.tendsto_atTop_finset_of_monotone hsmono hscover))
    have hnoise' : MemLp (fun w => W (fun q => periodise rho eps (z - q)) w) 2 P := by
      simpa [Y] using hnoise
    have hEq' := whiteNoise_ae_eq_tsum_of_tendsto_Lp hW s (fun i => f n i z)
      (fun i => e n i) hnoise' (he n) hK' hpartial hrandomLp hseries
    filter_upwards [hEq'] with w hw
    simpa [X, Y, mul_comm] using hw
  obtain ⟨xi, hxi_smooth, hxi_eq⟩ :=
    exists_smoothVersion_of_windowed_series_certificate_patched
      hU_open hU_cover hG hGae hX hSmooth hEq
  have hversion : ∃ xi : Ω → SpaceTime → ℝ,
      (∀ w, IsSmoothOnSpaceTime (xi w)) ∧
        ∀ z, Measurable (fun w => xi w z) ∧
          (fun w => xi w z) =ᵐ[P] W (fun w => periodise rho eps (z - w)) :=
    ⟨xi, hxi_smooth, by
      intro z
      simpa [Y] using hxi_eq z⟩
  exact regularisedNoise_exists_unique_of_smoothVersion P W hW rho eps hPhi
    ⟨R, hR⟩ hversion

end RegularityStructures.Phi43

end
