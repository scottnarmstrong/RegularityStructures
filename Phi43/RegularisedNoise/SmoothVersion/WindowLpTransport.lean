/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.RegularisedNoise.SmoothVersion.WindowCoefficientFormula
public import Phi43.RegularisedNoise.SmoothVersion.WindowSeriesSmooth
public import Phi43.RegularisedNoise.SmoothVersion.WindowedPatching
import Mathlib.MeasureTheory.Function.UniformIntegrable
import Mathlib.MeasureTheory.Function.UnifTight
public import Mathlib.Data.Set.FiniteExhaustion
public import Phi43.RegularisedNoise.SmoothVersion.RealTorusSplit

/-!
# Physical `L²` convergence of finite-window Fourier sums

The normalized Fourier series lives on the unit four-torus, whereas white noise is indexed by
functions on `ℝ × T³`.  This module records the elementary transport needed to compare the two:
on the time window, `windowPoint` changes normalized Haar measure into physical measure, and the
Fourier sums vanish outside the window.
-/

@[expose] public noncomputable section

open MeasureTheory Set
open Filter
open scoped BigOperators Topology ComplexConjugate

namespace RegularityStructures.Phi43

private theorem smoothVersion_windowPoint_surjective {a b : ℝ} (hab : a < b)
    {w : SpaceTime} (hw : w ∈ windowInterval a b) :
    ∃ y : UnitAddTorus (Fin 4), windowPoint a b y = w := by
  let t : ℝ := (b - a)⁻¹ * (w.1 - a)
  have ht : t ∈ Ioc (0 : ℝ) 1 := by
    dsimp [t]
    constructor
    · have hba : 0 < b - a := sub_pos.mpr hab
      exact mul_pos (inv_pos.mpr hba) (sub_pos.mpr hw.1.1)
    · have hba : 0 < b - a := sub_pos.mpr hab
      have hdiff : w.1 - a ≤ b - a := by linarith [hw.1.2]
      have hdiff' : w.1 - a ≤ 1 * (b - a) := by simpa using hdiff
      simpa [div_eq_mul_inv, mul_comm] using (div_le_iff₀ hba).2 hdiff'
  let y : UnitAddTorus (Fin 4) := coordinateInsert 0 (t : UnitAddCircle) w.2
  refine ⟨y, ?_⟩
  apply Prod.ext
  · unfold y windowPoint
    simp [coordinateInsert]
    rw [AddCircle.equivIoc_coe_of_mem (by simpa using ht)]
    dsimp [t]
    field_simp [ne_of_gt (sub_pos.mpr hab)]
    ring
  · unfold y windowPoint
    funext i
    simp [coordinateInsert]

private theorem smoothVersion_windowKernel_zero_outside
    {Phi : SpaceTime → ℝ} {R N : ℝ}
    (hR : ∀ q : SpaceTime, R < |q.1| → Phi q = 0)
    (hR0 : 0 ≤ R) {z : SpaceTime} (hz : |z.1| < N)
    {a b : ℝ} (ha : a = -N - R - 1) (hb : b = N + R + 1)
    {w : SpaceTime} (hw : w ∉ windowInterval a b) :
    Phi (z - w) = 0 := by
  have htime : w.1 ≤ a ∨ b < w.1 := by
    by_cases hle : w.1 ≤ a
    · exact Or.inl hle
    · right
      exact lt_of_not_ge fun hwb => hw ⟨⟨lt_of_not_ge hle, hwb⟩, mem_univ _⟩
  rcases htime with hleft | hright
  · apply hR
    have hzlow : -N < z.1 := (abs_lt.mp hz).1
    have hpos : 0 < z.1 - w.1 := by
      rw [ha] at hleft
      linarith
    rw [show (z - w).1 = z.1 - w.1 by rfl, abs_of_pos hpos]
    rw [ha] at hleft
    linarith
  · apply hR
    have hzupper : z.1 < N := (abs_lt.mp hz).2
    have hneg : z.1 - w.1 < 0 := by
      rw [hb] at hright
      linarith
    rw [show (z - w).1 = z.1 - w.1 by rfl, abs_of_neg hneg]
    rw [hb] at hright
    linarith

def smoothVersionWindowPhysicalMode (a b : ℝ)
    (i : Sum WindowFrequency WindowFrequency) : SpaceTime → ℝ :=
  match i with
  | Sum.inl k => windowFourierRealTestMode a b k
  | Sum.inr k => windowFourierImagTestMode a b k

private theorem smoothVersion_windowCoefficient_abs_summable
    {Phi : SpaceTime → ℝ} (hPhi : IsSmoothOnSpaceTime Phi)
    {R N : ℝ} (hR : ∀ q : SpaceTime, R < |q.1| → Phi q = 0)
    (hR0 : 0 ≤ R) {z : SpaceTime} (hz : |z.1| < N) {a b : ℝ}
    (ha : a = -N - R - 1) (hb : b = N + R + 1) :
    Summable (fun i : Sum WindowFrequency WindowFrequency =>
      |smoothVersionWindowSeriesTerm Phi a b i z|) := by
  obtain ⟨C, hC0, hC⟩ := smoothVersion_windowCoefficientAmplitude_decay
    hPhi hR hR0 (lt_of_le_of_lt (abs_nonneg z.1) hz) a b ha hb 6
  have hamp : Summable (fun k : WindowFrequency =>
      ‖smoothVersionWindowCoefficientAmplitude Phi a b k‖) := by
    apply summable_smoothVersion_fourier_of_coordinate_decay
    · exact ⟨‖smoothVersionWindowCoefficientAmplitude Phi a b 0‖,
        norm_nonneg _, le_rfl⟩
    · exact ⟨C, hC0, hC⟩
  have hnorm : ∀ k : WindowFrequency,
      ‖smoothVersionWindowCoefficientFormula Phi a b k z‖ =
        ‖smoothVersionWindowCoefficientAmplitude Phi a b k‖ := by
    intro k
    have hamp : smoothVersionWindowCoefficientFormula Phi a b k z =
        smoothVersionWindowCoefficientAmplitude Phi a b k •
          conj (globalWindowFourierMode (b - a) k z) := by
      unfold smoothVersionWindowCoefficientFormula smoothVersionWindowCoefficientAmplitude
      simp [Algebra.smul_def]
      ring
    rw [hamp]
    simp only [norm_smul]
    rw [Complex.norm_conj]
    unfold globalWindowFourierMode
    simp only [norm_mul, fourier_apply, Circle.norm_coe, norm_prod]
    simp
  have hreal : Summable (fun k : WindowFrequency =>
      |(smoothVersionWindowCoefficientFormula Phi a b k z).re|) := by
    apply Summable.of_norm_bounded hamp
    intro k
    simpa only [Real.norm_eq_abs, abs_abs] using
      (Complex.abs_re_le_norm _).trans_eq (hnorm k)
  have himag : Summable (fun k : WindowFrequency =>
      |-(smoothVersionWindowCoefficientFormula Phi a b k z).im|) := by
    apply Summable.of_norm_bounded hamp
    intro k
    simpa only [Real.norm_eq_abs, abs_abs, abs_neg] using
      (Complex.abs_im_le_norm _).trans_eq (hnorm k)
  refine Summable.sum (fun i : Sum WindowFrequency WindowFrequency =>
      |smoothVersionWindowSeriesTerm Phi a b i z|) ?_ ?_
  · convert hreal using 1
    funext k
    rfl
  · convert himag using 1
    funext k
    simp [smoothVersionWindowSeriesTerm]

theorem smoothVersion_windowPhysicalKernel_tendsto_Lp
    {Phi : SpaceTime → ℝ} (hPhi : IsSmoothOnSpaceTime Phi)
    {R N : ℝ} (hR : ∀ q : SpaceTime, R < |q.1| → Phi q = 0)
    (hR0 : 0 ≤ R) {z : SpaceTime} (hz : |z.1| < N) {a b : ℝ}
    (ha : a = -N - R - 1) (hb : b = N + R + 1) :
    ∃ s : ℕ → Finset (Sum WindowFrequency WindowFrequency),
      (∀ i, ∃ n, i ∈ s n) ∧
      Monotone s ∧
      ∃ hK : ∀ n, MemLp
        (fun w => ∑ i ∈ s n,
          smoothVersionWindowSeriesTerm Phi a b i z •
            smoothVersionWindowPhysicalMode a b i w) 2
        (volume : Measure SpaceTime),
      Tendsto
        (fun n => (hK n).toLp (fun w => ∑ i ∈ s n,
          smoothVersionWindowSeriesTerm Phi a b i z •
            smoothVersionWindowPhysicalMode a b i w)) atTop
        (𝓝 ((memLp_translate_of_isSmoothOnSpaceTime_of_timeSupport
          hPhi hR z).toLp (fun w => Phi (z - w)))) := by
  classical
  have hN : 0 < N := lt_of_le_of_lt (abs_nonneg z.1) hz
  have hab : a < b := by
    rw [ha, hb]
    linarith
  let K : Set.FiniteExhaustion (Set.univ : Set (Sum WindowFrequency WindowFrequency)) :=
    Set.Countable.finiteExhaustion Set.countable_univ
  let s : ℕ → Finset (Sum WindowFrequency WindowFrequency) := fun n =>
    (K n).toFinite.toFinset
  have hsmono : Monotone s := by
    intro m n hmn
    apply Finset.coe_subset.2
    simpa [s] using K.mono hmn
  have hscover : ∀ i, ∃ n, i ∈ s n := by
    intro i
    have hi : i ∈ ⋃ n, K n := by
      rw [K.iUnion_eq]
      exact Set.mem_univ i
    rcases Set.mem_iUnion.mp hi with ⟨n, hn⟩
    exact ⟨n, by simpa [s] using hn⟩
  let e : Sum WindowFrequency WindowFrequency → SpaceTime → ℝ :=
    smoothVersionWindowPhysicalMode a b
  have he : ∀ i, MemLp (e i) 2 (volume : Measure SpaceTime) := by
    intro i
    cases i with
    | inl k => exact memLp_windowFourierRealTestMode hab k
    | inr k => exact memLp_windowFourierImagTestMode hab k
  have hK : ∀ n, MemLp
      (fun w => ∑ i ∈ s n,
        smoothVersionWindowSeriesTerm Phi a b i z • e i w) 2
      (volume : Measure SpaceTime) := by
    intro n
    convert memLp_finsetSum (s n) (fun i hi =>
      (he i).const_smul (smoothVersionWindowSeriesTerm Phi a b i z)) using 1
  obtain ⟨hends, hcont, hpoint⟩ := continuous_windowKernelLift_eq_windowPoint
    hPhi hR hz ha hb
  let f : C(UnitAddTorus (Fin 4), ℝ) :=
    ⟨windowKernelLift Phi hPhi z a b hends, hcont⟩
  have hfpoint (y : UnitAddTorus (Fin 4)) :
      f y = Phi (z - windowPoint a b y) := by
    exact hpoint y
  have hformula (k : WindowFrequency) :
      smoothVersionWindowCoefficientFormula Phi a b k z =
        UnitAddTorus.mFourierCoeff (complexifyTorusContinuousMap f) k := by
    have hfun : (complexifyTorusContinuousMap f : UnitAddTorus (Fin 4) → ℂ) =
        (fun y => (Phi (z - windowPoint a b y) : ℂ)) := by
      funext y
      simp only [complexifyTorusContinuousMap_apply]
      rw [hfpoint]
    rw [hfun]
    exact smoothVersionWindowCoefficientFormula_eq_mFourierCoeff
      hPhi hR hR0 hz ha hb k
  have hampSum : Summable (fun k : WindowFrequency =>
      ‖smoothVersionWindowCoefficientAmplitude Phi a b k‖) := by
    obtain ⟨C, hC0, hC⟩ := smoothVersion_windowCoefficientAmplitude_decay
      hPhi hR hR0 hN a b ha hb 6
    apply summable_smoothVersion_fourier_of_coordinate_decay
    · exact ⟨‖smoothVersionWindowCoefficientAmplitude Phi a b 0‖,
        norm_nonneg _, le_rfl⟩
    · exact ⟨C, hC0, hC⟩
  have hfourier : Summable (fun k : WindowFrequency =>
      ‖UnitAddTorus.mFourierCoeff (complexifyTorusContinuousMap f) k‖) := by
    apply hampSum.congr
    intro k
    rw [← hformula k]
    have hamp : smoothVersionWindowCoefficientFormula Phi a b k z =
        smoothVersionWindowCoefficientAmplitude Phi a b k •
          conj (globalWindowFourierMode (b - a) k z) := by
      unfold smoothVersionWindowCoefficientFormula smoothVersionWindowCoefficientAmplitude
      simp [Algebra.smul_def]
      ring
    rw [hamp, norm_smul, Complex.norm_conj]
    unfold globalWindowFourierMode
    simp only [norm_mul, fourier_apply, Circle.norm_coe, norm_prod]
    simp
  have hseries_point (y : UnitAddTorus (Fin 4)) :
      Tendsto (fun n => ∑ i ∈ s n,
        realTorusFourierSplitTerm f i y) atTop (𝓝 (f y)) := by
    have hs := (hasSum_realTorusFourierSplitTerm f y hfourier).comp
      (Filter.tendsto_atTop_finset_of_monotone hsmono hscover)
    change Tendsto ((fun q => ∑ i ∈ q, realTorusFourierSplitTerm f i y) ∘ s)
      atTop (𝓝 (f y))
    exact hs
  have hpointwise : ∀ w : SpaceTime, Tendsto
      (fun n => ∑ i ∈ s n,
        smoothVersionWindowSeriesTerm Phi a b i z • e i w) atTop
      (𝓝 (Phi (z - w))) := by
    intro w
    by_cases hw : w ∈ windowInterval a b
    · obtain ⟨y, rfl⟩ := smoothVersion_windowPoint_surjective hab hw
      have hmode : ∀ i, smoothVersionWindowSeriesTerm Phi a b i z •
          e i (windowPoint a b y) = realTorusFourierSplitTerm f i y := by
        intro i
        cases i with
        | inl k =>
            simp only [e, smoothVersionWindowPhysicalMode, smoothVersionWindowSeriesTerm,
              windowFourierRealTestMode, Set.indicator_of_mem
                (windowPoint_mem_windowInterval hab y), smul_eq_mul,
              windowFourierRealModeShift, windowFourierModeShift_windowPoint hab k y]
            unfold realTorusFourierSplitTerm
            rw [hformula k]
        | inr k =>
            simp only [e, smoothVersionWindowPhysicalMode, smoothVersionWindowSeriesTerm,
              windowFourierImagTestMode, Set.indicator_of_mem
                (windowPoint_mem_windowInterval hab y), smul_eq_mul,
              windowFourierImagModeShift, windowFourierModeShift_windowPoint hab k y]
            unfold realTorusFourierSplitTerm
            rw [hformula k]
            ring
      have h := hseries_point y
      simpa only [hmode, hfpoint] using h
    · have hzero := smoothVersion_windowKernel_zero_outside hR hR0 hz ha hb hw
      have hsumzero : ∀ n, (∑ i ∈ s n,
          smoothVersionWindowSeriesTerm Phi a b i z • e i w) = 0 := by
        intro n
        apply Finset.sum_eq_zero
        intro i hi
        cases i with
        | inl k =>
            simp only [e, smoothVersionWindowPhysicalMode,
              windowFourierRealTestMode, Set.indicator_of_notMem hw,
              smul_eq_mul, mul_zero]
        | inr k =>
            simp only [e, smoothVersionWindowPhysicalMode,
              windowFourierImagTestMode, Set.indicator_of_notMem hw,
              smul_eq_mul, mul_zero]
      simp_rw [hsumzero]
      simp [hzero]
  let F : ℕ → SpaceTime → ℝ := fun n w => ∑ i ∈ s n,
    smoothVersionWindowSeriesTerm Phi a b i z • e i w
  have hFzero (n : ℕ) {w : SpaceTime} (hw : w ∉ windowInterval a b) : F n w = 0 := by
    dsimp [F]
    apply Finset.sum_eq_zero
    intro i hi
    cases i with
    | inl k =>
        simp only [e, smoothVersionWindowPhysicalMode,
          windowFourierRealTestMode, Set.indicator_of_notMem hw, mul_zero]
    | inr k =>
        simp only [e, smoothVersionWindowPhysicalMode,
          windowFourierImagTestMode, Set.indicator_of_notMem hw, mul_zero]
  have hmode_meas : ∀ i, Measurable (e i) := by
    intro i
    cases i with
    | inl k =>
        exact measurable_windowFourierRealTestMode k
    | inr k =>
        exact measurable_windowFourierImagTestMode k
  have hFmeas : ∀ n, Measurable (F n) := by
    intro n
    dsimp [F]
    fun_prop
  have hmode_norm : ∀ i w, ‖e i w‖ ≤ 1 := by
    intro i w
    cases i with
    | inl k =>
        unfold e smoothVersionWindowPhysicalMode
        by_cases hw : w ∈ windowInterval a b
        · change ‖(windowInterval a b).indicator
            (windowFourierRealModeShift a b k) w‖ ≤ 1
          rw [Set.indicator_of_mem hw]
          unfold windowFourierRealModeShift
          simpa only [Real.norm_eq_abs] using
            (Complex.abs_re_le_norm (windowFourierModeShift a b k w)).trans_eq
              (norm_windowFourierModeShift k w)
        · simp [windowFourierRealTestMode, hw]
    | inr k =>
        unfold e smoothVersionWindowPhysicalMode
        by_cases hw : w ∈ windowInterval a b
        · change ‖(windowInterval a b).indicator
            (windowFourierImagModeShift a b k) w‖ ≤ 1
          rw [Set.indicator_of_mem hw]
          unfold windowFourierImagModeShift
          simpa only [Real.norm_eq_abs] using
            (Complex.abs_im_le_norm (windowFourierModeShift a b k w)).trans_eq
              (norm_windowFourierModeShift k w)
        · simp [windowFourierImagTestMode, hw]
  have hcoef := smoothVersion_windowCoefficient_abs_summable
    hPhi hR hR0 hz ha hb
  let A : ℝ := ∑' i : Sum WindowFrequency WindowFrequency,
    |smoothVersionWindowSeriesTerm Phi a b i z|
  have hA0 : 0 ≤ A := by
    dsimp [A]
    exact tsum_nonneg (fun i => abs_nonneg _)
  have hFbound (n : ℕ) (w : SpaceTime) : ‖F n w‖ ≤ A := by
    dsimp [F, A]
    calc
      ‖∑ i ∈ s n, smoothVersionWindowSeriesTerm Phi a b i z • e i w‖ ≤
          ∑ i ∈ s n, ‖smoothVersionWindowSeriesTerm Phi a b i z • e i w‖ :=
        norm_sum_le _ _
      _ = ∑ i ∈ s n, |smoothVersionWindowSeriesTerm Phi a b i z| * ‖e i w‖ := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [norm_smul]
        simp only [Real.norm_eq_abs]
      _ ≤ ∑ i ∈ s n, |smoothVersionWindowSeriesTerm Phi a b i z| := by
        apply Finset.sum_le_sum
        intro i hi
        exact mul_le_of_le_one_right (abs_nonneg _) (hmode_norm i w)
      _ ≤ ∑' i : Sum WindowFrequency WindowFrequency,
          |smoothVersionWindowSeriesTerm Phi a b i z| :=
        Summable.sum_le_tsum _ (fun _ _ => abs_nonneg _) hcoef
  have hwindow : (volume : Measure SpaceTime) (windowInterval a b) ≠ (⊤ : ENNReal) := by
    have hcompact : IsCompact (Icc a b ×ˢ (Set.univ : Set Torus3)) :=
      isCompact_Icc.prod isCompact_univ
    have hfinite : (volume : Measure SpaceTime)
        (Icc a b ×ˢ (Set.univ : Set Torus3)) < (⊤ : ENNReal) :=
      hcompact.measure_lt_top
    apply (lt_of_le_of_lt (measure_mono (μ := (volume : Measure SpaceTime)) ?_) hfinite).ne
    exact Set.prod_mono Ioc_subset_Icc_self subset_rfl
  have hui : UnifIntegrable F 2 (volume : Measure SpaceTime) := by
    apply unifIntegrable_of' (p := (2 : ENNReal)) (μ := (volume : Measure SpaceTime))
      (by norm_num) (by norm_num)
    · intro n
      exact (hFmeas n).stronglyMeasurable
    · intro ε hε
      let C : NNReal := ⟨A + 1, by linarith [hA0]⟩
      refine ⟨C, ?_, ?_⟩
      · rw [← NNReal.coe_pos]
        dsimp [C]
        exact_mod_cast (show (0 : ℝ) < A + 1 by linarith [hA0])
      · intro n
        have hzero : {w | C ≤ ‖F n w‖₊}.indicator (F n) = 0 := by
          funext w
          by_cases hset : C ≤ ‖F n w‖₊
          · have hlt : ‖F n w‖₊ < C := by
              apply NNReal.coe_lt_coe.2
              change ‖F n w‖ < A + 1
              exact (hFbound n w).trans_lt (lt_add_of_pos_right A zero_lt_one)
            exact (not_lt_of_ge hset hlt).elim
          · change (if C ≤ ‖F n w‖₊ then F n w else 0) = 0
            simp [hset]
        rw [hzero]
        simp
  have hut : UnifTight F 2 (volume : Measure SpaceTime) := by
    intro ε hε
    refine ⟨windowInterval a b, hwindow, ?_⟩
    intro n
    have hzero : (windowInterval a b)ᶜ.indicator (F n) = 0 := by
      funext w
      by_cases hw : w ∈ windowInterval a b
      · have hwc : w ∉ (windowInterval a b)ᶜ := by
          intro h
          exact h hw
        simp [Set.indicator_of_notMem hwc]
      · have hwc : w ∈ (windowInterval a b)ᶜ := hw
        simp [Set.indicator_of_mem hwc, hFzero n hw]
    rw [hzero]
    simp
  refine ⟨s, hscover, hsmono, hK, ?_⟩
  change Tendsto (fun n => (hK n).toLp (F n)) atTop
    (𝓝 ((memLp_translate_of_isSmoothOnSpaceTime_of_timeSupport hPhi hR z).toLp
      (fun w => Phi (z - w))))
  refine (Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (μ := (volume : Measure SpaceTime))
    (p := (2 : ENNReal)) F hK (fun w => Phi (z - w))
      (memLp_translate_of_isSmoothOnSpaceTime_of_timeSupport hPhi hR z)).2 ?_
  have hLp := tendsto_Lp_of_tendsto_ae (μ := (volume : Measure SpaceTime))
    (p := (2 : ENNReal)) (by norm_num) (by norm_num)
    (fun n => (hFmeas n).aestronglyMeasurable)
    (memLp_translate_of_isSmoothOnSpaceTime_of_timeSupport hPhi hR z)
    hui hut (Filter.Eventually.of_forall (fun w => by simpa [F] using hpointwise w))
  exact hLp

end RegularityStructures.Phi43

end
