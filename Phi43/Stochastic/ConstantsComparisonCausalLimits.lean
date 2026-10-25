/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.Stochastic.ConstantsComparisonPairingLimits
public import Phi43.Stochastic.ConstantsComparisonKernelMemLp
import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp
public import RegularityStructures.Probability.AnnealedNoiseBridge

/-!
# Causal time cuts for covariance limits

A causal kernel splits into a part supported in `0 < t < a` and a part supported in `t ≥ a`.
The latter is in `L⁴` when the kernel is integrable and satisfies the order-three bound.
At nonzero time separation, sufficiently small mollifications of the two near parts have
disjoint support. The remaining correlations are conjugate-exponent pairings, as required
for the unregularised limit of Hairer's (10.41).
-/

@[expose] public noncomputable section

open MeasureTheory Filter Set
open scoped Topology

namespace RegularityStructures.Phi43

/-- The kernel with the initial time strip removed. -/
def constantsComparison_timeFar (f : SpaceTime → ℝ) (a : ℝ) : SpaceTime → ℝ :=
  {z : SpaceTime | a ≤ z.1}.indicator f

/-- The initial time-strip part of a causal kernel. -/
def constantsComparison_timeNear (f : SpaceTime → ℝ) (a : ℝ) : SpaceTime → ℝ :=
  f - constantsComparison_timeFar f a

private theorem comparisonCausal_far_measurable
    {f : SpaceTime → ℝ} (hf : Measurable f) (a : ℝ) :
    Measurable (constantsComparison_timeFar f a) :=
  hf.indicator (measurableSet_le measurable_const measurable_fst)

private theorem comparisonCausal_far_memLp_four
    {f : SpaceTime → ℝ} (hfm : Measurable f) (hfi : Integrable f)
    {a C : ℝ} (ha : 0 < a) (hC : 0 ≤ C)
    (hbound : ∀ z, 0 < torusParabolicSize z →
      |f z| ≤ C * torusParabolicSize z ^ (-(3 : ℝ))) :
    MemLp (constantsComparison_timeFar f a) (ENNReal.ofReal 4) := by
  let F := constantsComparison_timeFar f a
  let B : ℝ := C * (√a) ^ (-(3 : ℝ))
  have hB : 0 ≤ B := mul_nonneg hC (Real.rpow_nonneg (Real.sqrt_nonneg a) _)
  have hFm : Measurable F := comparisonCausal_far_measurable hfm a
  have hFi : Integrable F :=
    hfi.indicator (measurableSet_le measurable_const measurable_fst)
  have hFb : ∀ z, ‖F z‖ ≤ B := by
    intro z
    by_cases ht : a ≤ z.1
    · have ht0 : 0 < z.1 := ha.trans_le ht
      have hsize : √a ≤ torusParabolicSize z := by
        unfold torusParabolicSize
        rw [abs_of_pos ht0]
        exact (Real.sqrt_le_sqrt ht).trans
          (le_add_of_nonneg_right (torusSpatialNorm_nonneg z.2))
      have hroot : 0 < √a := Real.sqrt_pos.mpr ha
      have hsize0 := hroot.trans_le hsize
      have hh := (hbound z hsize0).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hroot hsize (by norm_num)) hC)
      simpa [F, constantsComparison_timeFar, ht, Real.norm_eq_abs, B] using hh
    · simp [F, constantsComparison_timeFar, ht, hB]
  have hpow : Integrable (fun z => ‖F z‖ ^ (ENNReal.ofReal 4).toReal) := by
    apply (hFi.norm.const_mul (B ^ 3)).mono'
      ((hFm.norm.pow_const _).aestronglyMeasurable)
    filter_upwards [] with z
    rw [show (ENNReal.ofReal (4 : ℝ)).toReal = 4 by norm_num]
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (norm_nonneg _) _),
      show (4 : ℝ) = (4 : ℕ) by norm_num, Real.rpow_natCast]
    calc
      ‖F z‖ ^ 4 = ‖F z‖ ^ 3 * ‖F z‖ := by ring
      _ ≤ B ^ 3 * ‖F z‖ := mul_le_mul_of_nonneg_right
        (pow_le_pow_left₀ (norm_nonneg _) (hFb z) 3) (norm_nonneg _)
  exact (integrable_norm_rpow_iff hFm.aestronglyMeasurable
    (by norm_num) (by norm_num)).mp hpow

private theorem comparisonCausal_near_support
    {f : SpaceTime → ℝ} (hf : ∀ z, z.1 ≤ 0 → f z = 0)
    {a : ℝ} {z : SpaceTime} (hz : constantsComparison_timeNear f a z ≠ 0) :
    0 < z.1 ∧ z.1 < a := by
  have ht : ¬ a ≤ z.1 := by
    intro ht
    exact hz (by simp [constantsComparison_timeNear, constantsComparison_timeFar, ht])
  refine ⟨?_, lt_of_not_ge ht⟩
  by_contra h
  exact hz (by simp [constantsComparison_timeNear, constantsComparison_timeFar, ht,
    hf z (le_of_not_gt h)])

private theorem comparisonCausal_mollified_near_support
    {f : SpaceTime → ℝ} (hf : ∀ z, z.1 ≤ 0 → f z = 0)
    {a : ℝ} {P : SpaceTime → ℝ}
    (hP : Function.support P ⊆ {w : SpaceTime | |w.1| < a})
    {z : SpaceTime}
    (hz : spaceTimeConvolution P (constantsComparison_timeNear f a) z ≠ 0) :
    -a < z.1 ∧ z.1 < 2 * a := by
  have hs : z ∈ Function.support
      (MeasureTheory.convolution P (constantsComparison_timeNear f a)
        (ContinuousLinearMap.lsmul ℝ ℝ) volume) := hz
  have hadd := support_convolution_subset_swap
    (L := ContinuousLinearMap.lsmul ℝ ℝ) hs
  rcases hadd with ⟨u, hu, v, hv, huv⟩
  have hu' := comparisonCausal_near_support hf hu
  have hPv := hP hv
  change |v.1| < a at hPv
  have hv' := abs_lt.mp hPv
  have heq : u.1 + v.1 = z.1 := congrArg Prod.fst huv
  constructor <;> linarith

private theorem comparisonCausal_near_product_zero
    {F : SpaceTime → ℝ} {a : ℝ}
    (hF : ∀ w, F w ≠ 0 → -a < w.1 ∧ w.1 < 2 * a)
    {z : SpaceTime} (hz : 3 * a ≤ |z.1|) :
    ∀ w, F (z + w) * F w = 0 := by
  intro w
  by_cases hw : F w = 0
  · simp [hw]
  by_cases hzw : F (z + w) = 0
  · simp [hzw]
  have hw' := hF w hw
  have hzw' := hF (z + w) hzw
  have habs : |z.1| < 3 * a := by
    rw [abs_lt]
    change -a < z.1 + w.1 ∧ z.1 + w.1 < 2 * a at hzw'
    constructor <;> linarith
  exact False.elim (not_lt_of_ge hz habs)

private theorem comparisonCausal_correlation_decomposition
    {f r : SpaceTime → ℝ}
    (hf : MemLp f (ENNReal.ofReal (4 / 3 : ℝ)))
    (hr : MemLp r (ENNReal.ofReal 4))
    (hrq : MemLp r (ENNReal.ofReal (4 / 3 : ℝ))) (z : SpaceTime)
    (hzero : ∀ w, (f (z + w) - r (z + w)) * (f w - r w) = 0) :
    (∫ w, f (z + w) * f w) =
      (∫ w, r (z + w) * f w) + (∫ w, f (z + w) * r w) -
        ∫ w, r (z + w) * r w := by
  have hpq : (4 : ℝ).HolderConjugate (4 / 3 : ℝ) := by
    apply Real.holderConjugate_iff.mpr
    constructor <;> norm_num
  have hfshift := hf.comp_measurePreserving (measurePreserving_add_left volume z)
  have hrshift := hr.comp_measurePreserving (measurePreserving_add_left volume z)
  have h1 : Integrable (fun w => r (z + w) * f w) :=
    @MemLp.integrable_mul SpaceTime _ volume ℝ _ _ _ _ _ hrshift hf hpq.ennrealOfReal
  have h2 : Integrable (fun w => f (z + w) * r w) :=
    @MemLp.integrable_mul SpaceTime _ volume ℝ _ _ _ _ _ hfshift hr hpq.symm.ennrealOfReal
  have h3 : Integrable (fun w => r (z + w) * r w) :=
    @MemLp.integrable_mul SpaceTime _ volume ℝ _ _ _ _ _ hrshift hrq hpq.ennrealOfReal
  calc
    _ = ∫ w, (r (z + w) * f w + f (z + w) * r w) - r (z + w) * r w := by
      apply integral_congr_ae
      filter_upwards [] with w
      linear_combination hzero w
    _ = _ := by
      have h12 : Integrable (fun w => r (z + w) * f w + f (z + w) * r w) :=
        h1.add h2
      rw [integral_sub h12 h3, integral_add h1 h2]

/-- Causal order-three kernels have mollifier-independent covariance limits off the time-zero
hyperplane. The limit is the covariance formed from the unregularised kernel itself. -/
theorem constantsComparison_causal_covariance_tendsto
    (ρ : ParabolicSpace → ℝ) (hρ : IsMollifier ρ)
    {f : SpaceTime → ℝ} (hfm : Measurable f) (hfi : Integrable f)
    (hfq : MemLp f (ENNReal.ofReal (4 / 3 : ℝ)))
    (hfcausal : ∀ w, w.1 ≤ 0 → f w = 0)
    (hfbound : ∃ C : ℝ, 0 ≤ C ∧ ∀ w, 0 < torusParabolicSize w →
      |f w| ≤ C * torusParabolicSize w ^ (-(3 : ℝ)))
    {z : SpaceTime} (hz : z.1 ≠ 0) :
    Tendsto (fun ε : ℝ => ∫ w,
      spaceTimeConvolution (periodise ρ ε) f (z + w) *
        spaceTimeConvolution (periodise ρ ε) f w)
      (𝓝[>] 0) (𝓝 (∫ w, f (z + w) * f w)) := by
  let a : ℝ := |z.1| / 4
  have ha : 0 < a := div_pos (abs_pos.mpr hz) (by norm_num)
  have hz3 : 3 * a ≤ |z.1| := by dsimp [a]; linarith [abs_pos.mpr hz]
  let r : SpaceTime → ℝ := constantsComparison_timeFar f a
  let n : SpaceTime → ℝ := constantsComparison_timeNear f a
  have hrm : Measurable r := comparisonCausal_far_measurable hfm a
  have hrq : MemLp r (ENNReal.ofReal (4 / 3 : ℝ)) :=
    hfq.indicator (measurableSet_le measurable_const measurable_fst)
  obtain ⟨C, hC, hfC⟩ := hfbound
  have hrp : MemLp r (ENNReal.ofReal 4) :=
    comparisonCausal_far_memLp_four hfm hfi ha hC hfC
  have hpq : (4 : ℝ).HolderConjugate (4 / 3 : ℝ) := by
    apply Real.holderConjugate_iff.mpr
    constructor <;> norm_num
  have h1 := constantsComparison_mollifiedPairing_tendsto ρ hρ hrm hfm hrp hfq z
  have h2 := constantsComparison_mollifiedPairing_tendsto_reverse ρ hρ hfm hrm hfq hrp z
  have h3 := constantsComparison_mollifiedPairing_tendsto ρ hρ hrm hrm hrp hrq z
  have hlimit := (h1.add h2).sub h3
  have hnzero : ∀ w, (f (z + w) - r (z + w)) * (f w - r w) = 0 := by
    have hn : ∀ w, n w ≠ 0 → -a < w.1 ∧ w.1 < 2 * a := by
      intro w hw
      have hh := comparisonCausal_near_support hfcausal hw
      constructor <;> linarith
    exact comparisonCausal_near_product_zero hn hz3
  rw [← comparisonCausal_correlation_decomposition hfq hrp hrq z hnzero] at hlimit
  apply hlimit.congr'
  have hU : {w : SpaceTime | |w.1| < a} ∈ 𝓝 (0 : SpaceTime) := by
    exact (isOpen_lt continuous_fst.abs continuous_const).mem_nhds
      (by simpa using ha)
  have hsupp := (tendsto_smallSets_iff.mp
    (constantsComparison_periodise_support_smallSets ρ hρ)) _ hU
  filter_upwards [self_mem_nhdsWithin, hsupp] with ε hε hP
  have hfε := constantsComparison_mollification_memLp ρ hρ hε hpq.symm hfq hfm
  have hrεp := constantsComparison_mollification_memLp ρ hρ hε hpq hrp hrm
  have hrεq := constantsComparison_mollification_memLp ρ hρ hε hpq.symm hrq hrm
  have heq : spaceTimeConvolution (periodise ρ ε) n =
      spaceTimeConvolution (periodise ρ ε) f - spaceTimeConvolution (periodise ρ ε) r := by
    have hconvf := constantsComparison_periodise_convolution_exists ρ hρ hε hpq.symm hfq
    have hconvr := constantsComparison_periodise_convolution_exists ρ hρ hε hpq.symm hrq
    funext w
    change (∫ u, periodise ρ ε u * (f (w - u) - r (w - u))) =
      (∫ u, periodise ρ ε u * f (w - u)) - ∫ u, periodise ρ ε u * r (w - u)
    simp_rw [mul_sub]
    exact integral_sub (hconvf w) (hconvr w)
  have hnε : ∀ w, spaceTimeConvolution (periodise ρ ε) n w ≠ 0 →
      -a < w.1 ∧ w.1 < 2 * a := by
    intro w hw
    exact comparisonCausal_mollified_near_support hfcausal hP hw
  have hzero := comparisonCausal_near_product_zero hnε hz3
  have hzero' : ∀ w,
      (spaceTimeConvolution (periodise ρ ε) f (z + w) -
        spaceTimeConvolution (periodise ρ ε) r (z + w)) *
      (spaceTimeConvolution (periodise ρ ε) f w -
        spaceTimeConvolution (periodise ρ ε) r w) = 0 := by
    intro w
    have hh := hzero w
    rw [heq] at hh
    exact hh
  exact (comparisonCausal_correlation_decomposition hfε hrεp hrεq z hzero').symm

end RegularityStructures.Phi43

end
