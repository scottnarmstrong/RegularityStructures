module

public import Mathlib.Analysis.Calculus.BumpFunction.Normed
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

/-! The single positive smooth time average used in the Gaussian slice probe.
The cutoff and all derivative allowances are fixed before stochastic data. -/

@[expose] public noncomputable section

open MeasureTheory Set Metric
open scoped ContDiff

namespace GlobalPhi43.Attachment

/-- Its closed support lies strictly inside the source interval (1/2,3/4). -/
def probeTimeBump : ContDiffBump (5 / 8 : ℝ) where
  rIn := 1 / 32
  rOut := 1 / 16
  rIn_pos := by norm_num
  rIn_lt_rOut := by norm_num

/-- One fixed averaging cutoff, with integral exactly one. -/
def probeTimeCutoff : ℝ → ℝ := probeTimeBump.normed volume

theorem probeTimeCutoff_smooth : ContDiff ℝ ∞ probeTimeCutoff :=
  probeTimeBump.contDiff_normed

theorem probeTimeCutoff_nonneg (r : ℝ) : 0 ≤ probeTimeCutoff r :=
  probeTimeBump.nonneg_normed r

theorem probeTimeCutoff_integral : ∫ r, probeTimeCutoff r = 1 :=
  probeTimeBump.integral_normed

theorem probeTimeCutoff_compact : HasCompactSupport probeTimeCutoff :=
  probeTimeBump.hasCompactSupport_normed

theorem probeTimeCutoff_support : tsupport probeTimeCutoff ⊆ Ioo (1 / 2 : ℝ) (3 / 4) := by
  intro r hr
  have hh : |r - 5 / 8| ≤ (1 / 16 : ℝ) := by
    have h := probeTimeBump.tsupport_normed_eq (μ := volume)
    rw [show probeTimeCutoff = probeTimeBump.normed volume from rfl, h] at hr
    simpa only [Metric.mem_closedBall, Real.dist_eq, probeTimeBump] using hr
  obtain ⟨hl, hu⟩ := abs_le.mp hh
  constructor <;> linarith

/-- The source chi_t, with the literal inverse-time normalization. -/
def probeTimeWeight (t r : ℝ) : ℝ := t⁻¹ * probeTimeCutoff (r / t)

theorem probeTimeWeight_smooth (t : ℝ) : ContDiff ℝ ∞ (probeTimeWeight t) :=
  contDiff_const.mul (probeTimeCutoff_smooth.comp (contDiff_id.div_const t))

theorem probeTimeWeight_nonneg {t : ℝ} (ht : 0 < t) (r : ℝ) :
    0 ≤ probeTimeWeight t r := mul_nonneg (inv_nonneg.mpr ht.le) (probeTimeCutoff_nonneg _)

theorem probeTimeWeight_support {t : ℝ} (ht : 0 < t) :
    tsupport (probeTimeWeight t) ⊆ Icc (t / 2) (3 * t / 4) := by
  apply closure_minimal _ isClosed_Icc
  intro r hr
  have hc : probeTimeCutoff (r / t) ≠ 0 := by
    intro he
    exact hr (by simp only [probeTimeWeight, he, mul_zero])
  have hh := probeTimeCutoff_support (subset_closure hc)
  have hl := (lt_div_iff₀ ht).mp hh.1
  have hu := (div_lt_iff₀ ht).mp hh.2
  constructor <;> linarith

theorem probeTimeWeight_compact {t : ℝ} (ht : 0 < t) :
    HasCompactSupport (probeTimeWeight t) :=
  isCompact_Icc.of_isClosed_subset (isClosed_tsupport _) (probeTimeWeight_support ht)

theorem probeTimeWeight_integral {t : ℝ} (ht : 0 < t) :
    ∫ r, probeTimeWeight t r = 1 := by
  change (∫ r, t⁻¹ * probeTimeCutoff (r / t)) = 1
  rw [integral_const_mul, Measure.integral_comp_div,
    probeTimeCutoff_integral, abs_of_pos ht, smul_eq_mul, mul_one, inv_mul_cancel₀ ht.ne']

end GlobalPhi43.Attachment
