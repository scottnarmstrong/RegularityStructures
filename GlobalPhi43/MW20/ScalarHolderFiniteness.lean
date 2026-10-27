module

public import GlobalPhi43.MW20.ScalarHolderSeminorm
public import GlobalPhi43.MW20.DyadicKernelSupport
public import GlobalPhi43.Local.SmoothingComparison
public import Mathlib.Analysis.Calculus.ContDiff.RCLike

/-! Finiteness of the actual local scalar source norm for smooth fields.
Ambient Lipschitz constants enter only this finiteness proof; exponent-sensitive
reconstruction estimates continue to use the exact parabolic metric. -/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Local Set
open scoped ENNReal ContDiff

/-- Smooth fields have finite actual parabolic Holder seminorm on every
bounded base domain for regularity between zero and one. -/
theorem scalarHolderSeminorm_finite_bound (f : ParabolicSpace → ℝ) (hf : ContDiff ℝ ∞ f)
    (D : Set ParabolicSpace) (R : ℝ) (hD : D ⊆ Metric.closedBall 0 R)
    {α : ℝ} (hα : 0 ≤ α) (hα₁ : α ≤ 1) :
    ∃ N : ℝ, 0 ≤ N ∧ scalarHolderSeminorm f D α ≤ ENNReal.ofReal N := by
  obtain ⟨K, hK⟩ := hf.contDiffOn.exists_lipschitzOnWith (by simp)
    (convex_closedBall (0 : ParabolicSpace) R) (isCompact_closedBall (0 : ParabolicSpace) R)
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : ParabolicSpace) R).exists_bound_of_continuousOn hf.continuous.continuousOn
  let N : ℝ := max (K : ℝ) (2 * max M 0)
  have hN : 0 ≤ N := K.coe_nonneg.trans (le_max_left _ _)
  refine ⟨N, hN, ?_⟩
  unfold scalarHolderSeminorm
  refine iSup_le fun x => iSup_le fun hx => iSup_le fun y => iSup_le fun hy => iSup_le fun hne => ?_
  apply (ENNReal.ofReal_le_ofReal_iff hN).2
  apply (div_le_iff₀ (Real.rpow_pos_of_pos (pdist_pos_of_ne hne) _)).2
  have hd : 0 < pdist x y := pdist_pos_of_ne hne
  by_cases hsmall : pdist x y ≤ 1
  · have hsum : x + (y - x) = y := by abel
    have hp : pdist 0 (y - x) ≤ pdist x y := by rw [← pdist_add_right x (y - x), hsum]
    have hn : ‖y - x‖ ≤ pdist x y :=
      (norm_le_of_pdist_zero_le hd.le hp).trans (max_le (by nlinarith) le_rfl)
    have hdiff : |f y - f x| ≤ (K : ℝ) * ‖y - x‖ := by
      simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs] using hK.dist_le_mul y (hD hy) x (hD hx)
    have hpow : pdist x y ≤ pdist x y ^ α := by
      simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_ge hd hsmall hα₁
    exact hdiff.trans ((mul_le_mul_of_nonneg_left hn K.coe_nonneg).trans
      (mul_le_mul (le_max_left _ _) hpow hd.le hN))
  · have hyM : |f y| ≤ max M 0 := by
      simpa only [Real.norm_eq_abs] using (hM y (hD hy)).trans (le_max_left _ _)
    have hxM : |f x| ≤ max M 0 := by
      simpa only [Real.norm_eq_abs] using (hM x (hD hx)).trans (le_max_left _ _)
    have hdiff : |f y - f x| ≤ N :=
      ((abs_sub _ _).trans (add_le_add hyM hxM)).trans (by dsimp [N]; linarith [le_max_right (K : ℝ) (2 * max M 0)])
    exact hdiff.trans (le_mul_of_one_le_right hN (Real.one_le_rpow (le_of_not_ge hsmall) hα))

/-- No separate finite-norm premise is needed for smooth local scalar data. -/
theorem scalarHolderSeminorm_ne_top (f : ParabolicSpace → ℝ) (hf : ContDiff ℝ ∞ f)
    (D : Set ParabolicSpace) (R : ℝ) (hD : D ⊆ Metric.closedBall 0 R)
    {α : ℝ} (hα : 0 ≤ α) (hα₁ : α ≤ 1) : scalarHolderSeminorm f D α ≠ ⊤ := by
  obtain ⟨N, _, hN⟩ := scalarHolderSeminorm_finite_bound f hf D R hD hα hα₁
  exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hN

end GlobalPhi43.MW20
