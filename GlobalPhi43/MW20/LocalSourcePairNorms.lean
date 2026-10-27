module

public import GlobalPhi43.MW20.MixedInteriorHolder
public import GlobalPhi43.MW20.LocalCylinderSup
public import GlobalPhi43.Local.Algebra

/-!
# Actual two-point supremum norms on the mixed source interiors
-/

public section

namespace GlobalPhi43.MW20

open RegularityStructures Set

/-- The exact mixed interior is a subset of its base source domain P_r. -/
theorem mixedInterior_subset_base {r d : ℝ} (hd : 0 ≤ d) :
    Local.cylinderInterior r d ⊆ sourceCylinder r := by
  intro z hz
  refine ⟨by nlinarith [hz.1, sq_nonneg d], hz.2.1, ?_⟩
  intro i
  rw [abs_lt]
  exact ⟨by linarith [(hz.2.2 i).1], by linarith [(hz.2.2 i).2]⟩

/-- The actual source norm is nonnegative even for empty insets; no upper
restriction on the inset is needed. -/
theorem sourceSup_nonneg_of_continuousOn_all {v : ParabolicSpace → ℝ}
    (hv : ContinuousOn v sourceClosedCylinder) {R : ℝ} (hR : 0 ≤ R) : 0 ≤ sourceSup v R := by
  by_cases hn : (sourceCylinder R).Nonempty
  · obtain ⟨z, hz⟩ := hn
    exact (abs_nonneg _).trans (abs_le_sourceSup_of_continuousOn hv hR hz)
  · have he : sourceCylinder R = ∅ := Set.not_nonempty_iff_eq_empty.mp hn
    simp [sourceSup, he]

/-- The pointwise analytic content of (4.13), before inserting actual local
norms. All coefficient factors are exact. -/
theorem expansion_abs_le_of_increments (v Y Z : ParabolicSpace → ℝ) (x y : ParabolicSpace)
    {M HY HZ : ℝ} (hvx : |v x| ≤ M) (hvy : |v y| ≤ M)
    (hY : |Y y - Y x| ≤ HY) (hZ : |Z y - Z x| ≤ HZ) :
    |Local.expansion v Y Z x y| ≤ 2 * M + HZ + 3 * M * HY := by
  have hM : 0 ≤ M := (abs_nonneg _).trans hvx
  have hvinc : |v y - v x| ≤ 2 * M := (abs_sub _ _).trans (by linarith)
  have hp : |3 * v x * (Y y - Y x)| ≤ 3 * M * HY := by
    rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3)]
    exact mul_le_mul (mul_le_mul_of_nonneg_left hvx (by norm_num)) hY (abs_nonneg _) (by positivity)
  have he : Local.expansion v Y Z x y = (v y - v x) + (Z y - Z x) + 3 * v x * (Y y - Y x) := by
    rw [Local.expansion_eq]; ring
  rw [he]
  have ht := (abs_add_le ((v y - v x) + (Z y - Z x)) (3 * v x * (Y y - Y x))).trans
    (add_le_add ((abs_add_le _ _).trans (add_le_add hvinc hZ)) hp)
  nlinarith

end GlobalPhi43.MW20
