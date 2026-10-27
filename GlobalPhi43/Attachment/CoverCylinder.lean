module

public import GlobalPhi43.Flow.WindowGeometry
public import GlobalPhi43.MW20.Setting.MWCylinder
public import GlobalPhi43.MW20.Setting.ParabolicClosedNbhd
public import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Tactic

/-! Cylinder geometry for the local-to-global cover estimate. -/

public noncomputable section

open Set RegularityStructures GlobalPhi43.Local
open scoped ContDiff

namespace GlobalPhi43.Attachment

@[expose] def coverScale (t : ℝ) : ℝ := Real.sqrt t / 2

@[expose] def coverMap (s t : ℝ) (x₀ : Fin 3 → ℝ) (z : ParabolicSpace) : ParabolicSpace :=
  (s + t - coverScale t ^ 2, x₀) + parabolicDilate (coverScale t) z

theorem coverScale_pos {t : ℝ} (ht : 0 < t) : 0 < coverScale t :=
  div_pos (Real.sqrt_pos.mpr ht) (by norm_num)

theorem coverScale_sq {t : ℝ} (ht : 0 ≤ t) : coverScale t ^ 2 = t / 4 := by
  unfold coverScale
  rw [div_pow, Real.sq_sqrt ht]
  norm_num

theorem coverScale_le_half {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) : coverScale t ≤ 1 / 2 := by
  unfold coverScale
  exact div_le_div_of_nonneg_right (Real.sqrt_le_one.mpr ht.2) (by norm_num)

theorem coverMap_contDiff (s t : ℝ) (x₀ : Fin 3 → ℝ) : ContDiff ℝ ∞ (coverMap s t x₀) := by
  unfold coverMap parabolicDilate
  fun_prop

/-- Exact normalized closed enlargement bounds, retaining the P-plus carrier. -/
theorem normalized_enlargement_bounds {z : ParabolicSpace}
    (hz : z ∈ parabolicClosedNbhd mwCylinder 1) :
    z.1 ∈ Icc (-1 : ℝ) 2 ∧ ∀ i : Fin 3, z.2 i ∈ Icc (-2 : ℝ) 2 := by
  obtain ⟨w, hw, hdist⟩ := hz
  have hroot : Real.sqrt |w.1 - z.1| ≤ 1 := (le_max_left _ _).trans hdist
  have habs : |w.1 - z.1| ≤ 1 := Real.sqrt_le_one.mp hroot
  have hspace : ‖w.2 - z.2‖ ≤ 1 := (le_max_right _ _).trans hdist
  refine ⟨⟨by linarith [(abs_le.mp habs).2, hw.1.1],
    by linarith [(abs_le.mp habs).1, hw.1.2]⟩, ?_⟩
  intro i
  have hwi : |w.2 i| < 1 := by
    simpa only [Real.norm_eq_abs] using (norm_le_pi_norm w.2 i).trans_lt hw.2
  have hdi : |w.2 i - z.2 i| ≤ 1 := by
    simpa only [Pi.sub_apply, Real.norm_eq_abs] using (norm_le_pi_norm (w.2 - z.2) i).trans hspace
  exact ⟨by linarith [(abs_lt.mp hwi).1, (abs_le.mp hdi).2],
    by linarith [(abs_lt.mp hwi).2, (abs_le.mp hdi).1]⟩

/-- The exact source time interval for the rescaled enlargement. -/
theorem coverMap_enlargement_time {t : ℝ} (ht : 0 < t) (s : ℝ) (x₀ : Fin 3 → ℝ)
    {z : ParabolicSpace} (hz : z ∈ parabolicClosedNbhd mwCylinder 1) :
    (coverMap s t x₀ z).1 ∈ Icc (s + t / 2) (s + 5 * t / 4) := by
  have hb := (normalized_enlargement_bounds hz).1
  have hl := mul_le_mul_of_nonneg_left hb.1 (sq_nonneg (coverScale t))
  have hu := mul_le_mul_of_nonneg_left hb.2 (sq_nonneg (coverScale t))
  change s + t - coverScale t ^ 2 + coverScale t ^ 2 * z.1 ∈ _
  rw [coverScale_sq ht.le] at hl hu ⊢
  constructor
  · linarith only [hl]
  · linarith only [hu]

/-- The open cylinder has exactly the source time margins. -/
theorem coverMap_cylinder_time {t : ℝ} (ht : 0 < t) (s : ℝ) (x₀ : Fin 3 → ℝ)
    {z : ParabolicSpace} (hz : z ∈ mwCylinder) :
    (coverMap s t x₀ z).1 ∈ Ioo (s + 3 * t / 4) (s + t) := by
  have hsq : 0 < coverScale t ^ 2 := sq_pos_of_pos (coverScale_pos ht)
  have hl := mul_pos hsq hz.1.1
  have hu := mul_lt_mul_of_pos_left hz.1.2 hsq
  change s + t - coverScale t ^ 2 + coverScale t ^ 2 * z.1 ∈ _
  rw [coverScale_sq ht.le] at hl hu ⊢
  constructor
  · linarith only [hl]
  · linarith only [hu]

/-- The actual rescaled P-plus lies in the same coverRegion used by the majorant. -/
theorem coverMap_enlargement_subset {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) 1) (s : ℝ)
    {x₀ : Fin 3 → ℝ} (hx₀ : ∀ i, x₀ i ∈ Ico (0 : ℝ) 1) :
    MapsTo (coverMap s t x₀) (parabolicClosedNbhd mwCylinder 1) (Flow.coverRegion s) := by
  intro z hz
  have htime := coverMap_enlargement_time ht.1 s x₀ hz
  have hlam := coverScale_pos ht.1
  have hlam1 := coverScale_le_half ht
  refine ⟨⟨by linarith [htime.1, ht.1], by linarith [htime.2, ht.2]⟩, ?_⟩
  intro i _
  have hb := (normalized_enlargement_bounds hz).2 i
  have hl := mul_le_mul_of_nonneg_left hb.1 hlam.le
  have hu := mul_le_mul_of_nonneg_left hb.2 hlam.le
  change -2 ≤ x₀ i + coverScale t * z.2 i ∧ x₀ i + coverScale t * z.2 i ≤ 3
  constructor
  · linarith only [hl, (hx₀ i).1, hlam1]
  · linarith only [hu, (hx₀ i).2, hlam1]

end GlobalPhi43.Attachment
