module

public import GlobalPhi43.MW20.NegativeSeminorms
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# The recentered coordinate-tree norm (MW20 (2.16))

The norm is the supremum norm of the actual vector integral, as in MW20's
spatial convention. Extracting a component retains its integrability premise;
that premise is supplied by smooth fields and the actual compact kernel.
-/

public section

namespace GlobalPhi43.MW20

open MeasureTheory RegularityStructures Set
open scoped ENNReal

/-- The actual recentered XV vector test at a base point. -/
@[expose] noncomputable def coordinateTreeTest (κ : ℝ → Measure ParabolicSpace)
    (V : ParabolicSpace → ℝ) (t : ℝ) (x : ParabolicSpace) : Fin 3 → ℝ :=
  ∫ z, V (x + z) • z.2 ∂κ t

/-- Literal (2.16), with the open upper scale endpoint and spatial sup norm. -/
@[expose] noncomputable def recenteredXVSeminorm (κ : ℝ → Measure ParabolicSpace)
    (D : Set ParabolicSpace) (ε : ℝ) (V : ParabolicSpace → ℝ) : ℝ≥0∞ :=
  ⨆ x ∈ D, ⨆ t ∈ Ioo (0 : ℝ) 1,
    ENNReal.ofReal (t ^ (2 * ε) * ‖coordinateTreeTest κ V t x‖)

/-- Extraction of the actual vector test from (2.16). -/
theorem recenteredXVSeminorm_test_bound (κ : ℝ → Measure ParabolicSpace)
    (D : Set ParabolicSpace) (ε : ℝ) (V : ParabolicSpace → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hnorm : recenteredXVSeminorm κ D ε V ≤ ENNReal.ofReal C)
    {x : ParabolicSpace} (hx : x ∈ D) {t : ℝ} (ht : 0 < t) (ht₁ : t < 1) :
    ‖coordinateTreeTest κ V t x‖ ≤ C * t ^ (-2 * ε) := by
  have hb : t ^ (2 * ε) * ‖coordinateTreeTest κ V t x‖ ≤ C := by
    apply (ENNReal.ofReal_le_ofReal_iff hC).mp
    have hh : ∀ x ∈ D, ∀ t ∈ Ioo (0 : ℝ) 1,
        ENNReal.ofReal (t ^ (2 * ε) * ‖coordinateTreeTest κ V t x‖) ≤ ENNReal.ofReal C := by
      simpa only [recenteredXVSeminorm, iSup_le_iff] using hnorm
    exact hh x hx t ⟨ht, ht₁⟩
  calc
    ‖coordinateTreeTest κ V t x‖ = t ^ (-2 * ε) * (t ^ (2 * ε) * ‖coordinateTreeTest κ V t x‖) := by
      rw [← mul_assoc, ← Real.rpow_add ht]
      have he : -2 * ε + 2 * ε = 0 := by ring
      rw [he, Real.rpow_zero, one_mul]
    _ ≤ t ^ (-2 * ε) * C := mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg ht.le _)
    _ = C * t ^ (-2 * ε) := mul_comm _ _

/-- Component tests used in Lemma 2.10 follow from the source vector norm. -/
theorem recenteredXVSeminorm_component_test_bound (κ : ℝ → Measure ParabolicSpace)
    (D : Set ParabolicSpace) (ε : ℝ) (V : ParabolicSpace → ℝ)
    {C : ℝ} (hC : 0 ≤ C) (hnorm : recenteredXVSeminorm κ D ε V ≤ ENNReal.ofReal C)
    {x : ParabolicSpace} (hx : x ∈ D) {t : ℝ} (ht : 0 < t) (ht₁ : t < 1)
    (hi : Integrable (fun z => V (x + z) • z.2) (κ t)) (i : Fin 3) :
    |pastSmooth (κ t) (fun y => (y.2 i - x.2 i) * V y) x| ≤ C * t ^ (-2 * ε) := by
  have he : pastSmooth (κ t) (fun y => (y.2 i - x.2 i) * V y) x =
      coordinateTreeTest κ V t x i := by
    unfold pastSmooth coordinateTreeTest
    change (∫ z, ((x + z).2 i - x.2 i) * V (x + z) ∂κ t) =
      (ContinuousLinearMap.proj i : (Fin 3 → ℝ) →L[ℝ] ℝ) (∫ z, V (x + z) • z.2 ∂κ t)
    rw [← (ContinuousLinearMap.proj i : (Fin 3 → ℝ) →L[ℝ] ℝ).integral_comp_comm hi]
    apply integral_congr_ae
    filter_upwards with z
    simp only [ContinuousLinearMap.proj_apply, Pi.smul_apply, smul_eq_mul,
      Prod.snd_add, Pi.add_apply, add_sub_cancel_left]
    ring
  rw [he, ← Real.norm_eq_abs]
  exact (norm_le_pi_norm _ i).trans (recenteredXVSeminorm_test_bound κ D ε V hC hnorm hx ht ht₁)

end GlobalPhi43.MW20
