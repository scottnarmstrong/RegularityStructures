/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.HairerCovarianceBounds
public import Phi43.BPHZ.TreeWickSquare
public import Phi43.Stochastic.ConstantsComparisonKernelLp
public import Phi43.Stochastic.StationaryField
public import Phi43.Structure.Renormalisation
public import Phi43.Torus.KernelBoundsK3
public import RegularityStructures.Torus.HeatKernelFacts

/-!
# The shift between `G`-constants and Hairer's `K`-constants

For the convergence of the G-models, the `G`-model with constants
`(wickConstant + c.1, sunsetConstant + c.2)` is the `K`-model shifted by
`gModelsShift N ρ c ε = (wickConstant − hairerWickConstant + c.1, sunsetConstant − hairerSunsetConstant + c.2)`.
This module proves that the shift is bounded on `(0, 1]` and that two shifts (for two mollifiers)
are asymptotically equal, given the convergence of the differences (the comparison of the
renormalisation constants, `constantsComparison`).
-/

@[expose] public section

namespace RegularityStructures.Phi43

/-- The shift of the `G`-constants relative to the `K`-constants, `c^ε`. -/
noncomputable def gModelsShift (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ)
    (c : RenormalisationConstants) (ε : ℝ) : RenormalisationConstants :=
  (wickConstant ρ ε - hairerWickConstant N ρ ε + c.1,
    sunsetConstant ρ ε - hairerSunsetConstant N ρ ε + c.2)

end RegularityStructures.Phi43

end

public section

open MeasureTheory Filter Topology

namespace RegularityStructures.Phi43

/-- The `K`-constants plus the shift are the `G`-constants plus `c`. -/
theorem hairerConstants_add_gModelsShift (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ)
    (c : RenormalisationConstants) (ε : ℝ) :
    (hairerWickConstant N ρ ε, hairerSunsetConstant N ρ ε) + gModelsShift N ρ c ε =
      (wickConstant ρ ε + c.1, sunsetConstant ρ ε + c.2) := by
  refine Prod.ext ?_ ?_ <;> simp only [gModelsShift, Prod.fst_add, Prod.snd_add] <;> ring

private theorem abs_integral_mul_sq_le {k q : SpaceTime → ℝ} {b : ℝ}
    (hk : Integrable k) (hq : ∀ z, |q z| ≤ b) : |∫ z, k z * q z ^ 2| ≤ b ^ 2 * ∫ z, ‖k z‖ := by
  have hb : 0 ≤ b := (abs_nonneg _).trans (hq 0)
  have := norm_integral_le_of_norm_le (hk.norm.const_mul (b ^ 2)) (f := fun z => k z * q z ^ 2)
    (Filter.Eventually.of_forall fun z => by
      rw [norm_mul, norm_pow, Real.norm_eq_abs, mul_comm]
      exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (hq z) 2) (abs_nonneg _))
  rwa [integral_const_mul, Real.norm_eq_abs] at this

private theorem abs_le_div_of_singular {Q : SpaceTime → ℝ} {C ε : ℝ} (hε : 0 < ε) (hC : 0 ≤ C)
    (h : ∀ z, |Q z| ≤ C * (torusParabolicSize z + ε) ^ (-(1 : ℝ))) (z : SpaceTime) :
    |Q z| ≤ C / ε := by
  refine (h z).trans ?_
  rw [Real.rpow_neg_one, div_eq_mul_inv]
  exact mul_le_mul_of_nonneg_left
    (inv_anti₀ hε (le_add_of_nonneg_left (torusParabolicSize_nonneg z))) hC

private theorem torusParabolicSize_zero_aux : torusParabolicSize (0 : SpaceTime) = 0 := by
  unfold torusParabolicSize
  simp [torusSpatialNorm_zero]

/-- A single quadratic bound for the four constants on `(0, 1]`. -/
theorem exists_abs_constants_le (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      |wickConstant ρ ε| ≤ M / ε ^ 2 ∧ |sunsetConstant ρ ε| ≤ M / ε ^ 2 ∧
      |hairerWickConstant N ρ ε| ≤ M / ε ^ 2 ∧ |hairerSunsetConstant N ρ ε| ≤ M / ε ^ 2 := by
  obtain ⟨CQ, hCQ, hQ⟩ := covariance_singular_bound ρ hρ
  obtain ⟨CH, hCH, hH⟩ := hairerCovariance_abs_le_add N ρ hρ
  set IG : ℝ := ∫ z, ‖massiveHeatKernel z‖ with hIG
  set IK : ℝ := ∫ z, ‖hairerKernelTorus N z‖ with hIK
  have hIG0 : 0 ≤ IG := integral_nonneg fun _ => norm_nonneg _
  have hIK0 : 0 ≤ IK := integral_nonneg fun _ => norm_nonneg _
  refine ⟨CQ + CH + 2 * CQ ^ 2 * IG + 2 * CH ^ 2 * IK, by positivity, fun ε hε hε1 => ?_⟩
  have hε2 : 0 < ε ^ 2 := by positivity
  have h1ε : 1 / ε ≤ 1 / ε ^ 2 := one_div_le_one_div_of_le hε2 (by nlinarith)
  have hQb := abs_le_div_of_singular hε hCQ (hQ hε hε1)
  have hHb := abs_le_div_of_singular hε hCH (hH hε hε1)
  have hdiv : ∀ x : ℝ, 0 ≤ x → x / ε ≤ x / ε ^ 2 := fun x hx => by
    rw [div_eq_mul_one_div, div_eq_mul_one_div x (ε ^ 2)]
    exact mul_le_mul_of_nonneg_left h1ε hx
  have hsq : ∀ x : ℝ, 0 ≤ x → (x / ε) ^ 2 = x ^ 2 / ε ^ 2 := fun x _ => by rw [div_pow]
  have hM : ∀ y : ℝ, y ≤ CQ + CH + 2 * CQ ^ 2 * IG + 2 * CH ^ 2 * IK →
      y / ε ^ 2 ≤ (CQ + CH + 2 * CQ ^ 2 * IG + 2 * CH ^ 2 * IK) / ε ^ 2 :=
    fun y hy => div_le_div_of_nonneg_right hy hε2.le
  refine ⟨?_, ?_, ?_, ?_⟩
  · have h0 : |wickConstant ρ ε| ≤ CQ / ε := by
      rw [← covariance_zero]; exact hQb 0
    refine h0.trans ((hdiv CQ hCQ).trans (hM CQ ?_))
    nlinarith [mul_nonneg (sq_nonneg CQ) hIG0, mul_nonneg (sq_nonneg CH) hIK0]
  · have h0 : |sunsetConstant ρ ε| ≤ 2 * ((CQ / ε) ^ 2 * IG) := by
      unfold sunsetConstant
      rw [abs_mul, abs_two]
      exact mul_le_mul_of_nonneg_left
        (abs_integral_mul_sq_le (integrable_massiveHeatKernel) hQb) (by norm_num)
    refine h0.trans (le_trans (le_of_eq ?_) (hM (2 * CQ ^ 2 * IG) ?_))
    · rw [hsq CQ hCQ]; ring
    · nlinarith [sq_nonneg CQ, sq_nonneg CH, mul_nonneg (sq_nonneg CH) hIK0]
  · have h0 : |hairerWickConstant N ρ ε| ≤ CH / ε := by
      rw [hairerWickConstant_eq_covariance_zero]
      have := hH hε hε1 0
      rw [torusParabolicSize_zero_aux, zero_add, Real.rpow_neg_one] at this
      simpa [div_eq_mul_inv] using this
    refine h0.trans ((hdiv CH hCH).trans (hM CH ?_))
    nlinarith [mul_nonneg (sq_nonneg CQ) hIG0, mul_nonneg (sq_nonneg CH) hIK0]
  · have h0 : |hairerSunsetConstant N ρ ε| ≤ 2 * ((CH / ε) ^ 2 * IK) := by
      unfold hairerSunsetConstant
      rw [abs_mul, abs_two]
      exact mul_le_mul_of_nonneg_left
        (abs_integral_mul_sq_le (integrable_constantsComparison_hairerKernelTorus N) hHb)
        (by norm_num)
    refine h0.trans (le_trans (le_of_eq ?_) (hM (2 * CH ^ 2 * IK) ?_))
    · rw [hsq CH hCH]; ring
    · nlinarith [sq_nonneg CQ, sq_nonneg CH, mul_nonneg (sq_nonneg CQ) hIG0]

/-- A function tending to a limit at `0⁺` and bounded by `M / ε²` on `(0, 1]` is bounded there. -/
theorem exists_abs_le_of_tendsto_of_le_div_sq {f : ℝ → ℝ} {L M : ℝ} (hM : 0 ≤ M)
    (hf : Tendsto f (𝓝[>] (0 : ℝ)) (𝓝 L))
    (hb : ∀ ε : ℝ, 0 < ε → ε ≤ 1 → |f ε| ≤ M / ε ^ 2) :
    ∃ B : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → |f ε| ≤ B := by
  have hev := hf.eventually (Metric.ball_mem_nhds L one_pos)
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 hev
  have hu0 : 0 < u := hu
  refine ⟨max (|L| + 1) (M / u ^ 2), fun ε hε hε1 => ?_⟩
  by_cases hεu : ε < u
  · have := hsub ⟨hε, hεu⟩
    rw [Set.mem_ofPred_eq, Real.dist_eq] at this
    refine le_trans ?_ (le_max_left _ _)
    have := abs_sub_abs_le_abs_sub (f ε) L
    linarith [abs_lt.1 ‹|f ε - L| < 1›, abs_nonneg L]
  · refine (hb ε hε hε1).trans (le_trans ?_ (le_max_right _ _))
    exact div_le_div_of_nonneg_left hM (by positivity) (pow_le_pow_left₀ hu0.le (not_lt.1 hεu) 2)

/-- The shift `c^ε` is bounded on `(0, 1]`, given the convergence of the differences of the
`G`- and `K`-constants. -/
theorem exists_norm_gModelsShift_le (N : ℕ) (ρ : ℝ × (Fin 3 → ℝ) → ℝ) (hρ : IsMollifier ρ)
    (c : RenormalisationConstants) {L₁ L₂ : ℝ}
    (h1 : Tendsto (fun ε : ℝ => wickConstant ρ ε - hairerWickConstant N ρ ε) (𝓝[>] 0) (𝓝 L₁))
    (h2 : Tendsto (fun ε : ℝ => sunsetConstant ρ ε - hairerSunsetConstant N ρ ε) (𝓝[>] 0)
      (𝓝 L₂)) :
    ∃ B : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 → ‖gModelsShift N ρ c ε‖ ≤ B := by
  obtain ⟨M, hM, hb⟩ := exists_abs_constants_le N ρ hρ
  obtain ⟨B₁, hB₁⟩ := exists_abs_le_of_tendsto_of_le_div_sq (M := M + M) (add_nonneg hM hM) h1
    fun ε hε hε1 => by
      obtain ⟨a, -, b, -⟩ := hb ε hε hε1
      calc _ ≤ |wickConstant ρ ε| + |hairerWickConstant N ρ ε| := abs_sub _ _
        _ ≤ M / ε ^ 2 + M / ε ^ 2 := add_le_add a b
        _ = _ := by ring
  obtain ⟨B₂, hB₂⟩ := exists_abs_le_of_tendsto_of_le_div_sq (M := M + M) (add_nonneg hM hM) h2
    fun ε hε hε1 => by
      obtain ⟨-, a, -, b⟩ := hb ε hε hε1
      calc _ ≤ |sunsetConstant ρ ε| + |hairerSunsetConstant N ρ ε| := abs_sub _ _
        _ ≤ M / ε ^ 2 + M / ε ^ 2 := add_le_add a b
        _ = _ := by ring
  refine ⟨max (B₁ + |c.1|) (B₂ + |c.2|), fun ε hε hε1 => ?_⟩
  rw [gModelsShift, Prod.norm_def, Real.norm_eq_abs, Real.norm_eq_abs]
  refine max_le_max ?_ ?_
  · exact (abs_add_le _ _).trans (add_le_add (hB₁ ε hε hε1) le_rfl)
  · exact (abs_add_le _ _).trans (add_le_add (hB₂ ε hε hε1) le_rfl)

end RegularityStructures.Phi43

end
