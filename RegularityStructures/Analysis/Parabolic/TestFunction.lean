/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Analysis.Parabolic.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Basic
public import Mathlib.Analysis.Calculus.ContDiff.Operations
public import Mathlib.Analysis.Calculus.ContDiff.FTaylorSeries
public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
public import Mathlib.MeasureTheory.Constructions.Pi
public import Mathlib.MeasureTheory.Group.Integral
public import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Rescaled test functions in parabolic space

For `φ : ℝ × ℝ³ → ℝ`, a scale `c > 0` and a base point `z`, the rescaled test function is
`φ^c_z(w) = c⁻⁵ φ((w₀ - z₀)/c², (w' - z')/c)` (Hairer, arXiv:1303.5113v4, (2.13)-(3.7)).
The class `B^r` is the set of smooth `φ` supported in the closed unit parabolic ball with
`‖D^k φ‖ ≤ 1` for `k ≤ r`.

We prove the algebra of `parabolicDilate`, the support and integral identities
(`rescaledTestFunction_eq_zero`, `integral_rescaledTestFunction`) and derivative bounds
(`norm_iteratedFDeriv_rescaledTestFunction_le`).
-/

@[expose] public noncomputable section

namespace RegularityStructures

/-- `φ^c_z(w) = c⁻⁵ φ((w₀ − z₀)/c², (w' − z')/c)`. -/
def rescaledTestFunction (φ : ParabolicSpace → ℝ) (c : ℝ) (z w : ParabolicSpace) : ℝ :=
  (c ^ 5)⁻¹ * φ (parabolicDilate c⁻¹ (w - z))

open scoped ContDiff in
/-- `B^r`: smooth functions vanishing outside the closed unit parabolic ball, with
`‖D^k φ‖ ≤ 1` for `k ≤ r`. -/
def testFunctionClass (r : ℕ) : Set (ParabolicSpace → ℝ) :=
  {φ | ContDiff ℝ ∞ φ ∧ (∀ w, 1 < parabolicNorm w → φ w = 0) ∧
    ∀ k ≤ r, ∀ w, ‖iteratedFDeriv ℝ k φ w‖ ≤ 1}

/-- The parabolic dilation as a continuous linear map. -/
def parabolicDilateCLM (c : ℝ) : ParabolicSpace →L[ℝ] ParabolicSpace :=
  (c ^ 2 • ContinuousLinearMap.fst ℝ ℝ (Fin 3 → ℝ)).prod
    (c • ContinuousLinearMap.snd ℝ ℝ (Fin 3 → ℝ))

end RegularityStructures

end

public section

namespace RegularityStructures

@[simp]
theorem parabolicDilateCLM_apply (c : ℝ) (z : ParabolicSpace) :
    parabolicDilateCLM c z = parabolicDilate c z := by
  simp [parabolicDilateCLM, parabolicDilate]

@[simp]
theorem parabolicDilate_one (z : ParabolicSpace) : parabolicDilate 1 z = z := by
  simp [parabolicDilate]

theorem parabolicDilate_mul (a b : ℝ) (z : ParabolicSpace) :
    parabolicDilate (a * b) z = parabolicDilate a (parabolicDilate b z) := by
  simp only [parabolicDilate, Prod.mk.injEq, mul_smul]
  exact ⟨by ring, trivial⟩

theorem parabolicDilate_sub (c : ℝ) (z w : ParabolicSpace) :
    parabolicDilate c (z - w) = parabolicDilate c z - parabolicDilate c w := by
  simp only [parabolicDilate, Prod.fst_sub, Prod.snd_sub, smul_sub, mul_sub]
  rfl

theorem parabolicDilate_inv_parabolicDilate {c : ℝ} (hc : c ≠ 0) (z : ParabolicSpace) :
    parabolicDilate c⁻¹ (parabolicDilate c z) = z := by
  rw [← parabolicDilate_mul, inv_mul_cancel₀ hc, parabolicDilate_one]

theorem parabolicDilate_parabolicDilate_inv {c : ℝ} (hc : c ≠ 0) (z : ParabolicSpace) :
    parabolicDilate c (parabolicDilate c⁻¹ z) = z := by
  rw [← parabolicDilate_mul, mul_inv_cancel₀ hc, parabolicDilate_one]

theorem parabolicNorm_parabolicDilate_inv {c : ℝ} (hc : 0 < c) (z : ParabolicSpace) :
    parabolicNorm (parabolicDilate c⁻¹ z) = c⁻¹ * parabolicNorm z :=
  parabolicNorm_parabolicDilate (inv_nonneg.2 hc.le) z

theorem rescaledTestFunction_eq_zero {φ : ParabolicSpace → ℝ}
    (hφ : ∀ w, 1 < parabolicNorm w → φ w = 0) {c : ℝ} (hc : 0 < c) {z w : ParabolicSpace}
    (h : c < parabolicNorm (w - z)) : rescaledTestFunction φ c z w = 0 := by
  unfold rescaledTestFunction
  rw [hφ _ ?_, mul_zero]
  rw [parabolicNorm_parabolicDilate_inv hc, lt_inv_mul_iff₀ hc]
  simpa using h

theorem measurable_parabolicDilate (c : ℝ) : Measurable (parabolicDilate c) := by
  unfold parabolicDilate
  fun_prop

/-- The parabolic dilation by `d ≠ 0` as a measurable equivalence. -/
noncomputable def parabolicDilateEquiv {d : ℝ} (hd : d ≠ 0) : ParabolicSpace ≃ᵐ ParabolicSpace where
  toFun := parabolicDilate d
  invFun := parabolicDilate d⁻¹
  left_inv := parabolicDilate_inv_parabolicDilate hd
  right_inv := parabolicDilate_parabolicDilate_inv hd
  measurable_toFun := measurable_parabolicDilate d
  measurable_invFun := measurable_parabolicDilate d⁻¹

theorem map_volume_parabolicDilate {d : ℝ} (hd : d ≠ 0) :
    MeasureTheory.Measure.map (parabolicDilate d)
      (MeasureTheory.volume : MeasureTheory.Measure ParabolicSpace) =
      ENNReal.ofReal |(d ^ 5)⁻¹| • MeasureTheory.volume := by
  have h1 : MeasureTheory.Measure.map (fun t : ℝ => d ^ 2 * t) MeasureTheory.volume =
      ENNReal.ofReal |(d ^ 2)⁻¹| • MeasureTheory.volume :=
    Real.map_volume_mul_left (pow_ne_zero 2 hd)
  have h2 : MeasureTheory.Measure.map (fun x : Fin 3 → ℝ => d • x) MeasureTheory.volume =
      ENNReal.ofReal |(d ^ 3)⁻¹| • MeasureTheory.volume := by
    simpa using MeasureTheory.Measure.map_addHaar_smul
      (MeasureTheory.volume : MeasureTheory.Measure (Fin 3 → ℝ)) hd
  have h3 : parabolicDilate d = Prod.map (fun t : ℝ => d ^ 2 * t) (fun x : Fin 3 → ℝ => d • x) :=
    rfl
  rw [MeasureTheory.Measure.volume_eq_prod, h3,
    ← MeasureTheory.Measure.map_prod_map _ _ (by fun_prop) (by fun_prop), h1, h2,
    MeasureTheory.Measure.prod_smul_left, MeasureTheory.Measure.prod_smul_right, smul_smul,
    ← ENNReal.ofReal_mul (abs_nonneg _), ← abs_mul]
  congr 3
  ring

theorem integral_comp_parabolicDilate (φ : ParabolicSpace → ℝ) {d : ℝ} (hd : 0 < d) :
    ∫ w, φ (parabolicDilate d w) = (d ^ 5)⁻¹ * ∫ w, φ w := by
  have hd' : d ≠ 0 := hd.ne'
  have := (parabolicDilateEquiv hd').measurableEmbedding.integral_map (μ := MeasureTheory.volume) φ
  have e : ∫ w, φ (parabolicDilate d w) = ∫ y, φ y ∂(MeasureTheory.Measure.map
      (parabolicDilateEquiv hd') MeasureTheory.volume) := this.symm
  rw [e]
  have : (MeasureTheory.Measure.map (parabolicDilateEquiv hd') MeasureTheory.volume) =
      MeasureTheory.Measure.map (parabolicDilate d) MeasureTheory.volume := rfl
  rw [this, map_volume_parabolicDilate hd', MeasureTheory.integral_smul_measure,
    ENNReal.toReal_ofReal (abs_nonneg _), abs_of_pos (by positivity), smul_eq_mul]

theorem integral_rescaledTestFunction (φ : ParabolicSpace → ℝ) {c : ℝ} (hc : 0 < c)
    (z : ParabolicSpace) :
    ∫ w, rescaledTestFunction φ c z w = ∫ w, φ w := by
  unfold rescaledTestFunction
  have : (MeasureTheory.volume : MeasureTheory.Measure ParabolicSpace).IsAddRightInvariant := by
    rw [MeasureTheory.Measure.volume_eq_prod]
    infer_instance
  rw [MeasureTheory.integral_const_mul,
    MeasureTheory.integral_sub_right_eq_self (fun w => φ (parabolicDilate c⁻¹ w)) z,
    integral_comp_parabolicDilate φ (inv_pos.2 hc), inv_pow, inv_inv, ← mul_assoc,
    inv_mul_cancel₀ (by positivity), one_mul]

theorem norm_parabolicDilateCLM_le {d : ℝ} (hd : 1 ≤ d) : ‖parabolicDilateCLM d‖ ≤ d ^ 2 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun z => ?_
  have h0 : 0 ≤ d := by linarith
  have h1 : d ≤ d ^ 2 := by nlinarith
  rw [parabolicDilateCLM_apply, Prod.norm_def]
  simp only [parabolicDilate]
  refine max_le ?_ ?_
  · rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (le_trans (Prod.norm_def z ▸ le_max_left _ _) le_rfl) (by positivity)
  · rw [norm_smul, Real.norm_of_nonneg h0]
    calc d * ‖z.2‖ ≤ d ^ 2 * ‖z.2‖ := by gcongr
      _ ≤ d ^ 2 * ‖z‖ := by
        gcongr
        exact le_max_right _ _

theorem rescaledTestFunction_eq_comp (φ : ParabolicSpace → ℝ) (c : ℝ) (z : ParabolicSpace) :
    rescaledTestFunction φ c z =
      (c ^ 5)⁻¹ • ((fun u => φ (u - parabolicDilate c⁻¹ z)) ∘ parabolicDilateCLM c⁻¹) := by
  funext w
  simp [rescaledTestFunction, parabolicDilate_sub]

theorem contDiff_rescaledTestFunction {n : WithTop ℕ∞} {φ : ParabolicSpace → ℝ}
    (hφ : ContDiff ℝ n φ) (c : ℝ) (z : ParabolicSpace) :
    ContDiff ℝ n (rescaledTestFunction φ c z) := by
  rw [rescaledTestFunction_eq_comp]
  exact (((hφ.comp (contDiff_id.sub contDiff_const))).comp (parabolicDilateCLM c⁻¹).contDiff).const_smul ((c ^ 5)⁻¹ : ℝ)

end RegularityStructures

end
