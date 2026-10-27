module

public import GlobalPhi43.Attachment.ProbeGaussianProfile
public import GlobalPhi43.Attachment.ProbeSpatialCutoff
import Mathlib.Tactic.Ring

/-! Scaling and norm arithmetic used by the actual annular Gaussian tests. -/

public noncomputable section

open RegularityStructures
open scoped ContDiff

namespace GlobalPhi43.Attachment

/-- Full jets of a linear pullback, retaining the actual scaling factor. -/
theorem probe_jet_comp_bound {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : F → ℝ} (hf : ContDiff ℝ ∞ f) (L : E →L[ℝ] F)
    (k : ℕ) (z : E) {A B : ℝ} (hA : 0 ≤ A)
    (hn : ‖L‖ ≤ B) (hb : ‖iteratedFDeriv ℝ k f (L z)‖ ≤ A) :
    ‖iteratedFDeriv ℝ k (f ∘ L) z‖ ≤ A * B ^ k := by
  rw [ContinuousLinearMap.iteratedFDeriv_comp_right (n := k) L
    (hf.of_le (by exact_mod_cast le_top)) z (by exact_mod_cast le_refl k)]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hp : ∏ _i : Fin k, ‖L‖ ≤ B ^ k := by
    simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_le_pow_left₀ (norm_nonneg _) hn k
  exact mul_le_mul hb hp (Finset.prod_nonneg fun _ _ => norm_nonneg _) hA

/-- The spatial sup norm is controlled by the Euclidean Gaussian quadratic form. -/
theorem probe_norm_sq_le_sqNorm3 (y : Fin 3 → ℝ) : ‖y‖ ^ 2 ≤ sqNorm3 y := by
  have hs : 0 ≤ sqNorm3 y := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hn : ‖y‖ ≤ Real.sqrt (sqNorm3 y) := by
    apply (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr
    intro i
    rw [Real.norm_eq_abs]
    apply (sq_le_sq₀ (abs_nonneg _) (Real.sqrt_nonneg _)).mp
    rw [sq_abs, Real.sq_sqrt hs]
    exact Finset.single_le_sum (fun j _ => sq_nonneg (y j)) (Finset.mem_univ i)
  nlinarith [Real.sq_sqrt hs, norm_nonneg y, Real.sqrt_nonneg (sqNorm3 y)]

/-- On the normalized annulus spatial rapid decay supplies eighteen inverse
powers; it beats the thirteen powers consumed by normalization and four jets. -/
theorem probe_annular_decay_arithmetic {c : ℝ} (hc : 0 < c)
    {y : Fin 3 → ℝ} (hy : c / 4 ≤ ‖y‖) :
    (1 + sqNorm3 y)⁻¹ ^ 9 ≤ (16 : ℝ) ^ 9 * (c⁻¹) ^ 18 := by
  have hs := probe_norm_sq_le_sqNorm3 y
  have hS : 0 ≤ sqNorm3 y := (sq_nonneg ‖y‖).trans hs
  have hh : c ^ 2 / 16 ≤ 1 + sqNorm3 y := by nlinarith [norm_nonneg y]
  have hi := inv_anti₀ (by positivity : 0 < c ^ 2 / 16) hh
  have he : (c ^ 2 / 16)⁻¹ = 16 * (c⁻¹) ^ 2 := by
    field_simp
  rw [he] at hi
  have hp := pow_le_pow_left₀ (by positivity : 0 ≤ (1 + sqNorm3 y)⁻¹) hi 9
  simpa only [mul_pow, ← pow_mul, show 2 * 9 = 18 from rfl] using hp

theorem probe_annular_power_cancel {c : ℝ} (hc : c ≠ 0) :
    c ^ 13 * (c⁻¹) ^ 18 = (c⁻¹) ^ 5 := by
  rw [show 18 = 13 + 5 from rfl, pow_add, ← mul_assoc, ← mul_pow, mul_inv_cancel₀ hc, one_pow, one_mul]

end GlobalPhi43.Attachment
