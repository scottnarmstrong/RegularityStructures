/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import RegularityStructures.Torus.HolderBesovPoissonKernel
public import Mathlib.MeasureTheory.Integral.Pi

/-!
# Scale-uniform tensor Fourier multipliers on the three-torus

The circle Poisson bounds tensorize: the L1 norm of a product of three coordinate kernels
equals the product of their L1 norms. All measurability and integrability follow from the
Schwartz profiles; no kernel estimate is assumed.

This is the multiplier bound for tensor-product cutoff profiles, including the localized
inverse-heat multiplier appearing in the reverse norm comparison.
-/

public noncomputable section

open MeasureTheory Set
open scoped ENNReal FourierTransform SchwartzMap

namespace RegularityStructures

theorem lintegral_torus_tensor_multiplier_le (m : Fin 3 → 𝓢(ℝ, ℂ))
    {a : ℝ} (ha : 0 < a) :
    (∫⁻ x : Torus3, ‖∏ i : Fin 3,
      ∑' k : ℤ, m i ((k : ℝ) / a) * fourier k (x i)‖ₑ) ≤
        ∏ i : Fin 3, ∫⁻ y : ℝ, ‖(𝓕⁻ (m i) : 𝓢(ℝ, ℂ)) y‖ₑ := by
  let K : Fin 3 → UnitAddCircle → ℂ :=
    fun i x => ∑' k : ℤ, m i ((k : ℝ) / a) * fourier k x
  have hc (i : Fin 3) : Continuous (K i) := continuous_schwartz_multiplier_circle (m i) ha
  have hI (i : Fin 3) : Integrable (K i) :=
    (hc i).integrable_of_hasCompactSupport (isClosed_tsupport _).isCompact
  have hprod : Integrable (fun x : Torus3 => ∏ i : Fin 3, K i (x i)) :=
    Integrable.fintype_prod hI
  change (∫⁻ x : Torus3, ‖∏ i : Fin 3, K i (x i)‖ₑ) ≤ _
  rw [← ofReal_integral_norm_eq_lintegral_enorm hprod]
  simp_rw [norm_prod]
  have hfactor : (∫ x : Torus3, ∏ i : Fin 3, ‖K i (x i)‖) =
      ∏ i : Fin 3, ∫ x : UnitAddCircle, ‖K i x‖ :=
    integral_fintype_prod_volume_eq_prod (fun i : Fin 3 => fun x : UnitAddCircle => ‖K i x‖)
  rw [hfactor,
    ENNReal.ofReal_prod_of_nonneg (fun _ _ => integral_nonneg fun _ => norm_nonneg _)]
  simp_rw [ofReal_integral_norm_eq_lintegral_enorm (hI _)]
  apply Finset.prod_le_prod
  intro i _
  exact lintegral_schwartz_multiplier_circle_le (m i) ha

theorem schwartz_torus_tensor_multiplier_bound_uniform (m : Fin 3 → 𝓢(ℝ, ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ℝ, 0 < a →
      (∫⁻ x : Torus3, ‖∏ i : Fin 3,
        ∑' k : ℤ, m i ((k : ℝ) / a) * fourier k (x i)‖ₑ) ≤ ENNReal.ofReal C := by
  let L : ℝ≥0∞ := ∏ i : Fin 3, ∫⁻ y : ℝ, ‖(𝓕⁻ (m i) : 𝓢(ℝ, ℂ)) y‖ₑ
  have hL : L ≠ ∞ := by
    apply ENNReal.prod_ne_top
    intro i _
    exact (hasFiniteIntegral_iff_enorm.mp
      (𝓕⁻ (m i) : 𝓢(ℝ, ℂ)).integrable.hasFiniteIntegral).ne
  refine ⟨L.toReal, ENNReal.toReal_nonneg, fun a ha => ?_⟩
  rw [ENNReal.ofReal_toReal hL]
  exact lintegral_torus_tensor_multiplier_le m ha

end RegularityStructures

end
