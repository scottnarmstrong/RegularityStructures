/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.ShiftedPiRegPiTrees
public import Phi43.BPHZ.BphzCauchyMomentDefs
public import Phi43.BPHZ.RandomCanonicalModel
public import Phi43.BPHZ.GammaFullMinkowski
public import Phi43.BPHZ.GammaFullUniform
import Mathlib.Tactic

/-!
# Ingredients for the moment bounds of the shifted rows

* measurability in `ω` of the rows `Q_t Π_x τ (x)` and of the gradients `gₖ`;
* the deterministic bounds `|∫ Q_t| ≤ M₀`, `|∫ Q_t (yₖ - xₖ)| ≤ M₁ t^(1/4)`;
* the `L^q` norm calculus used for the linear combinations: constants, sums, products through
  `L^(2q)` and the monotonicity in the power of `t`.
-/

public section

open MeasureTheory

universe u

namespace RegularityStructures.Phi43

open RegularityStructures

variable {N : ℕ} {κ : Kappa} {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
  {W : (SpaceTime → ℝ) → Ω → ℝ} {ρ : ℝ × (Fin 3 → ℝ) → ℝ} {ε : ℝ} {ξ : Ω → SpaceTime → ℝ}

theorem measurable_shiftedPiReg (hξ : IsRegularisedNoise P W ρ ε ξ)
    (hgr : ∀ ω, Statements.HasPhi43NoiseGrowth (ξ ω)) (C : RenormalisationConstants)
    (x : ParabolicSpace) {t : ℝ} (ht : 0 < t) (τ : Symbol) :
    Measurable fun ω => shiftedPiReg N κ C (ξ ω) x t τ :=
  (isContinuousRandomModelOn_canonicalModelOfLift (N := N) (κ := κ) (C := C)
    (fun z => (hξ.2 z).1) hξ.1 hgr Set.univ).1 τ x t ht

theorem measurable_shiftedPiGrad (hξ : IsRegularisedNoise P W ρ ε ξ) (x : ParabolicSpace)
    (k : Fin 3) : Measurable fun ω => shiftedPiGrad N ξ ω x k :=
  measurable_integral_mul_field (measurable_hairerPsiField_uncurry N hξ)
    ((measurable_hairerKernelTorusGrad N k).comp (measurable_const.sub measurable_id))

theorem abs_shiftedPiMass_le {t : ℝ} (ht : 0 < t) (x : ParabolicSpace) :
    |shiftedPiMass t x| ≤ parabolicSemigroup.momentConst 0 := by
  have h := parabolicSemigroup.moment_le ht (le_refl (0 : ℝ)) x
  simp only [Real.rpow_zero, mul_one, zero_div] at h
  unfold shiftedPiMass
  refine (abs_integral_le_integral_abs).trans ?_
  simpa using h

theorem abs_shiftedPiMoment_le {t : ℝ} (ht : 0 < t) (x : ParabolicSpace) (k : Fin 3) :
    |shiftedPiMoment t x k| ≤ parabolicSemigroup.momentConst 1 * t ^ (1 / 4 : ℝ) := by
  have h := parabolicSemigroup.moment_le ht (zero_le_one : (0 : ℝ) ≤ 1) x
  have hi := parabolicSemigroup.integrable_moment ht (zero_le_one : (0 : ℝ) ≤ 1) x
  have hm : parabolicSemigroup.order = 4 := rfl
  rw [hm] at h
  unfold shiftedPiMoment
  refine (abs_integral_le_integral_abs).trans (le_trans ?_ h)
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => abs_nonneg _) hi
    (Filter.Eventually.of_forall fun y => ?_)
  beta_reduce
  rw [abs_mul, Real.rpow_one]
  exact mul_le_mul_of_nonneg_left (abs_coord_sub_le x y k) (abs_nonneg _)

section Calculus

variable {f g : Ω → ℝ} {q : ℕ}

/-- A deterministic real has `L^q` norm at most its absolute value (probability measure). -/
theorem lintegral_enorm_pow_const_le [IsProbabilityMeasure P] (c : ℝ) {A : ℝ} (h : |c| ≤ A) :
    ∫⁻ _ : Ω, ‖c‖ₑ ^ q ∂P ≤ ENNReal.ofReal A ^ q := by
  rw [lintegral_const, measure_univ, mul_one, Real.enorm_eq_ofReal_abs]
  exact pow_le_pow_left' (ENNReal.ofReal_le_ofReal h) q

/-- Monotonicity in the power of `t ∈ (0, 1]`. -/
theorem shiftedPi_tpow_mono {t e₁ e₂ A : ℝ} (hA : 0 ≤ A) (ht : t ∈ Set.Ioc (0 : ℝ) 1)
    (he : e₁ ≤ e₂) : A * t ^ e₂ ≤ A * t ^ e₁ :=
  mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge ht.1 ht.2 he) hA

end Calculus

end RegularityStructures.Phi43

end
