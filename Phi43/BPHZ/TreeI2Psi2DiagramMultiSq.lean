/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI2Psi2DiagramMultiBasic
public import Phi43.BPHZ.TreeI2Psi2DiagramPair

/-!
# The principal pairing and the product pairings with general exponents

For `A(w) = K(y - w) - K(x - w)`, `A'(w') = K(y' - w') - K(x - w')`, `r = s(y - x)`,
`r' = s(y' - x)`, `d = s(y - y')`, and pure singular weights:

* `i2Psi2LintBound_diag_sq`: `∫∫ |A| |A'| s(w' - w)^(-e) ≲ B² r^γ r'^γ'`;
* `i2Psi2LintBound_diag_prod_single`: `(∫ |A| s(y' - w)^(-e₁)) (∫ |A'| s(y - w')^(-e₂))`;
* `i2Psi2LintBound_diag_prod_pair`: the product of two pair integrals
  `(∫ |A| s(y - w)^(-e₁) s(y' - w)^(-e₂)) (∫ |A'| s(y' - w')^(-e₃) s(y - w')^(-e₄))`.

They generalise `i2Psi2LintBound_chaos4_sq`, `_chaos4_prod` and `_chaos2_prod` to free exponents.
-/

public section

open MeasureTheory

namespace RegularityStructures

/-- **Principal pairing, general exponent**: `∫∫ |A| |A'| s(w' - w)^(-e) ≲ B² r^γ r'^γ'`. -/
theorem i2Psi2LintBound_diag_sq {γ γ' e : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hγ'0 : 0 ≤ γ')
    (hγ'1 : γ' ≤ 1) (he5 : e < 5) (hγe : 2 < γ + e) (hslab : 3 + γ' + (γ + e - 2) < 5) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K : SpaceTime → ℝ} {B : ℝ}, i2Psi2KernelHyp K B →
      ∀ x y y' : SpaceTime, |y.1 - x.1| ≤ 1 → |y'.1 - x.1| ≤ 1 →
        i2Psi2LintBound volume (fun q : SpaceTime × SpaceTime =>
          |i2Psi2Increment K x y q.1| * |i2Psi2Increment K x y' q.2| *
            torusParabolicSize (q.2 - q.1) ^ (-e))
          (C * B ^ 2 * torusParabolicSize (y - x) ^ γ * torusParabolicSize (y' - x) ^ γ') := by
  obtain ⟨C1, hC1, h1⟩ := i2Psi2LintBound_kernel_sub_single hγ0 hγ1 he5 hγe
  obtain ⟨CO, hCO, hO⟩ := i2Psi2LintBound_kernel_sub_slab (θ := γ') (l₁ := γ + e - 2) (l₂ := 0)
    hγ'0 hγ'1 (by linarith) le_rfl (by linarith)
  refine ⟨2 * C1 * CO, by positivity, ?_⟩
  intro K B hK x y y' hxy hxy'
  obtain ⟨hB, hKm, hKs, hKb, hKi⟩ := hK
  have hK' : i2Psi2KernelHyp K B := ⟨hB, hKm, hKs, hKb, hKi⟩
  have mA := measurable_i2Psi2Increment hKm
  set r := torusParabolicSize (y - x) with hr
  set r' := torusParabolicSize (y' - x) with hr'
  have hr0 : 0 ≤ r ^ γ := Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have hr0' : 0 ≤ r' ^ γ' := Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  set p := γ + e - 2 with hp
  show i2Psi2LintBound (volume.prod volume) _ _
  refine i2Psi2LintBound.of_prod_symm
    (G := fun w' => |i2Psi2Increment K x y' w'| * (C1 * B * r ^ γ *
      (torusParabolicSize (y - w') ^ (-p) + torusParabolicSize (x - w') ^ (-p)))) ?_ ?_ ?_
  · exact (((continuous_abs.measurable.comp (mA x y)).comp measurable_fst).mul
      ((continuous_abs.measurable.comp (mA x y')).comp measurable_snd)).mul
      ((Phi43.measurable_torusParabolicSize.comp (measurable_snd.sub measurable_fst)).pow_const _)
  · filter_upwards [ae_torusParabolicSize_sub_pos y, ae_torusParabolicSize_sub_pos x]
      with w' hy hx
    have h := (h1 hK' x y w' hy hx).const_mul (c := |i2Psi2Increment K x y' w'|)
      (abs_nonneg _)
    refine h.mono (fun w => ?_) le_rfl
    simp only [i2Psi2Increment]
    exact le_of_eq (by ring)
  · have e0 : ∀ u : SpaceTime, torusParabolicSize u ^ (-(0 : ℝ)) = 1 := fun u => by simp
    have hy2 : |y.1 - x.1| ≤ 2 := by linarith
    have hOy := hO hB hKs hKb hKi x y' y x hxy' hy2 (by simp)
    have hOx := hO hB hKs hKb hKi x y' x y hxy' (by simp) hy2
    have nn : ∀ (g₁ g₂ : SpaceTime) w', 0 ≤ |i2Psi2Increment K x y' w'| *
        (torusParabolicSize (g₁ - w') ^ (-p) * torusParabolicSize (g₂ - w') ^ (-(0 : ℝ))) :=
      fun g₁ g₂ w' => mul_nonneg (abs_nonneg _) (mul_nonneg
        (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
        (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))
    have hM : 0 ≤ CO * B * r' ^ γ' := mul_nonneg (mul_nonneg hCO hB) hr0'
    have mm : Measurable fun w' : SpaceTime => |i2Psi2Increment K x y' w'| *
        (torusParabolicSize (y - w') ^ (-p) * torusParabolicSize (x - w') ^ (-(0 : ℝ))) :=
      (continuous_abs.measurable.comp (mA x y')).mul
        ((measurable_torusParabolicSize_sub_rpow y _).mul
          (measurable_torusParabolicSize_sub_rpow x _))
    have s := hOy.add mm.aemeasurable (nn y x) (nn x y) hM hM hOx
    have c := s.const_mul (c := C1 * B * r ^ γ)
      (mul_nonneg (mul_nonneg hC1 hB) hr0)
    refine c.mono (fun w' => ?_) (le_of_eq (by ring))
    simp only [e0, mul_one]
    exact le_of_eq (by ring)

end RegularityStructures

end
