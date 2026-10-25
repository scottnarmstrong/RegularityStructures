/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI2Psi2DiagramMultiProd

/-!
# The cross pairing with general exponents

For `A(w) = K(y - w) - K(x - w)`, `A'(w') = K(y' - w') - K(x - w')`: three weights couple the
variables `w, w'`, namely `s(g₁ - w)^(-e₁)` (in `w` only), `s(w' - w)^(-e₂)` (both) and
`s(h - w')^(-e₃)` (in `w'` only).  If `3 + γ + e₁ < 5`, `2 < γ + e₁ + e₂` and
`3 + γ' + (γ + e₁ + e₂ - 2) + e₃ < 5`, then
`∫∫ |A| |A'| s(g₁ - w)^(-e₁) s(w' - w)^(-e₂) s(h - w')^(-e₃) ≲ B² r^γ r'^γ'`
(`i2Psi2LintBound_diag_cross`).  It generalises `i2Psi2LintBound_chaos4_cross`.
-/

public section

open MeasureTheory

namespace RegularityStructures

/-- **The cross pairing, general exponents.** -/
theorem i2Psi2LintBound_diag_cross {γ γ' e₁ e₂ e₃ : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hγ'0 : 0 ≤ γ') (hγ'1 : γ' ≤ 1) (he₁ : 0 ≤ e₁) (he₂ : 0 < e₂) (he₃ : 0 ≤ e₃)
    (h5 : 3 + γ + e₁ < 5) (he₂5 : e₂ < 5) (hs : 2 < γ + e₁ + e₂)
    (hslab : 3 + γ' + (γ + e₁ + e₂ - 2) + e₃ < 5) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K : SpaceTime → ℝ} {B : ℝ}, i2Psi2KernelHyp K B →
      ∀ x y y' g₁ h : SpaceTime, |y.1 - x.1| ≤ 1 → |y'.1 - x.1| ≤ 1 → |g₁.1 - x.1| ≤ 2 →
        |h.1 - x.1| ≤ 2 →
        i2Psi2LintBound volume (fun q : SpaceTime × SpaceTime =>
          |i2Psi2Increment K x y q.1| * |i2Psi2Increment K x y' q.2| *
            (torusParabolicSize (g₁ - q.1) ^ (-e₁) * torusParabolicSize (q.2 - q.1) ^ (-e₂) *
              torusParabolicSize (h - q.2) ^ (-e₃)))
          (C * B ^ 2 * torusParabolicSize (y - x) ^ γ * torusParabolicSize (y' - x) ^ γ') := by
  obtain ⟨CI, hCI, hI⟩ := i2Psi2LintBound_kernel_sub_pair hγ0 hγ1 he₁ he₂ h5 he₂5 hs
  obtain ⟨CO, hCO, hO⟩ := i2Psi2LintBound_kernel_sub_slab (θ := γ') (l₁ := γ + e₁ + e₂ - 2)
    (l₂ := e₃) hγ'0 hγ'1 (by linarith) he₃ (by linarith)
  refine ⟨4 * CI * CO, by positivity, ?_⟩
  intro K B hK x y y' g₁ h hxy hxy' hg₁ hh
  obtain ⟨hB, hKm, hKs, hKb, hKi⟩ := id hK
  have mA := measurable_i2Psi2Increment hKm
  set r := torusParabolicSize (y - x) with hr
  set r' := torusParabolicSize (y' - x) with hr'
  set p := γ + e₁ + e₂ - 2 with hp
  have hr0 : 0 ≤ r ^ γ := Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have hr0' : 0 ≤ r' ^ γ' := Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have nrpow : ∀ (u : SpaceTime) (e : ℝ), 0 ≤ torusParabolicSize u ^ e := fun u e =>
    Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  show i2Psi2LintBound (volume.prod volume) _ _
  refine i2Psi2LintBound.of_prod_symm
    (G := fun w' => |i2Psi2Increment K x y' w'| * torusParabolicSize (h - w') ^ (-e₃) *
      (CI * B * r ^ γ * (torusParabolicSize (y - w') ^ (-p) + torusParabolicSize (x - w') ^ (-p) +
        2 * torusParabolicSize (g₁ - w') ^ (-p)))) ?_ ?_ ?_
  · exact (((continuous_abs.measurable.comp (mA x y)).comp measurable_fst).mul
      ((continuous_abs.measurable.comp (mA x y')).comp measurable_snd)).mul
      ((((measurable_torusParabolicSize_sub_rpow g₁ _).comp measurable_fst).mul
        ((Phi43.measurable_torusParabolicSize.comp (measurable_snd.sub measurable_fst)).pow_const
          _)).mul ((measurable_torusParabolicSize_sub_rpow h _).comp measurable_snd))
  · filter_upwards [ae_torusParabolicSize_sub_pos y, ae_torusParabolicSize_sub_pos x,
      ae_torusParabolicSize_sub_pos g₁] with w' hy hx hg
    have hin := hI hK x y g₁ w' hy hx hg
    have hcst : 0 ≤ |i2Psi2Increment K x y' w'| * torusParabolicSize (h - w') ^ (-e₃) :=
      mul_nonneg (abs_nonneg _) (nrpow _ _)
    have hc := hin.const_mul (c := |i2Psi2Increment K x y' w'| *
      torusParabolicSize (h - w') ^ (-e₃)) hcst
    refine hc.mono (fun w => ?_) (le_of_eq (by ring))
    simp only [i2Psi2Increment]
    exact le_of_eq (by ring)
  · have bu : ∀ u : SpaceTime, |u.1 - x.1| ≤ 2 → i2Psi2LintBound volume (fun w' =>
        |i2Psi2Increment K x y' w'| * (torusParabolicSize (u - w') ^ (-p) *
          torusParabolicSize (h - w') ^ (-e₃))) (CO * B * r' ^ γ') := fun u hu =>
      hO hB hKs hKb hKi x y' u h hxy' hu hh
    have nn : ∀ (u : SpaceTime) w', 0 ≤ |i2Psi2Increment K x y' w'| *
        (torusParabolicSize (u - w') ^ (-p) * torusParabolicSize (h - w') ^ (-e₃)) :=
      fun u w' => mul_nonneg (abs_nonneg _) (mul_nonneg (nrpow _ _) (nrpow _ _))
    have mm : ∀ u : SpaceTime, Measurable fun w' : SpaceTime => |i2Psi2Increment K x y' w'| *
        (torusParabolicSize (u - w') ^ (-p) * torusParabolicSize (h - w') ^ (-e₃)) :=
      fun u => (continuous_abs.measurable.comp (mA x y')).mul
        ((measurable_torusParabolicSize_sub_rpow u _).mul
          (measurable_torusParabolicSize_sub_rpow h _))
    have hM : 0 ≤ CO * B * r' ^ γ' := mul_nonneg (mul_nonneg hCO hB) hr0'
    have hy2 : |y.1 - x.1| ≤ 2 := by linarith
    have hx2 : |x.1 - x.1| ≤ 2 := by simp
    have tg := (bu g₁ hg₁).const_mul (c := 2) (by norm_num)
    have s := i2Psi2LintBound.add_three (mm y) (mm x) (nn y) (nn x)
      (fun w' => mul_nonneg (by norm_num) (nn g₁ w')) hM hM (mul_nonneg (by norm_num) hM)
      (bu y hy2) (bu x hx2) tg
    have c := s.const_mul (c := CI * B * r ^ γ) (mul_nonneg (mul_nonneg hCI hB) hr0)
    refine c.mono (fun w' => ?_) (le_of_eq (by ring))
    exact le_of_eq (by ring)

end RegularityStructures

end
