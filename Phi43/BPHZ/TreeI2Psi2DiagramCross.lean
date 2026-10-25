/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI2Psi2DiagramFour

/-!
# The cross pairings of the tree `I(Ψ²) Ψ²`

Three covariance weights couple the two integration variables `w, w'` of the diagram integral
`∫∫ A(w) A'(w') χ(w, w')`: one in `w` only (`c₁`, singular at a point `g₁`), one in both
(`c₂`, singular on the diagonal `w = w'`), one in `w'` only (`c₃`, singular at a point `h`).
With `|cᵢ| ≤ 2 B s^(-1)` and `a ∈ (0, 1/2)`,
`∫∫ |A| |A'| |c₁| |c₂| |c₃| ≲ B⁵ s(y - x)^a s(y' - x)^a` (`i2Psi2LintBound_chaos4_cross`).
The inner integral is `i2Psi2LintBound_kernel_sub_three` (total order `5 + a`), the outer
integral is bounded (`i2Psi2LintBound_kernel_sub_slab`, total order `3 + a + a + 1 < 5`).
This covers the pairing `c₀₂ c₀₃ c₁₂` of chaos `4` and `c₀₁ c₂₃ c₀₂` of chaos `2`
[Hai14, p. 169-170].
-/

public section

open MeasureTheory

namespace RegularityStructures

/-- **The cross pairing** `∫∫ |A| |A'| |c₁(w)| |c₂(w, w')| |c₃(w')|`, `a ∈ (0, 1/2)`. -/
theorem i2Psi2LintBound_chaos4_cross {a : ℝ} (ha : 0 < a) (ha2 : a < 1 / 2) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K : SpaceTime → ℝ} {B : ℝ} {c₁ c₃ : SpaceTime → ℝ}
      {c₂ : SpaceTime → SpaceTime → ℝ}, 0 ≤ B → Measurable K →
      (∀ u : SpaceTime, 1 < |u.1| → K u = 0) →
      (∀ u : SpaceTime, 0 < torusParabolicSize u →
        |K u| ≤ B * torusParabolicSize u ^ (-(3 : ℝ))) →
      (∀ u h : SpaceTime, 0 < torusParabolicSize u →
        torusParabolicSize h ≤ torusParabolicSize u / 2 →
          |K (u + h) - K u| ≤ B * torusParabolicSize h * torusParabolicSize u ^ (-(4 : ℝ))) →
      Measurable c₁ → Measurable c₃ → Measurable (fun q : SpaceTime × SpaceTime => c₂ q.1 q.2) →
      ∀ x y y' g₁ h : SpaceTime, |y.1 - x.1| ≤ 1 → |y'.1 - x.1| ≤ 1 → |g₁.1 - x.1| ≤ 2 →
        |h.1 - x.1| ≤ 2 →
        (∀ w, 0 < torusParabolicSize (g₁ - w) →
          |c₁ w| ≤ 2 * B * torusParabolicSize (g₁ - w) ^ (-(1 : ℝ))) →
        (∀ w w', 0 < torusParabolicSize (w' - w) →
          |c₂ w w'| ≤ 2 * B * torusParabolicSize (w' - w) ^ (-(1 : ℝ))) →
        (∀ w', 0 < torusParabolicSize (h - w') →
          |c₃ w'| ≤ 2 * B * torusParabolicSize (h - w') ^ (-(1 : ℝ))) →
        i2Psi2LintBound volume (fun q : SpaceTime × SpaceTime =>
          |i2Psi2Increment K x y q.1| * |i2Psi2Increment K x y' q.2| *
            (|c₁ q.1| * |c₂ q.1 q.2| * |c₃ q.2|))
          (C * B ^ 5 * torusParabolicSize (y - x) ^ a * torusParabolicSize (y' - x) ^ a) := by
  obtain ⟨CI, hCI, hI⟩ := i2Psi2LintBound_kernel_sub_three (θ := a) (κ := 1) ha.le
    (by linarith) one_pos (by norm_num) (by linarith)
  obtain ⟨CO, hCO, hO⟩ := i2Psi2LintBound_kernel_sub_slab (θ := a) (l₁ := a) (l₂ := 1) ha.le
    (by linarith) ha.le zero_le_one (by linarith)
  refine ⟨32 * CI * CO, by positivity, ?_⟩
  intro K B c₁ c₃ c₂ hB hKm hKs hKb hKi hm₁ hm₃ hm₂ x y y' g₁ h hxy hxy' hg₁ hh hc₁ hc₂ hc₃
  have mA := measurable_i2Psi2Increment hKm
  have e1 : a + 1 - 1 = a := by ring
  set r := torusParabolicSize (y - x) with hr
  set r' := torusParabolicSize (y' - x) with hr'
  have hr0 : 0 ≤ r ^ a := Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have hr0' : 0 ≤ r' ^ a := Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have nrpow : ∀ (u : SpaceTime) (e : ℝ), 0 ≤ torusParabolicSize u ^ e := fun u e =>
    Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  show i2Psi2LintBound (volume.prod volume) _ _
  refine i2Psi2LintBound.of_prod_symm
    (G := fun w' => |i2Psi2Increment K x y' w'| * (2 * B * torusParabolicSize (h - w') ^ (-(1 : ℝ))) *
      (4 * B ^ 2 * (CI * B * r ^ a * (torusParabolicSize (y - w') ^ (-a) +
        torusParabolicSize (x - w') ^ (-a) + 2 * torusParabolicSize (g₁ - w') ^ (-a))))) ?_ ?_ ?_
  · exact (((continuous_abs.measurable.comp (mA x y)).comp measurable_fst).mul
      ((continuous_abs.measurable.comp (mA x y')).comp measurable_snd)).mul
      ((((continuous_abs.measurable.comp hm₁).comp measurable_fst).mul
        (continuous_abs.measurable.comp hm₂)).mul
        ((continuous_abs.measurable.comp hm₃).comp measurable_snd))
  · filter_upwards [ae_torusParabolicSize_sub_pos y, ae_torusParabolicSize_sub_pos x,
      ae_torusParabolicSize_sub_pos g₁, ae_torusParabolicSize_sub_pos h] with w' hy hx hg hhw
    have hin := hI hB hKb hKi x y g₁ w' hy hx hg
    rw [e1] at hin
    have hcst : 0 ≤ |i2Psi2Increment K x y' w'| * (2 * B * torusParabolicSize (h - w') ^ (-(1 : ℝ))) *
        (4 * B ^ 2) :=
      mul_nonneg (mul_nonneg (abs_nonneg _) (mul_nonneg (by positivity) (nrpow _ _)))
        (by positivity)
    have hc := hin.const_mul (c := |i2Psi2Increment K x y' w'| *
      (2 * B * torusParabolicSize (h - w') ^ (-(1 : ℝ))) * (4 * B ^ 2)) hcst
    refine hc.mono_ae ?_ (le_of_eq (by ring))
    filter_upwards [ae_torusParabolicSize_sub_pos g₁, ae_torusParabolicSize_sub_pos w'] with w hw1 hw2
    have b1 := hc₁ w hw1
    have b2 := hc₂ w w' hw2
    have b3 := hc₃ w' hhw
    have n1 : 0 ≤ 2 * B * torusParabolicSize (g₁ - w) ^ (-(1 : ℝ)) :=
      mul_nonneg (by positivity) (nrpow _ _)
    have n2 : 0 ≤ 2 * B * torusParabolicSize (w' - w) ^ (-(1 : ℝ)) :=
      mul_nonneg (by positivity) (nrpow _ _)
    have h12 := mul_le_mul b1 b2 (abs_nonneg _) n1
    have h123 := mul_le_mul h12 b3 (abs_nonneg _) (mul_nonneg n1 n2)
    have hAA : 0 ≤ |i2Psi2Increment K x y w| * |i2Psi2Increment K x y' w'| :=
      mul_nonneg (abs_nonneg _) (abs_nonneg _)
    calc |i2Psi2Increment K x y w| * |i2Psi2Increment K x y' w'| *
          (|c₁ w| * |c₂ w w'| * |c₃ w'|)
        ≤ |i2Psi2Increment K x y w| * |i2Psi2Increment K x y' w'| *
          (2 * B * torusParabolicSize (g₁ - w) ^ (-(1 : ℝ)) *
            (2 * B * torusParabolicSize (w' - w) ^ (-(1 : ℝ))) *
            (2 * B * torusParabolicSize (h - w') ^ (-(1 : ℝ)))) :=
          mul_le_mul_of_nonneg_left h123 hAA
      _ = _ := by simp only [i2Psi2Increment]; ring
  · have bu : ∀ u : SpaceTime, |u.1 - x.1| ≤ 2 → i2Psi2LintBound volume (fun w' =>
        |i2Psi2Increment K x y' w'| * (torusParabolicSize (u - w') ^ (-a) *
          torusParabolicSize (h - w') ^ (-(1 : ℝ)))) (CO * B * r' ^ a) := fun u hu =>
      hO hB hKs hKb hKi x y' u h hxy' hu hh
    have nn : ∀ (u : SpaceTime) w', 0 ≤ |i2Psi2Increment K x y' w'| *
        (torusParabolicSize (u - w') ^ (-a) * torusParabolicSize (h - w') ^ (-(1 : ℝ))) :=
      fun u w' => mul_nonneg (abs_nonneg _) (mul_nonneg (nrpow _ _) (nrpow _ _))
    have mm : ∀ u : SpaceTime, Measurable fun w' : SpaceTime => |i2Psi2Increment K x y' w'| *
        (torusParabolicSize (u - w') ^ (-a) * torusParabolicSize (h - w') ^ (-(1 : ℝ))) :=
      fun u => (continuous_abs.measurable.comp (mA x y')).mul
        ((measurable_torusParabolicSize_sub_rpow u _).mul
          (measurable_torusParabolicSize_sub_rpow h _))
    have hM : 0 ≤ CO * B * r' ^ a := mul_nonneg (mul_nonneg hCO hB) hr0'
    have hy2 : |y.1 - x.1| ≤ 2 := by linarith
    have hx2 : |x.1 - x.1| ≤ 2 := by simp
    have tg := (bu g₁ hg₁).const_mul (c := 2) (by norm_num)
    have s := i2Psi2LintBound.add_three (mm y) (mm x) (nn y) (nn x)
      (fun w' => mul_nonneg (by norm_num) (nn g₁ w')) hM hM (mul_nonneg (by norm_num) hM)
      (bu y hy2) (bu x hx2) tg
    have c := s.const_mul (c := 8 * B ^ 4 * CI * r ^ a)
      (mul_nonneg (mul_nonneg (by positivity) hCI) hr0)
    refine c.mono (fun w' => ?_) (le_of_eq (by ring))
    ring_nf
    exact le_rfl

end RegularityStructures

end
