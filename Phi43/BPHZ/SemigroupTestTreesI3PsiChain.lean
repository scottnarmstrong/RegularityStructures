/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestTreesChainIntegral

/-!
# The chain diagram of `I(Ψ³)Ψ`, for arbitrary `z, z'`

`i3PsiChain_bound_global`: for kernels `K, Q` with `|K| ≤ B s^(-3)`, `K = 0` for `|t| > 1`,
`|Q| ≤ B s^(-1)` (no support condition on `Q`), all `z, z'` with `z, z', z - z'` away from the
origin, and `D` bounding `s(w - v)` on the slab `|w.1| ≤ |z.1| + 1`, `|v.1| ≤ |z'.1| + 1`,
`|∫∫ chain| ≤ C D^δ (s(z - z')^(-δ) + s(z)^(-δ) + s(z')^(-δ))`.
There is no smallness assumption on `z, z'`: the recentred kernels `K(z - ·) - K(-·)` vanish
outside the slab, and on the slab `Q(w - v)² ≤ B² D^δ s(w - v)^(-2-δ)`.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

/-- The covariance squared, with a loss `δ` of the exponent, where the size is at most `D`. -/
theorem abs_Q_sq_le_of_le {Q : SpaceTime → ℝ} {B δ D : ℝ} (hδ : 0 ≤ δ)
    (hQ : ∀ x, 0 < torusParabolicSize x → |Q x| ≤ B * torusParabolicSize x ^ (-(1 : ℝ)))
    {x : SpaceTime} (hx : 0 < torusParabolicSize x) (hxD : torusParabolicSize x ≤ D) :
    |Q x| ^ 2 ≤ B ^ 2 * D ^ δ * torusParabolicSize x ^ (-(2 + δ)) := by
  have h1 := hQ x hx
  have hsq : |Q x| ^ 2 ≤ (B * torusParabolicSize x ^ (-(1 : ℝ))) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) h1 2
  have e : (B * torusParabolicSize x ^ (-(1 : ℝ))) ^ 2 =
      B ^ 2 * torusParabolicSize x ^ (-(2 : ℝ)) := by
    rw [mul_pow, ← Real.rpow_natCast (torusParabolicSize x ^ (-(1 : ℝ))) 2,
      ← Real.rpow_mul hx.le]
    norm_num
  have hpow : torusParabolicSize x ^ (-(2 : ℝ)) =
      torusParabolicSize x ^ δ * torusParabolicSize x ^ (-(2 + δ)) := by
    rw [← Real.rpow_add hx]; congr 1; ring
  have hle : torusParabolicSize x ^ δ ≤ D ^ δ := Real.rpow_le_rpow hx.le hxD hδ
  have hnn : 0 ≤ torusParabolicSize x ^ (-(2 + δ)) := Real.rpow_nonneg hx.le _
  calc |Q x| ^ 2 ≤ B ^ 2 * torusParabolicSize x ^ (-(2 : ℝ)) := hsq.trans e.le
    _ = B ^ 2 * (torusParabolicSize x ^ δ * torusParabolicSize x ^ (-(2 + δ))) := by
      rw [hpow]
    _ ≤ B ^ 2 * (D ^ δ * torusParabolicSize x ^ (-(2 + δ))) := by
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg B)
      exact mul_le_mul_of_nonneg_right hle hnn
    _ = _ := by ring

/-- The recentred kernel vanishes outside the slab `|w.1| ≤ |z.1| + 1`. -/
theorem dK_eq_zero_of_abs_lt {K : SpaceTime → ℝ} (hKs : ∀ x : SpaceTime, 1 < |x.1| → K x = 0)
    {z w : SpaceTime} (hw : |z.1| + 1 < |w.1|) : K (z - w) - K (-w) = 0 := by
  have e1 : K (z - w) = 0 := by
    apply hKs
    have : (z - w).1 = z.1 - w.1 := rfl
    rw [this]
    have h := abs_sub_abs_le_abs_sub w.1 z.1
    rw [abs_sub_comm w.1 z.1] at h
    linarith
  have e2 : K (-w) = 0 := by
    apply hKs
    have : (-w).1 = -w.1 := rfl
    rw [this, abs_neg]
    linarith [abs_nonneg z.1]
  rw [e1, e2, sub_zero]

/-- Pointwise majorant of the chain integrand, for arbitrary `z, z'`. -/
theorem abs_i3PsiChain_le_global {K Q : SpaceTime → ℝ} {B δ D : ℝ} (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hD0 : 0 ≤ D)
    (hK : ∀ x, 0 < torusParabolicSize x → |K x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ)))
    (hKs : ∀ x : SpaceTime, 1 < |x.1| → K x = 0)
    (hQ : ∀ x, 0 < torusParabolicSize x → |Q x| ≤ B * torusParabolicSize x ^ (-(1 : ℝ)))
    {z z' u u' w v : SpaceTime}
    (hD : ∀ w v : SpaceTime, |w.1| ≤ |z.1| + 1 → |v.1| ≤ |z'.1| + 1 →
      torusParabolicSize (w - v) ≤ D)
    (h1 : 0 < torusParabolicSize (z - w)) (h0 : 0 < torusParabolicSize (0 - w))
    (hu : 0 < torusParabolicSize (u - w))
    (h1' : 0 < torusParabolicSize (z' - v)) (h0' : 0 < torusParabolicSize (0 - v))
    (hu' : 0 < torusParabolicSize (u' - v)) (hwv : 0 < torusParabolicSize (w - v)) :
    |i3PsiChain K Q z z' u u' w v| ≤
      (4 * B ^ 6 * D ^ δ) * (((singularPow 3 z w + singularPow 3 0 w) * singularPow 1 u w) *
        ((singularPow 4 z' v + singularPow 4 0 v + 2 * singularPow 4 u' v) *
          singularPow (2 + δ) w v)) := by
  have n3 : (0 : ℝ) ≤ D ^ δ := Real.rpow_nonneg hD0 _
  have hrhs : 0 ≤ (4 * B ^ 6 * D ^ δ) * (((singularPow 3 z w + singularPow 3 0 w) *
      singularPow 1 u w) * ((singularPow 4 z' v + singularPow 4 0 v + 2 * singularPow 4 u' v) *
        singularPow (2 + δ) w v)) := by
    refine mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hB 6)) n3)
      (mul_nonneg (mul_nonneg (add_nonneg (singularPow_nonneg _ _ _)
        (singularPow_nonneg _ _ _)) (singularPow_nonneg _ _ _))
        (mul_nonneg ?_ (singularPow_nonneg _ _ _)))
    exact add_nonneg (add_nonneg (singularPow_nonneg _ _ _) (singularPow_nonneg _ _ _))
      (mul_nonneg (by norm_num) (singularPow_nonneg _ _ _))
  by_cases hw : |w.1| ≤ |z.1| + 1
  · by_cases hv : |v.1| ≤ |z'.1| + 1
    · have e : |i3PsiChain K Q z z' u u' w v| =
          |(K (z - w) - K (-w)) * Q (w - u)| *
            (|Q (w - v)| ^ 2 * |(K (z' - v) - K (-v)) * Q (v - u')|) := by
        unfold i3PsiChain
        simp only [abs_mul, abs_pow]
      rw [e]
      have a := abs_dK_mul_Q_le hB hK hQ h1 h0 hu
      have b := abs_dK_mul_Q_le_pow_four hB hK hQ h1' h0' hu'
      have c := abs_Q_sq_le_of_le hδ hQ hwv (hD w v hw hv)
      have hbb : 0 ≤ |(K (z' - v) - K (-v)) * Q (v - u')| := abs_nonneg _
      have key : |(K (z - w) - K (-w)) * Q (w - u)| *
          (|Q (w - v)| ^ 2 * |(K (z' - v) - K (-v)) * Q (v - u')|) ≤
          (2 * B ^ 2 * ((singularPow 3 z w + singularPow 3 0 w) * singularPow 1 u w)) *
            ((B ^ 2 * D ^ δ * singularPow (2 + δ) w v) *
              (2 * B ^ 2 * (singularPow 4 z' v + singularPow 4 0 v + 2 * singularPow 4 u' v))) := by
        have nc : 0 ≤ B ^ 2 * D ^ δ * singularPow (2 + δ) w v :=
          mul_nonneg (mul_nonneg (sq_nonneg B) n3) (singularPow_nonneg _ _ _)
        have nl : 0 ≤ 2 * B ^ 2 * ((singularPow 3 z w + singularPow 3 0 w) *
            singularPow 1 u w) :=
          mul_nonneg (by positivity) (mul_nonneg (add_nonneg (singularPow_nonneg _ _ _)
            (singularPow_nonneg _ _ _)) (singularPow_nonneg _ _ _))
        refine mul_le_mul a (mul_le_mul (by simpa [singularPow] using c) b hbb nc)
          (mul_nonneg (sq_nonneg _) hbb) nl
      refine key.trans (le_of_eq ?_)
      ring
    · have : K (z' - v) - K (-v) = 0 := dK_eq_zero_of_abs_lt hKs (not_le.1 hv)
      have h0 : i3PsiChain K Q z z' u u' w v = 0 := by
        unfold i3PsiChain
        rw [this]
        ring
      rw [h0, abs_zero]
      exact hrhs
  · have : K (z - w) - K (-w) = 0 := dK_eq_zero_of_abs_lt hKs (not_le.1 hw)
    have h0 : i3PsiChain K Q z z' u u' w v = 0 := by
      unfold i3PsiChain
      rw [this]
      ring
    rw [h0, abs_zero]
    exact hrhs

/-- **Chain diagram of `I(Ψ³)Ψ`, for arbitrary `z, z'`.**  The constant depends only on `B, δ`;
`D` bounds `s(w - v)` on the slab `|w.1| ≤ |z.1| + 1`, `|v.1| ≤ |z'.1| + 1`. -/
theorem i3PsiChain_bound_global {B δ : ℝ} (hB : 0 ≤ B) (hδ : 0 < δ) (hδ1 : δ ≤ 1 / 4) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K Q : SpaceTime → ℝ}, Measurable K →
      (∀ x, 0 < torusParabolicSize x → |K x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ))) →
      (∀ x : SpaceTime, 1 < |x.1| → K x = 0) → Measurable Q →
      (∀ x, 0 < torusParabolicSize x → |Q x| ≤ B * torusParabolicSize x ^ (-(1 : ℝ))) →
      ∀ (z z' u u' : SpaceTime) {D : ℝ}, 0 ≤ D →
      (∀ w v : SpaceTime, |w.1| ≤ |z.1| + 1 → |v.1| ≤ |z'.1| + 1 →
        torusParabolicSize (w - v) ≤ D) →
      0 < torusParabolicSize (z - z') → 0 < torusParabolicSize z → 0 < torusParabolicSize z' →
      ((u = z ∧ u' = z') ∨ (u = z' ∧ u' = z)) →
      Integrable (Function.uncurry (i3PsiChain K Q z z' u u')) (volume.prod volume) ∧
        |∫ w, ∫ v, i3PsiChain K Q z z' u u' w v| ≤
          C * D ^ δ * (torusParabolicSize (z - z') ^ (-δ) + torusParabolicSize z ^ (-δ) +
            torusParabolicSize z' ^ (-δ)) := by
  obtain ⟨C0, hC0, h0⟩ := i3PsiChain_majorant_integral hδ hδ1
  refine ⟨4 * B ^ 6 * C0, by positivity, ?_⟩
  intro K Q hKm hK hKs hQm hQ z z' u u' D hD0 hD hzz hz hz' hu
  have hΛ : 0 ≤ 4 * B ^ 6 * D ^ δ :=
    mul_nonneg (mul_nonneg (by norm_num) (pow_nonneg hB 6)) (Real.rpow_nonneg hD0 _)
  have hmeas : Measurable (fun p : SpaceTime × SpaceTime => i3PsiChain K Q z z' u u' p.1 p.2) := by
    unfold i3PsiChain
    fun_prop
  have := h0 (F := i3PsiChain K Q z z' u u') hΛ hmeas.aestronglyMeasurable z z' u u' hzz hz hz' hu (by
    filter_upwards [ae_torusParabolicSize_sub_pos z, ae_torusParabolicSize_sub_pos 0,
      ae_torusParabolicSize_sub_pos u] with w a b c
    filter_upwards [ae_torusParabolicSize_sub_pos z', ae_torusParabolicSize_sub_pos 0,
      ae_torusParabolicSize_sub_pos u', ae_torusParabolicSize_sub_pos w] with v a' b' c' d'
    exact abs_i3PsiChain_le_global hB hδ.le hD0 hK hKs hQ hD a b c a' b' c' d')
  refine ⟨this.1, this.2.trans (le_of_eq ?_)⟩
  ring

end RegularityStructures

end
