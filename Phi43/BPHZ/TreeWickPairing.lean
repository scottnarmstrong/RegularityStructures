/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SingularConvolution
public import Phi43.Stochastic.ConstantsComparisonConvolution

/-!
# Pairings of two singular kernels

For `f`, `g` with `|f| ≤ B₁ s^(-a)` and `|g| ≤ B₂ s^(-b)` away from the origin, `0 < a, b < 5`,
`a + b > 5`, the pairing `x ↦ ∫ f(x + w) g(w) dw` is bounded by `C B₁ B₂ s(x)^(5-a-b)`
[Hai14, Lemma 10.14].  This is `abs_integral_mul_singular_le_of_gt` for the shifted (rather than
reflected) first factor.
-/

public section

open MeasureTheory

namespace RegularityStructures.Phi43

open RegularityStructures

private theorem pairing_size_neg_le (w : SpaceTime) :
    torusParabolicSize (-w) ≤ 2 * torusParabolicSize w := by
  unfold torusParabolicSize
  change √|(-w.1)| + torusSpatialNorm (-w.2) ≤ 2 * (√|w.1| + torusSpatialNorm w.2)
  rw [abs_neg]
  have := torusSpatialNorm_neg_le w.2
  have := Real.sqrt_nonneg |w.1|
  have := torusSpatialNorm_nonneg w.2
  linarith

private theorem pairing_reflect {F : SpaceTime → ℝ} {B a : ℝ} (hB : 0 ≤ B) (ha : 0 ≤ a)
    (hF : ∀ v, 0 < torusParabolicSize v → |F v| ≤ B * torusParabolicSize v ^ (-a)) :
    ∀ w, 0 < torusParabolicSize w →
      |F (-w)| ≤ 2 ^ a * B * torusParabolicSize w ^ (-a) := by
  intro w hw
  have h2 : torusParabolicSize w ≤ 2 * torusParabolicSize (-w) := by
    simpa using pairing_size_neg_le (-w)
  have hw' : 0 < torusParabolicSize (-w) := by linarith
  have h3 : torusParabolicSize (-w) ^ (-a) ≤ 2 ^ a * torusParabolicSize w ^ (-a) := by
    have h4 : torusParabolicSize w / 2 ≤ torusParabolicSize (-w) := by linarith
    have h5 : torusParabolicSize (-w) ^ (-a) ≤ (torusParabolicSize w / 2) ^ (-a) :=
      Real.rpow_le_rpow_of_nonpos (by linarith) h4 (by linarith)
    have h6 : (torusParabolicSize w / 2) ^ (-a) = 2 ^ a * torusParabolicSize w ^ (-a) := by
      rw [Real.div_rpow hw.le (by norm_num), Real.rpow_neg hw.le,
        Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2), div_inv_eq_mul, mul_comm]
    exact h5.trans h6.le
  calc |F (-w)| ≤ B * torusParabolicSize (-w) ^ (-a) := hF _ hw'
    _ ≤ B * (2 ^ a * torusParabolicSize w ^ (-a)) := mul_le_mul_of_nonneg_left h3 hB
    _ = 2 ^ a * B * torusParabolicSize w ^ (-a) := by ring

/-- **Pairing of two singular kernels.** -/
theorem abs_integral_shift_mul_singular_le {a b : ℝ} (ha : 0 < a) (ha5 : a < 5) (hb : 0 < b)
    (hb5 : b < 5) (hab : 5 < a + b) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {f g : SpaceTime → ℝ} {B₁ B₂ : ℝ}, 0 ≤ B₁ → 0 ≤ B₂ →
      (∀ w, 0 < torusParabolicSize w → |f w| ≤ B₁ * torusParabolicSize w ^ (-a)) →
      (∀ w, 0 < torusParabolicSize w → |g w| ≤ B₂ * torusParabolicSize w ^ (-b)) →
      ∀ x, 0 < torusParabolicSize x →
        |∫ w, f (x + w) * g w| ≤ C * B₁ * B₂ * torusParabolicSize x ^ (5 - a - b) := by
  obtain ⟨Cc, hCc, hconv⟩ := abs_integral_mul_singular_le_of_gt ha ha5 hb hb5 hab
  refine ⟨Cc * 2 ^ b, by positivity, ?_⟩
  intro f g B₁ B₂ hB₁ hB₂ hf hg x hx
  have hgr := pairing_reflect hB₂ hb.le hg
  have t := hconv (f := f) (g := fun w => g (-w)) hB₁ (mul_nonneg (by positivity) hB₂) hf hgr x hx
  have hrefl : ∫ w, |f (x + w) * g w| = ∫ w, |f (x - w)| * |g (-w)| := by
    rw [← integral_comp_sub_left_spaceTime (fun w => |f (x + w) * g w|) 0]
    refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
    simp [sub_eq_add_neg, abs_mul]
  have hn : |∫ w, f (x + w) * g w| ≤ ∫ w, |f (x - w)| * |g (-w)| := by
    rw [← hrefl]
    simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun w => f (x + w) * g w)
  refine hn.trans (t.trans (le_of_eq ?_))
  ring

end RegularityStructures.Phi43

end
