/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3Psi2DiagramLeaves
public import Phi43.BPHZ.TreeI3PsiChainBasic

/-!
# Pointwise majorants for the diagrams of `I(Ψ³)Ψ²`

Bounds of the covariance entries by centred powers, `|Q(c - w)| ≤ B s(c - w)^(-1)`, its square
(with and without a loss `δ` of the exponent, the latter on the slab `|t| ≤ 4`), and the time
slab on which the recentred kernel `δK(z, ·)` lives.
-/

public section

open MeasureTheory

namespace RegularityStructures

/-- If `s(z) ≤ 1` then `|z.1| ≤ 1`. -/
theorem abs_fst_le_one_of_size_le_one {z : SpaceTime} (hz : torusParabolicSize z ≤ 1) :
    |z.1| ≤ 1 := by
  have h1 : √|z.1| ≤ 1 := by
    have := torusSpatialNorm_nonneg z.2
    unfold torusParabolicSize at hz
    linarith
  have := Real.sqrt_le_iff.1 h1
  linarith [this.2]

/-- `|Q(c - w)| ≤ B s(c - w)^(-1)`. -/
theorem abs_Q_le_singularPow {Q : SpaceTime → ℝ} {B : ℝ}
    (hQ : ∀ x, 0 < torusParabolicSize x → |Q x| ≤ B * torusParabolicSize x ^ (-(1 : ℝ)))
    {c w : SpaceTime} (h : 0 < torusParabolicSize (c - w)) :
    |Q (c - w)| ≤ B * singularPow 1 c w :=
  hQ _ h

/-- `|Q(c - w)|² ≤ B² s(c - w)^(-2)`. -/
theorem abs_Q_sq_le_singularPow {Q : SpaceTime → ℝ} {B : ℝ}
    (hQ : ∀ x, 0 < torusParabolicSize x → |Q x| ≤ B * torusParabolicSize x ^ (-(1 : ℝ)))
    {c w : SpaceTime} (h : 0 < torusParabolicSize (c - w)) :
    |Q (c - w)| ^ 2 ≤ B ^ 2 * singularPow 2 c w := by
  have h1 := abs_Q_le_singularPow hQ h
  have hsq : |Q (c - w)| ^ 2 ≤ (B * singularPow 1 c w) ^ 2 :=
    pow_le_pow_left₀ (abs_nonneg _) h1 2
  refine hsq.trans (le_of_eq ?_)
  unfold singularPow
  rw [mul_pow, ← Real.rpow_natCast (torusParabolicSize (c - w) ^ (-(1 : ℝ))) 2,
    ← Real.rpow_mul (torusParabolicSize_nonneg _)]
  norm_num

/-- `|Q(c - w)|² ≤ B² 3^δ s(c - w)^(-(2+δ))` on the slab `|t| ≤ 4`. -/
theorem abs_Q_sq_le_singularPow_loss {Q : SpaceTime → ℝ} {B δ : ℝ} (hδ : 0 ≤ δ)
    (hQ : ∀ x, 0 < torusParabolicSize x → |Q x| ≤ B * torusParabolicSize x ^ (-(1 : ℝ)))
    {c w : SpaceTime} (h : 0 < torusParabolicSize (c - w)) (h4 : |(c - w).1| ≤ 4) :
    |Q (c - w)| ^ 2 ≤ B ^ 2 * 3 ^ δ * singularPow (2 + δ) c w :=
  abs_Q_sq_le_of_abs_le_four hδ hQ h h4

/-- The time coordinate of `c - w` is at most `3` when `|c.1| ≤ 1` and `|w.1| ≤ 2`. -/
theorem abs_sub_fst_le_four {c w : SpaceTime} (hc : |c.1| ≤ 1) (hw : |w.1| ≤ 2) :
    |(c - w).1| ≤ 4 := by
  have : (c - w).1 = c.1 - w.1 := rfl
  rw [this]
  exact (abs_sub _ _).trans (by linarith)

/-- Evenness turns `Q(w - c)` into `Q(c - w)`. -/
theorem Q_sub_comm {Q : SpaceTime → ℝ} (hQe : ∀ x, Q (-x) = Q x) (a b : SpaceTime) :
    Q (a - b) = Q (b - a) := by
  rw [← hQe (b - a), neg_sub]

/-- Merging two powers with the same centre, with the exponent given explicitly. -/
theorem singularPow_mul_self_eq {a b e : ℝ} (hab : a + b = e) (c w : SpaceTime)
    (h : 0 < torusParabolicSize (c - w)) :
    singularPow a c w * singularPow b c w = singularPow e c w := by
  rw [singularPow_mul_self a b c w h, hab]

/-- Almost-everywhere merging of two powers with the same centre. -/
theorem ae_singularPow_mul_self {a b e : ℝ} (hab : a + b = e) (c : SpaceTime) :
    ∀ᵐ w : SpaceTime ∂volume, singularPow a c w * singularPow b c w = singularPow e c w := by
  filter_upwards [ae_torusParabolicSize_sub_pos c] with w hw
  exact singularPow_mul_self_eq hab c w hw

/-- Flipping the centre: `s(w - c)^(-p) ≤ 2^p s(c - w)^(-p)`. -/
theorem rpow_neg_flip_singularPow {p : ℝ} (hp : 0 ≤ p) {c w : SpaceTime}
    (h : 0 < torusParabolicSize (c - w)) :
    torusParabolicSize (w - c) ^ (-p) ≤ 2 ^ p * singularPow p c w :=
  torusParabolicSize_rpow_neg_flip_le' hp h

end RegularityStructures

end
