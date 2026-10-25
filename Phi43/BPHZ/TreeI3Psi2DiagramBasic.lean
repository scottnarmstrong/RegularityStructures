/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3Psi2DiagramDefs
public import Phi43.BPHZ.TreeI3PsiPointwise
public import Phi43.BPHZ.TreeI3PsiSigma
public import Phi43.BPHZ.TreeI3PsiDiagramUniform

/-!
# Basic facts for the diagrams of `I(Ψ³)Ψ²`

* evenness of `Q` when `Q(x) = ∫ J(x + w) J(w) dw`;
* the covariance with a loss `δ` of the exponent, `|Q x| ≤ B 3^δ s(x)^(-(1+δ))`
  (on the slab `|t| ≤ 4`, no support hypothesis on `Q`);
* the flip `s(b - a)^(-p) ≤ 2^p s(a - b)^(-p)` of a centred power.
-/

public section

open MeasureTheory

namespace RegularityStructures

/-- If `Q(x) = ∫ J(x + w) J(w) dw` then `Q` is even. -/
theorem i3Psi2_Q_neg {J Q : SpaceTime → ℝ} (hQJ : ∀ x, Q x = ∫ w, J (x + w) * J w) (x : SpaceTime) :
    Q (-x) = Q x := by
  rw [hQJ, hQJ]
  have h := integral_add_right_eq_self (μ := (volume : Measure SpaceTime))
    (fun w => J (-x + w) * J w) x
  rw [← h]
  refine integral_congr_ae (Filter.Eventually.of_forall fun w => ?_)
  have e : -x + (w + x) = w := by abel
  show J (-x + (w + x)) * J (w + x) = J (x + w) * J w
  rw [e, add_comm w x, mul_comm]

/-- The covariance with a loss `δ` of the exponent, on the slab `|t| ≤ 4`. -/
theorem abs_Q_le_lower {Q : SpaceTime → ℝ} {B δ : ℝ} (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hQ : ∀ x, 0 < torusParabolicSize x → |Q x| ≤ B * torusParabolicSize x ^ (-(1 : ℝ)))
    {x : SpaceTime} (hx : 0 < torusParabolicSize x) (hx4 : |x.1| ≤ 4) :
    |Q x| ≤ B * 3 ^ δ * torusParabolicSize x ^ (-(1 + δ)) := by
  have h3 := torusParabolicSize_le_three_of_abs_le_four hx4
  have hpow : torusParabolicSize x ^ (-(1 : ℝ)) =
      torusParabolicSize x ^ δ * torusParabolicSize x ^ (-(1 + δ)) := by
    rw [← Real.rpow_add hx]; congr 1; ring
  have hle : torusParabolicSize x ^ δ ≤ 3 ^ δ := Real.rpow_le_rpow hx.le h3 hδ
  have hnn : 0 ≤ torusParabolicSize x ^ (-(1 + δ)) := Real.rpow_nonneg hx.le _
  calc |Q x| ≤ B * torusParabolicSize x ^ (-(1 : ℝ)) := hQ x hx
    _ = B * (torusParabolicSize x ^ δ * torusParabolicSize x ^ (-(1 + δ))) := by rw [hpow]
    _ ≤ B * (3 ^ δ * torusParabolicSize x ^ (-(1 + δ))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hle hnn) hB
    _ = _ := by ring

/-- Flipping the argument of a centred power costs a factor `2^p`. -/
theorem torusParabolicSize_rpow_neg_flip_le' {p : ℝ} (hp : 0 ≤ p) {a b : SpaceTime}
    (h : 0 < torusParabolicSize (a - b)) :
    torusParabolicSize (b - a) ^ (-p) ≤ 2 ^ p * torusParabolicSize (a - b) ^ (-p) := by
  have hneg := torusParabolicSize_neg_le_two_mul (b - a)
  rw [neg_sub] at hneg
  have hy : 0 < torusParabolicSize (a - b) / 2 := by linarith
  have h1 : torusParabolicSize (b - a) ^ (-p) ≤ (torusParabolicSize (a - b) / 2) ^ (-p) :=
    Real.rpow_le_rpow_of_nonpos hy (by linarith) (neg_nonpos.2 hp)
  have h2 : (torusParabolicSize (a - b) / 2) ^ (-p) = 2 ^ p * torusParabolicSize (a - b) ^ (-p) := by
    rw [Real.div_rpow h.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_neg h.le]
    field_simp
  exact h1.trans h2.le

/-- Two centred powers with the same centre merge. -/
theorem singularPow_mul_self (a b : ℝ) (c w : SpaceTime) (h : 0 < torusParabolicSize (c - w)) :
    singularPow a c w * singularPow b c w = singularPow (a + b) c w := by
  unfold singularPow
  rw [← Real.rpow_add h]
  congr 1; ring

end RegularityStructures

end
