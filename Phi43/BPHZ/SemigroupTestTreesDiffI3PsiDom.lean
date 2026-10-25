/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestTreesI3PsiChain
public import Phi43.BPHZ.TreeI3PsiDiagramMultiPointwise

/-!
# Global chain domination for the cross-mollifier difference of `I(Ψ³)Ψ`

Global versions of `abs_dK_dK_chain_le`, `abs_dK_dK_chain_flip_le` and
`abs_dK_dK_chain_flip_left_le`: the hypotheses `s(z), s(z') ≤ 1` (which are used only to restrict
to the slab `|w.1| ≤ 2` carrying the support of the recentred kernel `K(z - ·) - K(-·)` and to
bound `s(w - v) ≤ 3` there) are replaced by an explicit bound `s(w - v) ≤ D` on the slab
`|w.1| ≤ |z.1| + 1`, `|v.1| ≤ |z'.1| + 1`, and `3 ^ δ` by `D ^ δ`.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

/-- **Global chain domination.** -/
theorem abs_dK_dK_chain_le_global_i3Psi {K : SpaceTime → ℝ} {B δ α β₀ γ D : ℝ} (hB : 0 ≤ B)
    (hδ : 0 ≤ δ) (hγ : 0 ≤ γ) (hD0 : 0 ≤ D)
    (hK : ∀ x, 0 < torusParabolicSize x → |K x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ)))
    (hKs : ∀ x : SpaceTime, 1 < |x.1| → K x = 0) {z z' u u' w v : SpaceTime}
    (hD : ∀ w v : SpaceTime, |w.1| ≤ |z.1| + 1 → |v.1| ≤ |z'.1| + 1 →
      torusParabolicSize (w - v) ≤ D)
    (h1 : 0 < torusParabolicSize (z - w)) (h0 : 0 < torusParabolicSize (0 - w))
    (h1' : 0 < torusParabolicSize (z' - v)) (h0' : 0 < torusParabolicSize (0 - v))
    (hu' : 0 < torusParabolicSize (u' - v)) (hwv : 0 < torusParabolicSize (w - v)) :
    |K (z - w) - K (-w)| * |K (z' - v) - K (-v)| *
        (singularPow (1 + α) u w * torusParabolicSize (w - v) ^ (-(2 + β₀)) *
          singularPow (1 + γ) u' v) ≤
      B ^ 2 * D ^ δ * i3PsiChainMajorant α (β₀ + δ) γ z z' u u' w v := by
  have n3 : (0 : ℝ) ≤ D ^ δ := Real.rpow_nonneg hD0 _
  have hrhs := i3PsiChainMajorant_nonneg α (β₀ + δ) γ z z' u u' w v
  have hrhs' : 0 ≤ B ^ 2 * D ^ δ * i3PsiChainMajorant α (β₀ + δ) γ z z' u u' w v :=
    mul_nonneg (mul_nonneg (sq_nonneg B) n3) hrhs
  by_cases hw : |w.1| ≤ |z.1| + 1
  · by_cases hv : |v.1| ≤ |z'.1| + 1
    · have a := abs_dK_le hK h1 h0
      have b := abs_dK_le hK h1' h0'
      have e1 := singularPow_mul_le (a := 3) (b := 1 + γ) (by norm_num) (by linarith) h1' hu'
      have e2 := singularPow_mul_le (a := 3) (b := 1 + γ) (by norm_num) (by linarith) h0' hu'
      have e : (3 : ℝ) + (1 + γ) = 4 + γ := by ring
      rw [e] at e1 e2
      have nσ := singularPow_nonneg (1 + α) u w
      have nσ' := singularPow_nonneg (1 + γ) u' v
      have hL : |K (z - w) - K (-w)| * singularPow (1 + α) u w ≤
          B * ((singularPow 3 z w + singularPow 3 0 w) * singularPow (1 + α) u w) := by
        have := mul_le_mul_of_nonneg_right a nσ
        linarith
      have hR : |K (z' - v) - K (-v)| * singularPow (1 + γ) u' v ≤
          B * (singularPow (4 + γ) z' v + singularPow (4 + γ) 0 v +
            2 * singularPow (4 + γ) u' v) := by
        have := mul_le_mul_of_nonneg_right b nσ'
        have h5 : B * (singularPow 3 z' v + singularPow 3 0 v) * singularPow (1 + γ) u' v ≤
            B * (singularPow (4 + γ) z' v + singularPow (4 + γ) 0 v +
              2 * singularPow (4 + γ) u' v) := by
          have := mul_le_mul_of_nonneg_left (add_le_add e1 e2) hB
          nlinarith [this]
        linarith
      have hC : torusParabolicSize (w - v) ^ (-(2 + β₀)) ≤
          D ^ δ * singularPow (2 + (β₀ + δ)) w v := by
        have hpow : torusParabolicSize (w - v) ^ (-(2 + β₀)) =
            torusParabolicSize (w - v) ^ δ * singularPow (2 + (β₀ + δ)) w v := by
          unfold singularPow
          rw [← Real.rpow_add hwv]; congr 1; ring
        rw [hpow]
        exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hwv.le (hD w v hw hv) hδ)
          (singularPow_nonneg _ _ _)
      have nLeft : 0 ≤ B * ((singularPow 3 z w + singularPow 3 0 w) * singularPow (1 + α) u w) :=
        mul_nonneg hB (mul_nonneg (add_nonneg (singularPow_nonneg _ _ _)
          (singularPow_nonneg _ _ _)) nσ)
      have nRight : 0 ≤ B * (singularPow (4 + γ) z' v + singularPow (4 + γ) 0 v +
          2 * singularPow (4 + γ) u' v) :=
        mul_nonneg hB (add_nonneg (add_nonneg (singularPow_nonneg _ _ _)
          (singularPow_nonneg _ _ _)) (mul_nonneg (by norm_num) (singularPow_nonneg _ _ _)))
      have key : (|K (z - w) - K (-w)| * singularPow (1 + α) u w) *
          (|K (z' - v) - K (-v)| * singularPow (1 + γ) u' v) *
          torusParabolicSize (w - v) ^ (-(2 + β₀)) ≤
          (B * ((singularPow 3 z w + singularPow 3 0 w) * singularPow (1 + α) u w)) *
          (B * (singularPow (4 + γ) z' v + singularPow (4 + γ) 0 v +
            2 * singularPow (4 + γ) u' v)) * (D ^ δ * singularPow (2 + (β₀ + δ)) w v) :=
        mul_le_mul (mul_le_mul hL hR (mul_nonneg (abs_nonneg _) nσ') nLeft) hC
          (Real.rpow_nonneg (torusParabolicSize_nonneg _) _) (mul_nonneg nLeft nRight)
      refine le_trans (le_of_eq ?_) (key.trans (le_of_eq ?_))
      · ring
      · unfold i3PsiChainMajorant
        ring
    · have : K (z' - v) - K (-v) = 0 := dK_eq_zero_of_abs_lt hKs (not_le.1 hv)
      rw [this, abs_zero]
      simpa using hrhs'
  · have : K (z - w) - K (-w) = 0 := dK_eq_zero_of_abs_lt hKs (not_le.1 hw)
    rw [this, abs_zero]
    simpa using hrhs'

/-- **Global chain domination, weights `s(w - u)^(-a) s(w - v)^(-b) s(v - u')^(-c)`.** -/
theorem abs_dK_dK_chain_flip_le_global_i3Psi {K : SpaceTime → ℝ} {B δ α β₀ β γ a b c D : ℝ}
    (hB : 0 ≤ B) (hδ : 0 ≤ δ) (hα : 0 ≤ α) (hα1 : α ≤ 1) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hD0 : 0 ≤ D) (ha : a = 1 + α) (hb : b = 2 + β₀) (hβ : β = β₀ + δ) (hc : c = 1 + γ)
    (hK : ∀ x, 0 < torusParabolicSize x → |K x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ)))
    (hKs : ∀ x : SpaceTime, 1 < |x.1| → K x = 0) {z z' u u' w v : SpaceTime}
    (hD : ∀ w v : SpaceTime, |w.1| ≤ |z.1| + 1 → |v.1| ≤ |z'.1| + 1 →
      torusParabolicSize (w - v) ≤ D)
    (h1 : 0 < torusParabolicSize (z - w)) (h0 : 0 < torusParabolicSize (0 - w))
    (hu : 0 < torusParabolicSize (u - w))
    (h1' : 0 < torusParabolicSize (z' - v)) (h0' : 0 < torusParabolicSize (0 - v))
    (hu' : 0 < torusParabolicSize (u' - v)) (hwv : 0 < torusParabolicSize (w - v)) :
    |K (z - w) - K (-w)| * |K (z' - v) - K (-v)| *
        (torusParabolicSize (w - u) ^ (-a) * torusParabolicSize (w - v) ^ (-b) *
          torusParabolicSize (v - u') ^ (-c)) ≤
      16 * B ^ 2 * D ^ δ * i3PsiChainMajorant α β γ z z' u u' w v := by
  subst ha hb hβ hc
  have key := abs_dK_dK_chain_le_global_i3Psi (α := α) (β₀ := β₀) (γ := γ) (u := u) (u' := u') hB hδ hγ
    hD0 hK hKs hD h1 h0 h1' h0' hu' hwv
  have f1 := singularPow_flip_le (a := 1 + α) (by linarith) (by linarith) hu
  have f2 := singularPow_flip_le (a := 1 + γ) (by linarith) (by linarith) hu'
  have n1 := singularPow_nonneg (1 + α) u w
  have n2 := singularPow_nonneg (1 + γ) u' v
  have n3 : 0 ≤ torusParabolicSize (w - v) ^ (-(2 + β₀)) :=
    Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have nK : 0 ≤ |K (z - w) - K (-w)| * |K (z' - v) - K (-v)| :=
    mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hw : torusParabolicSize (w - u) ^ (-(1 + α)) * torusParabolicSize (w - v) ^ (-(2 + β₀)) *
      torusParabolicSize (v - u') ^ (-(1 + γ)) ≤
      16 * (singularPow (1 + α) u w * torusParabolicSize (w - v) ^ (-(2 + β₀)) *
        singularPow (1 + γ) u' v) := by
    have := mul_le_mul (mul_le_mul_of_nonneg_right f1 n3) f2
      (Real.rpow_nonneg (torusParabolicSize_nonneg _) _) (mul_nonneg (by positivity) n3)
    refine this.trans (le_of_eq ?_)
    ring
  calc _ ≤ |K (z - w) - K (-w)| * |K (z' - v) - K (-v)| *
        (16 * (singularPow (1 + α) u w * torusParabolicSize (w - v) ^ (-(2 + β₀)) *
          singularPow (1 + γ) u' v)) := mul_le_mul_of_nonneg_left hw nK
    _ = 16 * (|K (z - w) - K (-w)| * |K (z' - v) - K (-v)| *
        (singularPow (1 + α) u w * torusParabolicSize (w - v) ^ (-(2 + β₀)) *
          singularPow (1 + γ) u' v)) := by ring
    _ ≤ 16 * (B ^ 2 * D ^ δ * i3PsiChainMajorant α (β₀ + δ) γ z z' u u' w v) :=
        mul_le_mul_of_nonneg_left key (by norm_num)
    _ = _ := by ring

/-- **Global chain domination, weights `s(w - u)^(-a) s(w - v)^(-b) s(u' - v)^(-c)`.** -/
theorem abs_dK_dK_chain_flip_left_le_global_i3Psi {K : SpaceTime → ℝ} {B δ α β₀ β γ a b c D : ℝ}
    (hB : 0 ≤ B) (hδ : 0 ≤ δ) (hα : 0 ≤ α) (hα1 : α ≤ 1) (hγ : 0 ≤ γ) (hD0 : 0 ≤ D)
    (ha : a = 1 + α) (hb : b = 2 + β₀) (hβ : β = β₀ + δ) (hc : c = 1 + γ)
    (hK : ∀ x, 0 < torusParabolicSize x → |K x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ)))
    (hKs : ∀ x : SpaceTime, 1 < |x.1| → K x = 0) {z z' u u' w v : SpaceTime}
    (hD : ∀ w v : SpaceTime, |w.1| ≤ |z.1| + 1 → |v.1| ≤ |z'.1| + 1 →
      torusParabolicSize (w - v) ≤ D)
    (h1 : 0 < torusParabolicSize (z - w)) (h0 : 0 < torusParabolicSize (0 - w))
    (hu : 0 < torusParabolicSize (u - w))
    (h1' : 0 < torusParabolicSize (z' - v)) (h0' : 0 < torusParabolicSize (0 - v))
    (hu' : 0 < torusParabolicSize (u' - v)) (hwv : 0 < torusParabolicSize (w - v)) :
    |K (z - w) - K (-w)| * |K (z' - v) - K (-v)| *
        (torusParabolicSize (w - u) ^ (-a) * torusParabolicSize (w - v) ^ (-b) *
          torusParabolicSize (u' - v) ^ (-c)) ≤
      4 * B ^ 2 * D ^ δ * i3PsiChainMajorant α β γ z z' u u' w v := by
  subst ha hb hβ hc
  have key := abs_dK_dK_chain_le_global_i3Psi (α := α) (β₀ := β₀) (γ := γ) (u := u) (u' := u') hB hδ hγ
    hD0 hK hKs hD h1 h0 h1' h0' hu' hwv
  have f1 := singularPow_flip_le (a := 1 + α) (by linarith) (by linarith) hu
  have n1 := singularPow_nonneg (1 + α) u w
  have n2 := singularPow_nonneg (1 + γ) u' v
  have n3 : 0 ≤ torusParabolicSize (w - v) ^ (-(2 + β₀)) :=
    Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have nK : 0 ≤ |K (z - w) - K (-w)| * |K (z' - v) - K (-v)| :=
    mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hw : torusParabolicSize (w - u) ^ (-(1 + α)) * torusParabolicSize (w - v) ^ (-(2 + β₀)) *
      torusParabolicSize (u' - v) ^ (-(1 + γ)) ≤
      4 * (singularPow (1 + α) u w * torusParabolicSize (w - v) ^ (-(2 + β₀)) *
        singularPow (1 + γ) u' v) := by
    have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right f1 n3) n2
    refine this.trans (le_of_eq ?_)
    unfold singularPow
    ring
  calc _ ≤ |K (z - w) - K (-w)| * |K (z' - v) - K (-v)| *
        (4 * (singularPow (1 + α) u w * torusParabolicSize (w - v) ^ (-(2 + β₀)) *
          singularPow (1 + γ) u' v)) := mul_le_mul_of_nonneg_left hw nK
    _ = 4 * (|K (z - w) - K (-w)| * |K (z' - v) - K (-v)| *
        (singularPow (1 + α) u w * torusParabolicSize (w - v) ^ (-(2 + β₀)) *
          singularPow (1 + γ) u' v)) := by ring
    _ ≤ 4 * (B ^ 2 * D ^ δ * i3PsiChainMajorant α (β₀ + δ) γ z z' u u' w v) :=
        mul_le_mul_of_nonneg_left key (by norm_num)
    _ = _ := by ring

end RegularityStructures

end
