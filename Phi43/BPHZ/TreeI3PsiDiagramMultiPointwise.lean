/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3PsiDiagramMultiChain
public import Phi43.BPHZ.TreeI3PsiDiagramMultiPrincipal
public import Phi43.BPHZ.TreeI3PsiDiagramSlab

/-!
# Pointwise domination by the chain and principal majorants

For the kernel `K` of order `-3`, supported in `|t| ≤ 1`, and `s(z), s(z') ≤ 1`:

* `abs_dK_dK_chain_le`: `|δK(z,w)| |δK(z',v)| · s_{1+α}(u,w) s(w-v)^(-(2+β₀)) s_{1+γ}(u',v)` is bounded
  by `B² 3^δ` times `i3PsiChainMajorant α (β₀ + δ) γ`;
* `abs_dK_dK_principal_le`: `|δK(z,w)| |δK(z',v)| · s_{3+τ}(w,v)` is bounded by
  `12 B² s(z')^θ` times `i3PsiPrincipalMajorant θ τ`.

`singularPow_flip_le` converts `s(w - u)^(-a)` to the centred power `s_a(u, w)`.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

/-- Flipping the argument of `s^(-a)`, `0 ≤ a ≤ 2`, costs a factor at most `4`. -/
theorem singularPow_flip_le {a : ℝ} (ha0 : 0 ≤ a) (ha2 : a ≤ 2) {u w : SpaceTime}
    (h : 0 < torusParabolicSize (u - w)) :
    torusParabolicSize (w - u) ^ (-a) ≤ 4 * singularPow a u w := by
  have hneg := torusParabolicSize_neg_le_two_mul (w - u)
  rw [neg_sub] at hneg
  have hy : 0 < torusParabolicSize (u - w) / 2 := by linarith
  have h1 : torusParabolicSize (w - u) ^ (-a) ≤ (torusParabolicSize (u - w) / 2) ^ (-a) :=
    Real.rpow_le_rpow_of_nonpos hy (by linarith) (neg_nonpos.2 ha0)
  have h2 : (torusParabolicSize (u - w) / 2) ^ (-a) =
      2 ^ a * torusParabolicSize (u - w) ^ (-a) := by
    rw [Real.div_rpow h.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
      Real.rpow_neg h.le]
    field_simp
  have h3 : (2 : ℝ) ^ a ≤ 4 := by
    calc (2 : ℝ) ^ a ≤ 2 ^ (2 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by norm_num) ha2
      _ = 4 := by rw [Real.rpow_two]; norm_num
  have h4 : 0 ≤ torusParabolicSize (u - w) ^ (-a) := Real.rpow_nonneg h.le _
  calc _ ≤ _ := h1
    _ = _ := h2
    _ ≤ 4 * torusParabolicSize (u - w) ^ (-a) := mul_le_mul_of_nonneg_right h3 h4
    _ = 4 * singularPow a u w := rfl

theorem i3PsiChainMajorant_nonneg (α β γ : ℝ) (z z' u u' w v : SpaceTime) :
    0 ≤ i3PsiChainMajorant α β γ z z' u u' w v := by
  unfold i3PsiChainMajorant
  have := singularPow_nonneg
  exact mul_nonneg (mul_nonneg (add_nonneg (this _ _ _) (this _ _ _)) (this _ _ _))
    (mul_nonneg (add_nonneg (add_nonneg (this _ _ _) (this _ _ _))
      (mul_nonneg (by norm_num) (this _ _ _))) (this _ _ _))

theorem i3PsiPrincipalMajorant_nonneg (θ τ : ℝ) (z z' w v : SpaceTime) :
    0 ≤ i3PsiPrincipalMajorant θ τ z z' w v := by
  unfold i3PsiPrincipalMajorant
  have := singularPow_nonneg
  exact mul_nonneg (Set.indicator_nonneg (fun w _ => add_nonneg (this _ _ _) (this _ _ _)) w)
    (mul_nonneg (add_nonneg (this _ _ _) (this _ _ _)) (this _ _ _))

/-- **Chain domination.** -/
theorem abs_dK_dK_chain_le {K : SpaceTime → ℝ} {B δ α β₀ γ : ℝ} (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hγ : 0 ≤ γ)
    (hK : ∀ x, 0 < torusParabolicSize x → |K x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ)))
    (hKs : ∀ x : SpaceTime, 1 < |x.1| → K x = 0) {z z' u u' w v : SpaceTime}
    (hz1 : torusParabolicSize z ≤ 1) (hz1' : torusParabolicSize z' ≤ 1)
    (h1 : 0 < torusParabolicSize (z - w)) (h0 : 0 < torusParabolicSize (0 - w))
    (h1' : 0 < torusParabolicSize (z' - v)) (h0' : 0 < torusParabolicSize (0 - v))
    (hu' : 0 < torusParabolicSize (u' - v)) (hwv : 0 < torusParabolicSize (w - v)) :
    |K (z - w) - K (-w)| * |K (z' - v) - K (-v)| *
        (singularPow (1 + α) u w * torusParabolicSize (w - v) ^ (-(2 + β₀)) *
          singularPow (1 + γ) u' v) ≤
      B ^ 2 * 3 ^ δ * i3PsiChainMajorant α (β₀ + δ) γ z z' u u' w v := by
  have n3 : (0 : ℝ) ≤ 3 ^ δ := Real.rpow_nonneg (by norm_num) _
  have hrhs := i3PsiChainMajorant_nonneg α (β₀ + δ) γ z z' u u' w v
  have hrhs' : 0 ≤ B ^ 2 * 3 ^ δ * i3PsiChainMajorant α (β₀ + δ) γ z z' u u' w v :=
    mul_nonneg (mul_nonneg (sq_nonneg B) n3) hrhs
  by_cases hw : |w.1| ≤ 2
  · by_cases hv : |v.1| ≤ 2
    · have hwv4 : |(w - v).1| ≤ 4 := by
        have : (w - v).1 = w.1 - v.1 := rfl
        rw [this]
        exact (abs_sub _ _).trans (by linarith)
      have h3 := torusParabolicSize_le_three_of_abs_le_four hwv4
      have a := abs_dK_le hK h1 h0
      have b := abs_dK_le hK h1' h0'
      have e1 := singularPow_mul_le (a := 3) (b := 1 + γ) (by norm_num) (by linarith) h1' hu'
      have e2 := singularPow_mul_le (a := 3) (b := 1 + γ) (by norm_num) (by linarith) h0' hu'
      have e : (3 : ℝ) + (1 + γ) = 4 + γ := by ring
      rw [e] at e1 e2
      have nσ := singularPow_nonneg (1 + α) u w
      have nσ' := singularPow_nonneg (1 + γ) u' v
      -- left and right factors
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
          linarith [this]
        linarith
      have hC : torusParabolicSize (w - v) ^ (-(2 + β₀)) ≤
          3 ^ δ * singularPow (2 + (β₀ + δ)) w v := by
        have hpow : torusParabolicSize (w - v) ^ (-(2 + β₀)) =
            torusParabolicSize (w - v) ^ δ * singularPow (2 + (β₀ + δ)) w v := by
          unfold singularPow
          rw [← Real.rpow_add hwv]; congr 1; ring
        rw [hpow]
        exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow hwv.le h3 hδ) (singularPow_nonneg _ _ _)
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
            2 * singularPow (4 + γ) u' v)) * (3 ^ δ * singularPow (2 + (β₀ + δ)) w v) :=
        mul_le_mul (mul_le_mul hL hR (mul_nonneg (abs_nonneg _) nσ') nLeft) hC
          (Real.rpow_nonneg (torusParabolicSize_nonneg _) _) (mul_nonneg nLeft nRight)
      refine le_trans (le_of_eq ?_) (key.trans (le_of_eq ?_))
      · ring
      · unfold i3PsiChainMajorant
        ring
    · have : K (z' - v) - K (-v) = 0 := dK_eq_zero_of_two_lt hKs hz1' (not_le.1 hv)
      rw [this, abs_zero]
      simpa using hrhs'
  · have : K (z - w) - K (-w) = 0 := dK_eq_zero_of_two_lt hKs hz1 (not_le.1 hw)
    rw [this, abs_zero]
    simpa using hrhs'

/-- **Principal domination.** -/
theorem abs_dK_dK_principal_le {K : SpaceTime → ℝ} {B θ τ : ℝ} (hB : 0 ≤ B) (hθ0 : 0 ≤ θ)
    (hθ1 : θ ≤ 1)
    (hK : ∀ x, 0 < torusParabolicSize x → |K x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ)))
    (hinc : ∀ u h : SpaceTime, 0 < torusParabolicSize u →
      torusParabolicSize h ≤ torusParabolicSize u / 2 →
        |K (u + h) - K u| ≤ B * torusParabolicSize h * torusParabolicSize u ^ (-(4 : ℝ)))
    (hKs : ∀ x : SpaceTime, 1 < |x.1| → K x = 0) {z z' w v : SpaceTime}
    (hz1 : torusParabolicSize z ≤ 1)
    (h1 : 0 < torusParabolicSize (z - w)) (h0 : 0 < torusParabolicSize (0 - w))
    (h1' : 0 < torusParabolicSize (z' - v)) (h0' : 0 < torusParabolicSize (0 - v)) :
    |K (z - w) - K (-w)| * |K (z' - v) - K (-v)| * singularPow (3 + τ) w v ≤
      12 * B ^ 2 * torusParabolicSize z' ^ θ * i3PsiPrincipalMajorant θ τ z z' w v := by
  have hP : 0 ≤ torusParabolicSize z' ^ θ := Real.rpow_nonneg (torusParabolicSize_nonneg _) _
  have hrhs := i3PsiPrincipalMajorant_nonneg θ τ z z' w v
  have hrhs' : 0 ≤ 12 * B ^ 2 * torusParabolicSize z' ^ θ *
      i3PsiPrincipalMajorant θ τ z z' w v := mul_nonneg (by positivity) hrhs
  by_cases hw : |w.1| ≤ 2
  · have a := abs_dK_le hK h1 h0
    have b := abs_dK_le_holder hB hθ0 hθ1 hK hinc h1' h0'
    have nm := singularPow_nonneg (3 + τ) w v
    have nb : 0 ≤ 12 * B * torusParabolicSize z' ^ θ *
        (singularPow (3 + θ) z' v + singularPow (3 + θ) 0 v) :=
      mul_nonneg (by positivity) (add_nonneg (singularPow_nonneg _ _ _) (singularPow_nonneg _ _ _))
    have na : 0 ≤ B * (singularPow 3 z w + singularPow 3 0 w) :=
      mul_nonneg hB (add_nonneg (singularPow_nonneg _ _ _) (singularPow_nonneg _ _ _))
    have key : |K (z - w) - K (-w)| * |K (z' - v) - K (-v)| * singularPow (3 + τ) w v ≤
        (B * (singularPow 3 z w + singularPow 3 0 w)) *
          (12 * B * torusParabolicSize z' ^ θ *
            (singularPow (3 + θ) z' v + singularPow (3 + θ) 0 v)) * singularPow (3 + τ) w v :=
      mul_le_mul_of_nonneg_right (mul_le_mul a b (abs_nonneg _) na) nm
    refine key.trans (le_of_eq ?_)
    unfold i3PsiPrincipalMajorant
    rw [Set.indicator_of_mem (show w ∈ {w : SpaceTime | |w.1| ≤ 2} from hw)]
    ring
  · have : K (z - w) - K (-w) = 0 := dK_eq_zero_of_two_lt hKs hz1 (not_le.1 hw)
    rw [this, abs_zero]
    simpa using hrhs'

/-- **Chain domination, weights `s(w - u)^(-a) s(w - v)^(-b) s(v - u')^(-c)`.** -/
theorem abs_dK_dK_chain_flip_le {K : SpaceTime → ℝ} {B δ α β₀ β γ a b c : ℝ} (hB : 0 ≤ B)
    (hδ : 0 ≤ δ) (hα : 0 ≤ α) (hα1 : α ≤ 1) (hγ : 0 ≤ γ) (hγ1 : γ ≤ 1) (ha : a = 1 + α)
    (hb : b = 2 + β₀) (hβ : β = β₀ + δ) (hc : c = 1 + γ)
    (hK : ∀ x, 0 < torusParabolicSize x → |K x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ)))
    (hKs : ∀ x : SpaceTime, 1 < |x.1| → K x = 0) {z z' u u' w v : SpaceTime}
    (hz1 : torusParabolicSize z ≤ 1) (hz1' : torusParabolicSize z' ≤ 1)
    (h1 : 0 < torusParabolicSize (z - w)) (h0 : 0 < torusParabolicSize (0 - w))
    (hu : 0 < torusParabolicSize (u - w))
    (h1' : 0 < torusParabolicSize (z' - v)) (h0' : 0 < torusParabolicSize (0 - v))
    (hu' : 0 < torusParabolicSize (u' - v)) (hwv : 0 < torusParabolicSize (w - v)) :
    |K (z - w) - K (-w)| * |K (z' - v) - K (-v)| *
        (torusParabolicSize (w - u) ^ (-a) * torusParabolicSize (w - v) ^ (-b) *
          torusParabolicSize (v - u') ^ (-c)) ≤
      16 * B ^ 2 * 3 ^ δ * i3PsiChainMajorant α β γ z z' u u' w v := by
  subst ha hb hβ hc
  have key := abs_dK_dK_chain_le (α := α) (β₀ := β₀) (γ := γ) (u := u) (u' := u') hB hδ hγ hK hKs
    hz1 hz1' h1 h0 h1' h0' hu' hwv
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
    _ ≤ 16 * (B ^ 2 * 3 ^ δ * i3PsiChainMajorant α (β₀ + δ) γ z z' u u' w v) :=
        mul_le_mul_of_nonneg_left key (by norm_num)
    _ = _ := by ring

/-- **Chain domination, weights `s(w - u)^(-a) s(w - v)^(-b) s(u' - v)^(-c)`.** -/
theorem abs_dK_dK_chain_flip_left_le {K : SpaceTime → ℝ} {B δ α β₀ β γ a b c : ℝ} (hB : 0 ≤ B)
    (hδ : 0 ≤ δ) (hα : 0 ≤ α) (hα1 : α ≤ 1) (hγ : 0 ≤ γ) (ha : a = 1 + α)
    (hb : b = 2 + β₀) (hβ : β = β₀ + δ) (hc : c = 1 + γ)
    (hK : ∀ x, 0 < torusParabolicSize x → |K x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ)))
    (hKs : ∀ x : SpaceTime, 1 < |x.1| → K x = 0) {z z' u u' w v : SpaceTime}
    (hz1 : torusParabolicSize z ≤ 1) (hz1' : torusParabolicSize z' ≤ 1)
    (h1 : 0 < torusParabolicSize (z - w)) (h0 : 0 < torusParabolicSize (0 - w))
    (hu : 0 < torusParabolicSize (u - w))
    (h1' : 0 < torusParabolicSize (z' - v)) (h0' : 0 < torusParabolicSize (0 - v))
    (hu' : 0 < torusParabolicSize (u' - v)) (hwv : 0 < torusParabolicSize (w - v)) :
    |K (z - w) - K (-w)| * |K (z' - v) - K (-v)| *
        (torusParabolicSize (w - u) ^ (-a) * torusParabolicSize (w - v) ^ (-b) *
          torusParabolicSize (u' - v) ^ (-c)) ≤
      4 * B ^ 2 * 3 ^ δ * i3PsiChainMajorant α β γ z z' u u' w v := by
  subst ha hb hβ hc
  have key := abs_dK_dK_chain_le (α := α) (β₀ := β₀) (γ := γ) (u := u) (u' := u') hB hδ hγ hK hKs
    hz1 hz1' h1 h0 h1' h0' hu' hwv
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
    _ ≤ 4 * (B ^ 2 * 3 ^ δ * i3PsiChainMajorant α (β₀ + δ) γ z z' u u' w v) :=
        mul_le_mul_of_nonneg_left key (by norm_num)
    _ = _ := by ring

end RegularityStructures

end
