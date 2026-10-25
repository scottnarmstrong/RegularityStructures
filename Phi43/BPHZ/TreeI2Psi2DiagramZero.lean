/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI2Psi2DiagramPair

/-!
# The chaos-`0` part of the tree `I(Ψ²) Ψ²`

[Hai14, (10.39)-(10.42)]: the chaos-`0` component is `-2 ∫ K(x - w) Q(w - y)² dw`, and
`K * Q²` is of order `-3 - 2 + 5 = 0`, so it is `≲ s(y - x)^(-δ)` for every `δ > 0`.
We prove it for `K`, `Q` as in the kernel calculus (`|K| ≤ B s^(-3)`, time support `|t| ≤ 1`,
`|Q| ≤ B s^(-1)`), for `|y₀ - x₀| ≤ 1`: `|∫ K(x - w) Q(w - y)²| ≤ C B³ s(y - x)^(-δ)`.  The borderline
total order `5` is handled by weakening `s^(-2)` to `3^δ s^(-2-δ)` on the support.
-/

public section

open MeasureTheory

namespace RegularityStructures

/-- On `0 < s ≤ 3`, `s^(-b) ≤ 3^ε s^(-(b + ε))`. -/
theorem rpow_neg_le_three_rpow_mul {s b ε : ℝ} (hε : 0 ≤ ε) (hs : 0 < s)
    (h3 : s ≤ 3) : s ^ (-b) ≤ 3 ^ ε * s ^ (-(b + ε)) := by
  have h1 : (3 : ℝ) ^ (-ε) ≤ s ^ (-ε) := Real.rpow_le_rpow_of_nonpos hs h3 (neg_nonpos.2 hε)
  have e : s ^ (-(b + ε)) = s ^ (-b) * s ^ (-ε) := by
    rw [← Real.rpow_add hs]; congr 1; ring
  have h3p : (3 : ℝ) ^ ε * (3 : ℝ) ^ (-ε) = 1 := by
    rw [← Real.rpow_add (by norm_num)]; simp
  have n1 : 0 ≤ s ^ (-b) := Real.rpow_nonneg hs.le _
  have n3 : 0 ≤ (3 : ℝ) ^ ε := Real.rpow_nonneg (by norm_num) _
  rw [e]
  calc s ^ (-b) = s ^ (-b) * ((3 : ℝ) ^ ε * (3 : ℝ) ^ (-ε)) := by rw [h3p, mul_one]
    _ = 3 ^ ε * (s ^ (-b) * (3 : ℝ) ^ (-ε)) := by ring
    _ ≤ 3 ^ ε * (s ^ (-b) * s ^ (-ε)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h1 n1) n3

/-- **The chaos-`0` integral**, lower-integral form:
`∫ |K(x - w)| Q(w - y)² dw ≲ B³ s(y - x)^(-δ)`. -/
theorem i2Psi2LintBound_chaos0 {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K Q : SpaceTime → ℝ} {B : ℝ}, 0 ≤ B →
      (∀ u : SpaceTime, 1 < |u.1| → K u = 0) →
      (∀ u : SpaceTime, 0 < torusParabolicSize u →
        |K u| ≤ B * torusParabolicSize u ^ (-(3 : ℝ))) →
      (∀ u : SpaceTime, 0 < torusParabolicSize u →
        |Q u| ≤ B * torusParabolicSize u ^ (-(1 : ℝ))) →
      ∀ x y : SpaceTime, |y.1 - x.1| ≤ 1 → 0 < torusParabolicSize (y - x) →
        i2Psi2LintBound volume (fun w => |K (x - w) * Q (w - y) ^ 2|)
          (C * B ^ 3 * torusParabolicSize (y - x) ^ (-δ)) := by
  obtain ⟨CG, hCG, hG⟩ := i2Psi2LintBound_rpow_mul_rpow_of_gt (a := 3) (b := 2 + δ)
    (by norm_num) (by norm_num) (by linarith) (by linarith) (by linarith)
  refine ⟨8 * 3 ^ δ * CG, mul_nonneg (mul_nonneg (by norm_num) (Real.rpow_nonneg (by norm_num) _))
    hCG, ?_⟩
  intro K Q B hB hKs hKb hQb x y hxy hr
  have hyx : 0 < torusParabolicSize (x - y) := torusParabolicSize_pos_of_sub_pos hr
  have g := hG x y hyx
  have e : (5 : ℝ) - 3 - (2 + δ) = -δ := by ring
  rw [e] at g
  have c := g.const_mul (c := 4 * B ^ 3 * 3 ^ δ) (mul_nonneg (by positivity)
    (Real.rpow_nonneg (by norm_num) _))
  have t := torusParabolicSize_sub_rpow_neg_le (a := x) (b := y) (e := δ) hδ.le hδ1 hr
  refine c.mono_ae ?_ ?_
  · filter_upwards [ae_torusParabolicSize_sub_pos x, ae_torusParabolicSize_sub_pos y]
      with w hx hy
    by_cases hK : K (x - w) = 0
    · rw [hK, zero_mul, abs_zero]
      exact mul_nonneg (mul_nonneg (by positivity) (Real.rpow_nonneg (by norm_num) _))
        (mul_nonneg (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
          (Real.rpow_nonneg (torusParabolicSize_nonneg _) _))
    · have h1 : |(x - w).1| ≤ 1 := by
        by_contra hc
        exact hK (hKs _ (not_le.1 hc))
      have h4 : |(y - w).1| ≤ 4 := by
        have : (y - w).1 = (y.1 - x.1) + (x - w).1 := by simp only [Prod.fst_sub]; ring
        rw [this]
        calc |(y.1 - x.1) + (x - w).1| ≤ |y.1 - x.1| + |(x - w).1| := abs_add_le _ _
          _ ≤ 4 := by linarith
      have h3 := torusParabolicSize_le_three_of_abs_le h4
      have hw := rpow_neg_le_three_rpow_mul (b := 2) (ε := δ) hδ.le hy h3
      have hq := sq_cov_flip_le hB hQb (g := y) (w := w) hy
      have hk := hKb _ hx
      rw [abs_mul, abs_sq]
      calc |K (x - w)| * Q (w - y) ^ 2
          ≤ (B * torusParabolicSize (x - w) ^ (-(3 : ℝ))) *
            (4 * B ^ 2 * torusParabolicSize (y - w) ^ (-(2 : ℝ))) :=
          mul_le_mul hk hq (sq_nonneg _) (mul_nonneg hB (Real.rpow_nonneg hx.le _))
        _ ≤ (B * torusParabolicSize (x - w) ^ (-(3 : ℝ))) *
            (4 * B ^ 2 * (3 ^ δ * torusParabolicSize (y - w) ^ (-(2 + δ)))) := by
          refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hB (Real.rpow_nonneg hx.le _))
          exact mul_le_mul_of_nonneg_left hw (by positivity)
        _ = _ := by ring
  · have hn : 0 ≤ 4 * B ^ 3 * 3 ^ δ * CG := mul_nonneg (mul_nonneg (by positivity)
      (Real.rpow_nonneg (by norm_num) _)) hCG
    calc 4 * B ^ 3 * 3 ^ δ * (CG * torusParabolicSize (x - y) ^ (-δ))
        ≤ 4 * B ^ 3 * 3 ^ δ * (CG * (2 * torusParabolicSize (y - x) ^ (-δ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left t hCG) (by positivity)
      _ = _ := by ring

/-- **Chaos `0` of the tree `I(Ψ²) Ψ²`**, [Hai14, (10.42)]: for `δ ∈ (0, 1]`,
`|-2 ∫ K(x - w) Q(w - y)² dw| ≤ C B³ s(y - x)^(-δ)` whenever `|y₀ - x₀| ≤ 1`, where
`|K| ≤ B s^(-3)` with time support `|t| ≤ 1` and `|Q| ≤ B s^(-1)`; the integrand is integrable. -/
theorem integrable_and_abs_integral_chaos0_le {δ : ℝ} (hδ : 0 < δ) (hδ1 : δ ≤ 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K Q : SpaceTime → ℝ} {B : ℝ}, 0 ≤ B → Measurable K → Measurable Q →
      (∀ u : SpaceTime, 1 < |u.1| → K u = 0) →
      (∀ u : SpaceTime, 0 < torusParabolicSize u →
        |K u| ≤ B * torusParabolicSize u ^ (-(3 : ℝ))) →
      (∀ u : SpaceTime, 0 < torusParabolicSize u →
        |Q u| ≤ B * torusParabolicSize u ^ (-(1 : ℝ))) →
      ∀ x y : SpaceTime, |y.1 - x.1| ≤ 1 → 0 < torusParabolicSize (y - x) →
        Integrable (fun w => K (x - w) * Q (w - y) ^ 2) ∧
        |-2 * ∫ w, K (x - w) * Q (w - y) ^ 2| ≤
          C * B ^ 3 * torusParabolicSize (y - x) ^ (-δ) := by
  obtain ⟨C, hC, h⟩ := i2Psi2LintBound_chaos0 hδ hδ1
  refine ⟨2 * C, by positivity, ?_⟩
  intro K Q B hB hKm hQm hKs hKb hQb x y hxy hr
  have hm : AEStronglyMeasurable (fun w => K (x - w) * Q (w - y) ^ 2) volume :=
    ((hKm.comp (measurable_const.sub measurable_id)).mul
      ((hQm.comp (measurable_id.sub measurable_const)).pow_const 2)).aestronglyMeasurable
  have hM : 0 ≤ C * B ^ 3 * torusParabolicSize (y - x) ^ (-δ) :=
    mul_nonneg (mul_nonneg hC (pow_nonneg hB 3)) (Real.rpow_nonneg (torusParabolicSize_nonneg _) _)
  obtain ⟨hi, hb⟩ := abs_integral_le_of_i2Psi2LintBound hm (h hB hKs hKb hQb x y hxy hr) hM
  refine ⟨hi, ?_⟩
  rw [abs_mul, abs_neg, abs_two]
  calc 2 * |∫ w, K (x - w) * Q (w - y) ^ 2| ≤ 2 * (C * B ^ 3 * torusParabolicSize (y - x) ^ (-δ)) :=
        mul_le_mul_of_nonneg_left hb (by norm_num)
    _ = _ := by ring

end RegularityStructures

end
