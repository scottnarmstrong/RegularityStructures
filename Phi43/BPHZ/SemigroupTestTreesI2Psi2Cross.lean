/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestTreesI2Psi2Sq

/-!
# The coupled terms of the chaos-`4` and chaos-`2` parts of `I(Ψ²) Ψ²`, for arbitrary `x, y, y'`

Two terms are dominated by the coupled majorant with `α = β = 4`, `k = 1`:

* the cross term `∫∫ A_y(w) A_{y'}(v) Q(w - v) Q(w - y') Q(y - v)` of chaos `4`;
* the chain term `∫∫ A_y(w) Q(w - y) A_{y'}(v) Q(v - y') Q(w - v)` of chaos `2`.

Both reduce to `coupled_four_four_integral` since `(s₃(p₁; w) + s₃(p₂; w)) s₁(e; w)` is dominated by
`s₄(p₁; w) + s₄(p₂; w) + 2 s₄(e; w)`.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

/-- `(s₃(p₁) + s₃(p₂)) s₁(e) ≤ s₄(p₁) + s₄(p₂) + 2 s₄(e)` on a slab. -/
theorem ind_singularPow_three_mul_one_le (S : Set SpaceTime) {p₁ p₂ e w : SpaceTime}
    (h1 : 0 < torusParabolicSize (p₁ - w)) (h2 : 0 < torusParabolicSize (p₂ - w))
    (h3 : 0 < torusParabolicSize (e - w)) :
    Set.indicator S (fun w => singularPow 3 p₁ w + singularPow 3 p₂ w) w * singularPow 1 e w ≤
      Set.indicator S (fun w => ∑ i, (![1, 1, 2] : Fin 3 → ℝ) i *
        singularPow 4 (![p₁, p₂, e] i) w) w := by
  by_cases hw : w ∈ S
  · simp only [Set.indicator_of_mem hw, Fin.sum_univ_three]
    have e1 := singularPow_mul_le (a := 3) (b := 1) (by norm_num) (by norm_num) h1 h3
    have e2 := singularPow_mul_le (a := 3) (b := 1) (by norm_num) (by norm_num) h2 h3
    norm_num at e1 e2 ⊢
    nlinarith [e1, e2]
  · simp [Set.indicator_of_notMem hw]

/-- **Coupled integral with `α = β = 4`, `k = 1`.** -/
theorem coupled_four_four_integral :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {F : SpaceTime → SpaceTime → ℝ} {Λ τ T T' D : ℝ}
      {p₁ p₂ e p₁' p₂' e' : SpaceTime}, 0 ≤ Λ → 0 ≤ T → 0 ≤ T' → 0 ≤ D →
      AEStronglyMeasurable (Function.uncurry F) (volume.prod volume) →
      (∀ w v : SpaceTime, |w.1 - τ| ≤ T → |v.1 - τ| ≤ T' → torusParabolicSize (w - v) ≤ D) →
      (∀ᵐ w : SpaceTime ∂volume, ∀ᵐ v : SpaceTime ∂volume, |F w v| ≤
        Λ * ((Set.indicator {w : SpaceTime | |w.1 - τ| ≤ T}
            (fun w => singularPow 3 p₁ w + singularPow 3 p₂ w) w * singularPow 1 e w) *
          (singularPow 1 w v * (Set.indicator {v : SpaceTime | |v.1 - τ| ≤ T'}
            (fun v => singularPow 3 p₁' v + singularPow 3 p₂' v) v * singularPow 1 e' v)))) →
      Integrable (Function.uncurry F) (volume.prod volume) ∧
        |∫ w, ∫ v, F w v| ≤ C * Λ * D ^ (1 / 4 : ℝ) * 16 *
          (80 / (5 - (4 + 1 / 4)) + 2 * T) := by
  obtain ⟨C0, hC0, h0⟩ := coupled_sum_integral (α := 4) (β := 4) (k := 1) (δ := 1 / 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
  refine ⟨C0, hC0, ?_⟩
  intro F Λ τ T T' D p₁ p₂ e p₁' p₂' e' hΛ hT hT' hD hmeas hDw hFG
  have e3 : (∑ i, (![1, 1, 2] : Fin 3 → ℝ) i) = 4 := by
    simp [Fin.sum_univ_three]; norm_num
  have key := h0 (F := F) (Λ := Λ) (τ := τ) (τ' := τ) (T := T) (T' := T') (D := D)
    (c := ![1, 1, 2]) (c' := ![1, 1, 2]) (q := ![p₁, p₂, e]) (q' := ![p₁', p₂', e'])
    hΛ hT hT' hD (by intro i; fin_cases i <;> simp) (by intro j; fin_cases j <;> simp)
    hmeas hDw ?_
  · refine ⟨key.1, key.2.trans (le_of_eq ?_)⟩
    rw [e3]
    ring
  · filter_upwards [hFG, ae_torusParabolicSize_sub_pos p₁, ae_torusParabolicSize_sub_pos p₂,
      ae_torusParabolicSize_sub_pos e] with w hw a b c
    filter_upwards [hw, ae_torusParabolicSize_sub_pos p₁', ae_torusParabolicSize_sub_pos p₂',
      ae_torusParabolicSize_sub_pos e'] with v hv a' b' c'
    refine hv.trans ?_
    have m1 := ind_singularPow_three_mul_one_le {w : SpaceTime | |w.1 - τ| ≤ T} a b c
    have m2 := ind_singularPow_three_mul_one_le {v : SpaceTime | |v.1 - τ| ≤ T'} a' b' c'
    have n1 : 0 ≤ Set.indicator {w : SpaceTime | |w.1 - τ| ≤ T}
        (fun w => singularPow 3 p₁ w + singularPow 3 p₂ w) w * singularPow 1 e w :=
      mul_nonneg (Set.indicator_nonneg (fun w _ => add_nonneg (singularPow_nonneg _ _ _)
        (singularPow_nonneg _ _ _)) w) (singularPow_nonneg _ _ _)
    have n2 : 0 ≤ singularPow 1 w v := singularPow_nonneg _ _ _
    refine mul_le_mul_of_nonneg_left ?_ hΛ
    exact mul_le_mul m1 (mul_le_mul_of_nonneg_left m2 n2) (mul_nonneg n2 (mul_nonneg
      (Set.indicator_nonneg (fun w _ => add_nonneg (singularPow_nonneg _ _ _)
        (singularPow_nonneg _ _ _)) v) (singularPow_nonneg _ _ _))) (Set.indicator_nonneg
      (fun w _ => Finset.sum_nonneg fun i _ => mul_nonneg (by fin_cases i <;> simp)
        (singularPow_nonneg _ _ _)) w)

end RegularityStructures

end
