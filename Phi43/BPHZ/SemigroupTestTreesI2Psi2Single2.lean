/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestTreesI2Psi2Single

/-!
# Single integrals with two first-order singularities, and the mean of `I(Ψ²) Ψ²`

* `i2Psi2_single_one_one_global`: `|∫ A_p(w) G(w) dw| ≤ C B Λ D^(1/4) (s(p - e)^(-1/4) + s(x - e)^(-1/4))`
  when `|G| ≤ Λ s₁(p; ·) s₁(e; ·)`;
* `i2Psi2_mean_global`: the mean `-2 ∫ K(x - w) Q(w - y)² dw` is bounded by
  `C B³ D^(1/4) s(x - y)^(-1/4)`.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

/-- Single integral against two first-order singularities. -/
theorem i2Psi2_single_one_one_global :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K Q : SpaceTime → ℝ} {B : ℝ}, SingularKernelData K Q B →
      ∀ (x p e : SpaceTime) {D Λ : ℝ} {G : SpaceTime → ℝ}, 0 ≤ D → 0 ≤ Λ →
      0 < torusParabolicSize (p - e) → 0 < torusParabolicSize (x - e) →
      (∀ w : SpaceTime, |w.1 - x.1| ≤ |p.1 - x.1| + 1 → torusParabolicSize (e - w) ≤ D) →
      AEStronglyMeasurable G volume →
      (∀ᵐ w : SpaceTime ∂volume, |G w| ≤ Λ * (singularPow 1 p w * singularPow 1 e w)) →
      Integrable (fun w => i2Psi2Increment K x p w * G w) ∧
        |∫ w, i2Psi2Increment K x p w * G w| ≤ C * B * Λ * D ^ (1 / 4 : ℝ) *
          (torusParabolicSize (p - e) ^ (-(1 / 4 : ℝ)) +
            torusParabolicSize (x - e) ^ (-(1 / 4 : ℝ))) := by
  obtain ⟨C1, hC1, h1⟩ := singularIntLe_mul_two (a := 4) (b := 1 + 1 / 4) (η := 1 / 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨C1 * 3, by positivity, ?_⟩
  intro K Q B h x p e D Λ G hD0 hΛ hpe hxe hD hGm hG
  have hB := h.nonneg
  have hDδ : 0 ≤ D ^ (1 / 4 : ℝ) := Real.rpow_nonneg hD0 _
  have hs := (((h1 p e hpe).const_mul (c := 3) (by norm_num)).add (h1 x e hxe)).const_mul
    (c := B * Λ * D ^ (1 / 4 : ℝ)) (by positivity)
  refine integrable_abs_integral_le_of_singularIntLe (M := fun w => B * Λ * D ^ (1 / 4 : ℝ) *
    (3 * (singularPow 4 p w * singularPow (1 + 1 / 4) e w) +
      singularPow 4 x w * singularPow (1 + 1 / 4) e w)) (hs.mono_right ?_) ?_ ?_
  · set a := torusParabolicSize (p - e) ^ (-(1 / 4 : ℝ)) with ha
    set b := torusParabolicSize (x - e) ^ (-(1 / 4 : ℝ)) with hb'
    have hb0 : 0 ≤ b := Real.rpow_nonneg (torusParabolicSize_nonneg _) _
    have hc0 : 0 ≤ B * Λ * D ^ (1 / 4 : ℝ) * C1 * b := by
      have := mul_nonneg (mul_nonneg hB hΛ) hDδ
      exact mul_nonneg (mul_nonneg this hC1) hb0
    nlinarith [hc0]
  · exact ((h.measurable_increment x p).aestronglyMeasurable).mul hGm
  · filter_upwards [ae_abs_i2Psi2Increment_le h x p, hG, ae_torusParabolicSize_sub_pos e,
      ae_torusParabolicSize_sub_pos p, ae_torusParabolicSize_sub_pos x] with w hw hg hpos hpp hpx
    rw [abs_mul]
    by_cases hS : w ∈ {w : SpaceTime | |w.1 - x.1| ≤ |p.1 - x.1| + 1}
    · simp only [Set.indicator_of_mem hS] at hw
      have hpad := rpow_neg_le_pad (k := 1) hpos (hD w hS) (δ := 1 / 4) (by norm_num)
      have hsp : singularPow 1 e w ≤ D ^ (1 / 4 : ℝ) * singularPow (1 + 1 / 4) e w := by
        simpa [singularPow] using hpad
      have hind := ind_singularPow_three_mul_one_le Set.univ (p₁ := p) (p₂ := x) (e := p) (w := w)
        hpp hpx hpp
      simp only [Set.indicator_univ, Fin.sum_univ_three] at hind
      norm_num at hind
      have hn : 0 ≤ singularPow 3 p w + singularPow 3 x w :=
        add_nonneg (singularPow_nonneg _ _ _) (singularPow_nonneg _ _ _)
      calc |i2Psi2Increment K x p w| * |G w|
          ≤ (B * (singularPow 3 p w + singularPow 3 x w)) *
              (Λ * (singularPow 1 p w * singularPow 1 e w)) :=
            mul_le_mul hw hg (abs_nonneg _) (mul_nonneg hB hn)
        _ = B * Λ * (((singularPow 3 p w + singularPow 3 x w) * singularPow 1 p w) *
              singularPow 1 e w) := by ring
        _ ≤ B * Λ * ((3 * singularPow 4 p w + singularPow 4 x w) *
              (D ^ (1 / 4 : ℝ) * singularPow (1 + 1 / 4) e w)) := by
            refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hB hΛ)
            exact mul_le_mul (by linarith) hsp (singularPow_nonneg _ _ _)
              (by have := singularPow_nonneg 4 p w; have := singularPow_nonneg 4 x w; positivity)
        _ = _ := by ring
    · simp only [Set.indicator_of_notMem hS, mul_zero] at hw
      have : |i2Psi2Increment K x p w| = 0 := le_antisymm hw (abs_nonneg _)
      rw [this, zero_mul]
      have := singularPow_nonneg 4 p w
      have := singularPow_nonneg 4 x w
      have := singularPow_nonneg (1 + 1 / 4) e w
      positivity

/-- The mean of the field of `I(Ψ²) Ψ²`. -/
theorem i2Psi2_mean_global :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K Q : SpaceTime → ℝ} {B : ℝ}, SingularKernelData K Q B →
      ∀ (x y : SpaceTime) {D : ℝ}, 0 ≤ D → 0 < torusParabolicSize (x - y) →
      (∀ w : SpaceTime, |w.1 - x.1| ≤ 1 → torusParabolicSize (y - w) ≤ D) →
      |-2 * ∫ w, K (x - w) * Q (w - y) ^ 2| ≤ C * B ^ 3 * D ^ (1 / 4 : ℝ) *
        torusParabolicSize (x - y) ^ (-(1 / 4 : ℝ)) := by
  obtain ⟨C1, hC1, h1⟩ := singularIntLe_mul_two (a := 3) (b := 2 + 1 / 4) (η := 1 / 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨C1 * 8, by positivity, ?_⟩
  intro K Q B h x y D hD0 hxy hD
  have hB := h.nonneg
  have hDδ : 0 ≤ D ^ (1 / 4 : ℝ) := Real.rpow_nonneg hD0 _
  have hs := (h1 x y hxy).const_mul (c := 4 * B ^ 3 * D ^ (1 / 4 : ℝ)) (by positivity)
  have key := integrable_abs_integral_le_of_singularIntLe
    (G := fun w => K (x - w) * Q (w - y) ^ 2)
    (M := fun w => 4 * B ^ 3 * D ^ (1 / 4 : ℝ) *
      (singularPow 3 x w * singularPow (2 + 1 / 4) y w)) hs
    (((h.measurable_K.comp (measurable_const.sub measurable_id)).mul
      ((h.measurable_Q.comp (measurable_id.sub measurable_const)).pow_const 2)
      ).aestronglyMeasurable) ?_
  · rw [abs_mul, abs_neg, abs_two]
    calc 2 * |∫ w, K (x - w) * Q (w - y) ^ 2|
        ≤ 2 * (4 * B ^ 3 * D ^ (1 / 4 : ℝ) * (C1 * torusParabolicSize (x - y) ^ (-(1 / 4 : ℝ)))) :=
          mul_le_mul_of_nonneg_left key.2 (by norm_num)
      _ = _ := by ring
  · filter_upwards [ae_torusParabolicSize_sub_pos y, ae_torusParabolicSize_sub_pos x] with w hpos hpx
    rw [abs_mul]
    by_cases hS : |w.1 - x.1| ≤ 1
    · have hK : |K (x - w)| ≤ B * singularPow 3 x w := h.K_bound _ hpx
      have hq := sq_cov_flip_le hB h.Q_bound hpos
      have hq' : |Q (w - y) ^ 2| ≤ 4 * B ^ 2 * singularPow 2 y w := by
        rw [abs_of_nonneg (sq_nonneg _)]
        simpa [singularPow] using hq
      have hpad := rpow_neg_le_pad (k := 2) hpos (hD w hS) (δ := 1 / 4) (by norm_num)
      have hsp : singularPow 2 y w ≤ D ^ (1 / 4 : ℝ) * singularPow (2 + 1 / 4) y w := by
        simpa [singularPow] using hpad
      calc |K (x - w)| * |Q (w - y) ^ 2|
          ≤ (B * singularPow 3 x w) * (4 * B ^ 2 * singularPow 2 y w) :=
            mul_le_mul hK hq' (abs_nonneg _) (mul_nonneg hB (singularPow_nonneg _ _ _))
        _ ≤ (B * singularPow 3 x w) * (4 * B ^ 2 * (D ^ (1 / 4 : ℝ) *
              singularPow (2 + 1 / 4) y w)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsp (by positivity))
              (mul_nonneg hB (singularPow_nonneg _ _ _))
        _ = _ := by ring
    · have : K (x - w) = 0 := by
        apply h.K_supp
        have : (x - w).1 = x.1 - w.1 := rfl
        rw [this, abs_sub_comm]
        exact not_le.1 hS
      rw [this, abs_zero, zero_mul]
      have := singularPow_nonneg 3 x w
      have := singularPow_nonneg (2 + 1 / 4) y w
      positivity

end RegularityStructures

end
