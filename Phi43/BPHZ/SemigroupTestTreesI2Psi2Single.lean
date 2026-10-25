/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.SemigroupTestTreesI2Psi2Cross

/-!
# The single integrals of `I(Ψ²) Ψ²`, for arbitrary `x, y, y'`

The factorised terms of the covariance of the field of `I(Ψ²) Ψ²` are products of single integrals
`∫ A_p(w) G(w) dw` with `|G| ≤ Λ s₂(e; w)` (`i2Psi2_single_two_global`, giving
`C B Λ D^(1/4) (s(p - e)^(-1/4) + s(x - e)^(-1/4))`) or `|G| ≤ Λ s₁(p; w) s₁(e; w)`
(`i2Psi2_single_one_one_global`).  The mean `-2 ∫ K(x - w) Q(w - y)² dw` is bounded by
`C B³ D^(1/4) s(x - y)^(-1/4)` (`i2Psi2_mean_global`).  Here `D` bounds `s(e - w)` on the slab.
-/

public section

open MeasureTheory Set

namespace RegularityStructures

/-- A function dominated by an integrable singular majorant has a bounded absolute integral. -/
theorem integrable_abs_integral_le_of_singularIntLe {G M : SpaceTime → ℝ} {X : ℝ}
    (hM : SingularIntLe M X) (hG : AEStronglyMeasurable G volume)
    (h : ∀ᵐ w : SpaceTime ∂volume, |G w| ≤ M w) : Integrable G ∧ |∫ w, G w| ≤ X := by
  have hI : Integrable G := hM.1.mono' hG (h.mono fun w hw => by rwa [Real.norm_eq_abs])
  refine ⟨hI, ?_⟩
  have := norm_integral_le_of_norm_le hM.1 (h.mono fun w hw => by rwa [Real.norm_eq_abs])
  rw [Real.norm_eq_abs] at this
  exact this.trans hM.2

/-- Single integral against a square singularity. -/
theorem i2Psi2_single_two_global :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K Q : SpaceTime → ℝ} {B : ℝ}, SingularKernelData K Q B →
      ∀ (x p e : SpaceTime) {D Λ : ℝ} {G : SpaceTime → ℝ}, 0 ≤ D → 0 ≤ Λ →
      0 < torusParabolicSize (p - e) → 0 < torusParabolicSize (x - e) →
      (∀ w : SpaceTime, |w.1 - x.1| ≤ |p.1 - x.1| + 1 → torusParabolicSize (e - w) ≤ D) →
      AEStronglyMeasurable G volume →
      (∀ᵐ w : SpaceTime ∂volume, |G w| ≤ Λ * singularPow 2 e w) →
      Integrable (fun w => i2Psi2Increment K x p w * G w) ∧
        |∫ w, i2Psi2Increment K x p w * G w| ≤ C * B * Λ * D ^ (1 / 4 : ℝ) *
          (torusParabolicSize (p - e) ^ (-(1 / 4 : ℝ)) +
            torusParabolicSize (x - e) ^ (-(1 / 4 : ℝ))) := by
  obtain ⟨C1, hC1, h1⟩ := singularIntLe_mul_two (a := 3) (b := 2 + 1 / 4) (η := 1 / 4)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  refine ⟨C1, hC1, ?_⟩
  intro K Q B h x p e D Λ G hD0 hΛ hpe hxe hD hGm hG
  have hB := h.nonneg
  have hDδ : 0 ≤ D ^ (1 / 4 : ℝ) := Real.rpow_nonneg hD0 _
  have hs := ((h1 p e hpe).add (h1 x e hxe)).const_mul (c := B * Λ * D ^ (1 / 4 : ℝ))
    (by positivity)
  refine integrable_abs_integral_le_of_singularIntLe (M := fun w => B * Λ * D ^ (1 / 4 : ℝ) *
    (singularPow 3 p w * singularPow (2 + 1 / 4) e w + singularPow 3 x w *
      singularPow (2 + 1 / 4) e w)) (hs.mono_right (le_of_eq ?_)) ?_ ?_
  · ring
  · exact ((h.measurable_increment x p).aestronglyMeasurable).mul hGm
  · filter_upwards [ae_abs_i2Psi2Increment_le h x p, hG, ae_torusParabolicSize_sub_pos e] with w hw hg hpos
    rw [abs_mul]
    by_cases hS : w ∈ {w : SpaceTime | |w.1 - x.1| ≤ |p.1 - x.1| + 1}
    · simp only [Set.indicator_of_mem hS] at hw
      have hpad := rpow_neg_le_pad (k := 2) hpos (hD w hS) (δ := 1 / 4) (by norm_num)
      have hsp : singularPow 2 e w ≤ D ^ (1 / 4 : ℝ) * singularPow (2 + 1 / 4) e w := by
        simpa [singularPow] using hpad
      calc |i2Psi2Increment K x p w| * |G w|
          ≤ (B * (singularPow 3 p w + singularPow 3 x w)) * (Λ * singularPow 2 e w) :=
            mul_le_mul hw hg (abs_nonneg _) (mul_nonneg hB (add_nonneg (singularPow_nonneg _ _ _)
              (singularPow_nonneg _ _ _)))
        _ ≤ (B * (singularPow 3 p w + singularPow 3 x w)) *
              (Λ * (D ^ (1 / 4 : ℝ) * singularPow (2 + 1 / 4) e w)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsp hΛ)
              (mul_nonneg hB (add_nonneg (singularPow_nonneg _ _ _) (singularPow_nonneg _ _ _)))
        _ = _ := by ring
    · simp only [Set.indicator_of_notMem hS, mul_zero] at hw
      have : |i2Psi2Increment K x p w| = 0 := le_antisymm hw (abs_nonneg _)
      rw [this, zero_mul]
      refine mul_nonneg (mul_nonneg (mul_nonneg hB hΛ) hDδ) (add_nonneg (mul_nonneg
        (singularPow_nonneg _ _ _) (singularPow_nonneg _ _ _)) (mul_nonneg
        (singularPow_nonneg _ _ _) (singularPow_nonneg _ _ _)))

end RegularityStructures

end
