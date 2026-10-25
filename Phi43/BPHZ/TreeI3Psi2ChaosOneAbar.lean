/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3Psi2ChaosOneSplit
public import Phi43.BPHZ.KernelCalculusRenorm

/-!
# Bound for the renormalised convolution `Ā`

`L = K Q²` is of order `-5`, hence (on its support `s ≤ 2`) also of order `-(5+δ)`, and
Lemma 10.16 of [Hai14] (`abs_integral_mul_sub_le`, with `a₁ = 5 + δ`, `a₂ = 3`) gives
`|Ā(x)| ≤ C s(x)^(-(3+δ))`, with `C` depending only on `B, δ`.
-/

public section

open MeasureTheory

namespace RegularityStructures

theorem abs_i3Psi2L_le {K Q : SpaceTime → ℝ} {B δ : ℝ} (hB : 0 ≤ B) (hδ : 0 ≤ δ)
    (hKs : ∀ x : SpaceTime, 1 < |x.1| → K x = 0)
    (hK : ∀ x, 0 < torusParabolicSize x → |K x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ)))
    (hQ : ∀ x, 0 < torusParabolicSize x → |Q x| ≤ B * torusParabolicSize x ^ (-(1 : ℝ)))
    {v : SpaceTime} (hv : 0 < torusParabolicSize v) :
    |K v * Q v ^ 2| ≤ (B ^ 3 * 2 ^ δ) * torusParabolicSize v ^ (-(5 + δ)) := by
  have n2 : (0 : ℝ) ≤ 2 ^ δ := Real.rpow_nonneg (by norm_num) _
  have hnn : 0 ≤ (B ^ 3 * 2 ^ δ) * torusParabolicSize v ^ (-(5 + δ)) :=
    mul_nonneg (mul_nonneg (pow_nonneg hB 3) n2) (Real.rpow_nonneg hv.le _)
  by_cases h1 : |v.1| ≤ 1
  · have h2 : torusParabolicSize v ≤ 2 := by
      have := torusParabolicSize_le_sqrt_add_one h1
      simpa [Real.sqrt_one, one_add_one_eq_two] using this
    have sq := abs_Q_sq_le_singularPow hQ (c := v) (w := 0) (by simpa using hv)
    have a1 := hK v hv
    have e : |K v * Q v ^ 2| = |K v| * |Q v| ^ 2 := by rw [abs_mul, abs_pow]
    have hQ1 := hQ v hv
    have hsq : |Q v| ^ 2 ≤ (B * torusParabolicSize v ^ (-(1 : ℝ))) ^ 2 :=
      pow_le_pow_left₀ (abs_nonneg _) hQ1 2
    have e2 : (B * torusParabolicSize v ^ (-(1 : ℝ))) ^ 2 = B ^ 2 * torusParabolicSize v ^ (-(2 : ℝ)) := by
      rw [mul_pow, ← Real.rpow_natCast (torusParabolicSize v ^ (-(1 : ℝ))) 2,
        ← Real.rpow_mul hv.le]
      norm_num
    have hpow : torusParabolicSize v ^ (-(3 : ℝ)) * torusParabolicSize v ^ (-(2 : ℝ)) =
        torusParabolicSize v ^ δ * torusParabolicSize v ^ (-(5 + δ)) := by
      rw [← Real.rpow_add hv, ← Real.rpow_add hv]; congr 1; ring
    have hle : torusParabolicSize v ^ δ ≤ 2 ^ δ := Real.rpow_le_rpow hv.le h2 hδ
    have nn := Real.rpow_nonneg hv.le (-(5 + δ))
    calc |K v * Q v ^ 2| = |K v| * |Q v| ^ 2 := e
      _ ≤ (B * torusParabolicSize v ^ (-(3 : ℝ))) * (B ^ 2 * torusParabolicSize v ^ (-(2 : ℝ))) :=
          mul_le_mul a1 (hsq.trans e2.le) (sq_nonneg _) (mul_nonneg hB (Real.rpow_nonneg hv.le _))
      _ = B ^ 3 * (torusParabolicSize v ^ (-(3 : ℝ)) * torusParabolicSize v ^ (-(2 : ℝ))) := by
          ring
      _ = B ^ 3 * (torusParabolicSize v ^ δ * torusParabolicSize v ^ (-(5 + δ))) := by rw [hpow]
      _ ≤ B ^ 3 * (2 ^ δ * torusParabolicSize v ^ (-(5 + δ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hle nn) (pow_nonneg hB 3)
      _ = _ := by ring
  · rw [hKs v (not_le.1 h1)]
    simpa using hnn

/-- **Bound for `Ā`** ([Hai14, Lemma 10.16]). -/
theorem abs_i3Psi2Abar_le {B δ : ℝ} (hB : 0 ≤ B) (hδ : 0 < δ) (hδ1 : δ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {K J Q : SpaceTime → ℝ},
      (∀ x : SpaceTime, 1 < |x.1| → K x = 0) →
      (∀ x, 0 < torusParabolicSize x → |K x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ))) →
      (∀ x, 0 < torusParabolicSize x → |Q x| ≤ B * torusParabolicSize x ^ (-(1 : ℝ))) →
      (∀ x, 0 < torusParabolicSize x → |J x| ≤ B * torusParabolicSize x ^ (-(3 : ℝ))) →
      (∀ u h : SpaceTime, 0 < torusParabolicSize u →
        torusParabolicSize h ≤ torusParabolicSize u / 2 →
          |J (u + h) - J u| ≤ B * torusParabolicSize h * torusParabolicSize u ^ (-(4 : ℝ))) →
      ∀ x : SpaceTime, 0 < torusParabolicSize x →
        |i3Psi2Abar K J Q x| ≤ C * torusParabolicSize x ^ (-(3 + δ)) := by
  obtain ⟨C0, hC0, h⟩ := abs_integral_mul_sub_le (a₁ := 5 + δ) (a₂ := 3) (by linarith)
    (by linarith) (by norm_num) (by linarith)
  have n2 : (0 : ℝ) ≤ 2 ^ δ := Real.rpow_nonneg (by norm_num) _
  refine ⟨C0 * (B ^ 3 * 2 ^ δ) * B, mul_nonneg (mul_nonneg hC0 (mul_nonneg (pow_nonneg hB 3) n2))
    hB, ?_⟩
  intro K J Q hKs hK hQ hJ hinc x hx
  have hinc' : ∀ u h : SpaceTime, 0 < torusParabolicSize u →
      torusParabolicSize h ≤ torusParabolicSize u / 2 →
        |J (u + h) - J u| ≤ B * torusParabolicSize h * torusParabolicSize u ^ (-(3 : ℝ) - 1) := by
    intro u h hu hh
    have e : (-(3 : ℝ) - 1) = -(4 : ℝ) := by norm_num
    rw [e]; exact hinc u h hu hh
  have := h (f₁ := fun v => K v * Q v ^ 2) (f₂ := J) (B₁ := B ^ 3 * 2 ^ δ) (B₂ := B)
    (mul_nonneg (pow_nonneg hB 3) n2) hB (fun v hv => abs_i3Psi2L_le hB hδ.le hKs hK hQ hv) hJ
    hinc' x hx
  have e : min 0 (5 - (5 + δ) - 3) = -(3 + δ) := by
    rw [min_eq_right (by linarith)]; ring
  rw [e] at this
  unfold i3Psi2Abar
  exact this

end RegularityStructures

end
