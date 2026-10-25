/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import Phi43.BPHZ.TreeI3PsiFieldMoment

/-!
# The block `E[:X_a²: X_b :X_c²: X_d]` on a Gaussian vector

For a centred Gaussian vector with covariance `C`:
`E[:X_a²: X_b :X_c²: X_d] = 2 C_ac² C_bd + 4 C_ac C_ad C_bc + 4 C_ab C_ac C_cd`
(`integral_wick_two_mul_X_mul_wick_two_mul_X`), and, when the diagonal is bounded by `D`, the product
is integrable with `E|·| ≤ 10 D³` (`integrable_and_abs_integral_wick_two_le`).
-/

public section

open MeasureTheory

namespace RegularityStructures

variable {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {n : ℕ} {X : Ω → Fin n → ℝ}
  {C : Fin n → Fin n → ℝ}

/-- **Block formula** for `E[:X_a²: X_b :X_c²: X_d]`. -/
theorem integral_wick_two_mul_X_mul_wick_two_mul_X (h : IsCentredGaussianVector P X C)
    (a b c d : Fin n) :
    ∫ ω, wickMonomial C (List.replicate 2 a) (X ω) * X ω b *
        wickMonomial C (List.replicate 2 c) (X ω) * X ω d ∂P =
      2 * C a c ^ 2 * C b d + 4 * C a c * C a d * C b c + 4 * C a b * C a c * C c d := by
  have := integral_wick_mul_wick_mul_wick_mul_wick_eq h (List.replicate 2 a) [b]
    (List.replicate 2 c) [d]
  simp only [wickMonomial_singleton] at this
  rw [this]
  simp [taggedLetters, List.finRange_succ, listMatchSum_cons_picks, listMatchSum_nil, picks,
    taggedWeight, List.replicate]
  ring

namespace IsCentredGaussianVector

/-- The square of `:X_a²: X_b` is integrable. -/
theorem integrable_wick_two_mul_X_sq (h : IsCentredGaussianVector P X C) (s : ℝ) (a b : Fin n) :
    Integrable (fun ω => ((X ω a ^ 2 - s) * X ω b) * ((X ω a ^ 2 - s) * X ω b)) P := by
  have e : (fun ω => ((X ω a ^ 2 - s) * X ω b) * ((X ω a ^ 2 - s) * X ω b)) =
      fun ω => X ω a ^ 4 * X ω b ^ 2 - (2 * s) * (X ω a ^ 2 * X ω b ^ 2) +
        (s ^ 2) * X ω b ^ 2 := by
    funext ω; ring
  rw [e]
  exact ((h.integrable_pow_mul_pow a b 4 2).sub
    ((h.integrable_pow_mul_pow a b 2 2).const_mul _)).add
    ((h.integrable_pow_apply b 2).const_mul _)

/-- The product of two blocks `(X_a² - s) X_b` is integrable. -/
theorem integrable_wick_two_pair (h : IsCentredGaussianVector P X C) (s t : ℝ)
    (a b c d : Fin n) :
    Integrable (fun ω => ((X ω a ^ 2 - s) * X ω b) * ((X ω c ^ 2 - t) * X ω d)) P := by
  have hmaj := ((h.integrable_wick_two_mul_X_sq s a b).add
    (h.integrable_wick_two_mul_X_sq t c d)).div_const 2
  refine hmaj.mono' ?_ (Filter.Eventually.of_forall fun ω => ?_)
  · have ha := h.aemeasurable_apply a
    have hb := h.aemeasurable_apply b
    have hc := h.aemeasurable_apply c
    have hd := h.aemeasurable_apply d
    exact ((((ha.pow_const 2).sub_const _).mul hb).mul (((hc.pow_const 2).sub_const _).mul
      hd)).aestronglyMeasurable
  · simp only [Pi.add_apply, Real.norm_eq_abs]
    rw [abs_le]
    constructor <;> nlinarith [sq_nonneg ((X ω a ^ 2 - s) * X ω b - (X ω c ^ 2 - t) * X ω d),
      sq_nonneg ((X ω a ^ 2 - s) * X ω b + (X ω c ^ 2 - t) * X ω d)]

/-- The second moment of `:X_a²: X_b` is at most `10 D³`. -/
theorem integral_wick_two_mul_X_sq_le (h : IsCentredGaussianVector P X C) {D : ℝ}
    (hD : ∀ i, C i i ≤ D) (a b : Fin n) :
    ∫ ω, wickMonomial C (List.replicate 2 a) (X ω) * X ω b *
        (wickMonomial C (List.replicate 2 a) (X ω) * X ω b) ∂P ≤ 10 * D ^ 3 := by
  have hf := integral_wick_two_mul_X_mul_wick_two_mul_X h a b a b
  have e : (fun ω => wickMonomial C (List.replicate 2 a) (X ω) * X ω b *
        (wickMonomial C (List.replicate 2 a) (X ω) * X ω b)) =
      fun ω => wickMonomial C (List.replicate 2 a) (X ω) * X ω b *
        wickMonomial C (List.replicate 2 a) (X ω) * X ω b := by
    funext ω; ring
  rw [e, hf]
  have hab := h.abs_apply_le_of_diag_le hD a b
  have hba := h.abs_apply_le_of_diag_le hD b a
  have haa := h.abs_apply_le_of_diag_le hD a a
  have hbb := h.abs_apply_le_of_diag_le hD b b
  have hD0 : 0 ≤ D := (abs_nonneg _).trans haa
  have m3 : ∀ u v w : ℝ, |u| ≤ D → |v| ≤ D → |w| ≤ D → u * v * w ≤ D ^ 3 := by
    intro u v w hu hv hw
    have : |u * v * w| ≤ D * D * D := by
      rw [abs_mul, abs_mul]; gcongr
    calc u * v * w ≤ |u * v * w| := le_abs_self _
      _ ≤ D * D * D := this
      _ = D ^ 3 := by ring
  have t1 := m3 (C a a) (C a a) (C b b) haa haa hbb
  have t2 := m3 (C a a) (C a b) (C b a) haa hab hba
  have t3 := m3 (C a b) (C a a) (C a b) hab haa hab
  have e1 : 2 * C a a ^ 2 * C b b = 2 * (C a a * C a a * C b b) := by ring
  nlinarith [t1, t2, t3]

/-- **Moment bound for `:X_a²: X_b :X_c²: X_d`.** -/
theorem integrable_and_abs_integral_wick_two_le (h : IsCentredGaussianVector P X C) {D : ℝ}
    (hD : ∀ i, C i i ≤ D) (a b c d : Fin n) :
    Integrable (fun ω => wickMonomial C (List.replicate 2 a) (X ω) * X ω b *
        wickMonomial C (List.replicate 2 c) (X ω) * X ω d) P ∧
      ∫ ω, |wickMonomial C (List.replicate 2 a) (X ω) * X ω b *
        wickMonomial C (List.replicate 2 c) (X ω) * X ω d| ∂P ≤ 10 * D ^ 3 := by
  have := h.isProbabilityMeasure
  have hw : ∀ (a : Fin n) (ω : Ω), wickMonomial C (List.replicate 2 a) (X ω) =
      X ω a ^ 2 - C a a := fun a ω => wickMonomial_pair_self C a (X ω)
  have hi : ∀ a b c d : Fin n, Integrable (fun ω =>
      wickMonomial C (List.replicate 2 a) (X ω) * X ω b *
        (wickMonomial C (List.replicate 2 c) (X ω) * X ω d)) P := by
    intro a b c d
    simp only [hw]
    exact h.integrable_wick_two_pair _ _ a b c d
  have hpq := hi a b c d
  have hpp := hi a b a b
  have hqq := hi c d c d
  have e : ∀ ω, wickMonomial C (List.replicate 2 a) (X ω) * X ω b *
        wickMonomial C (List.replicate 2 c) (X ω) * X ω d =
      wickMonomial C (List.replicate 2 a) (X ω) * X ω b *
        (wickMonomial C (List.replicate 2 c) (X ω) * X ω d) := fun ω => by ring
  simp only [e]
  refine ⟨hpq, ?_⟩
  have hmaj := (hpp.add hqq).div_const 2
  calc ∫ ω, |wickMonomial C (List.replicate 2 a) (X ω) * X ω b *
          (wickMonomial C (List.replicate 2 c) (X ω) * X ω d)| ∂P
      ≤ ∫ ω, (wickMonomial C (List.replicate 2 a) (X ω) * X ω b *
            (wickMonomial C (List.replicate 2 a) (X ω) * X ω b) +
          wickMonomial C (List.replicate 2 c) (X ω) * X ω d *
            (wickMonomial C (List.replicate 2 c) (X ω) * X ω d)) / 2 ∂P := by
        refine integral_mono hpq.abs hmaj fun ω => ?_
        simp only
        rw [abs_le]
        constructor <;> nlinarith [sq_nonneg (wickMonomial C (List.replicate 2 a) (X ω) * X ω b -
          wickMonomial C (List.replicate 2 c) (X ω) * X ω d),
          sq_nonneg (wickMonomial C (List.replicate 2 a) (X ω) * X ω b +
          wickMonomial C (List.replicate 2 c) (X ω) * X ω d)]
    _ = (∫ ω, wickMonomial C (List.replicate 2 a) (X ω) * X ω b *
            (wickMonomial C (List.replicate 2 a) (X ω) * X ω b) ∂P +
          ∫ ω, wickMonomial C (List.replicate 2 c) (X ω) * X ω d *
            (wickMonomial C (List.replicate 2 c) (X ω) * X ω d) ∂P) / 2 := by
        rw [integral_div, integral_add hpp hqq]
    _ ≤ (10 * D ^ 3 + 10 * D ^ 3) / 2 := by
        gcongr
        · exact h.integral_wick_two_mul_X_sq_le hD a b
        · exact h.integral_wick_two_mul_X_sq_le hD c d
    _ = 10 * D ^ 3 := by ring

end IsCentredGaussianVector

end RegularityStructures

end
